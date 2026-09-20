"""Verify formal nodes independently of human entries."""

from datetime import datetime, timezone
import json
from pathlib import Path
import re
import shutil
import subprocess
import tempfile

from django.conf import settings
from django.core.management.base import BaseCommand, CommandError

from formalization.lean import verification_inputs
from formalization.nodes import ALLOWED_AXIOMS, REPORT, REPORT_VERSION, file_hash, load_nodes, node_fingerprint


class Command(BaseCommand):
    help = 'Check node declarations and transitive axioms; record complete and pending proofs.'

    def handle(self, **options):
        root = settings.REPOSITORY_DIR
        formal_dir = root / 'formal'
        try:
            nodes = load_nodes(root, check_reports=False)
            bound = {key: node for key,
                     node in nodes.items() if node['declaration']}
            if not bound:
                self.stdout.write('No formal node declarations to check.')
                return
            inputs = verification_inputs(root, bound)
            before = {path.relative_to(root).as_posix(): file_hash(
                path) for path in sorted(inputs)}
            fingerprints = {key: node_fingerprint(
                node) for key, node in nodes.items()}
        except (ValueError, OSError) as error:
            raise CommandError(str(error)) from error
        lake = shutil.which('lake') or str(Path.home() / '.elan/bin/lake')
        modules = sorted({node['module'] for node in bound.values()})
        names = sorted({node['declaration'] for node in bound.values()})
        source = '\n'.join(f'import {module}' for module in modules) + '\n\n'
        source += '\n'.join(
            f'#check {name}\n#print axioms {name}' for name in names) + '\n'

        def run(args):
            try:
                result = subprocess.run([lake, *args], cwd=formal_dir, text=True,
                                        capture_output=True, timeout=300)
            except (OSError, subprocess.TimeoutExpired) as error:
                raise CommandError(str(error)) from error
            if result.returncode:
                raise CommandError(result.stdout + result.stderr)
            return result.stdout + result.stderr

        self.stdout.write('Building the pinned Lean modules…')
        run(['build', *modules])
        with tempfile.NamedTemporaryFile('w', suffix='.lean', prefix='NodeCheck', dir=formal_dir) as check:
            check.write(source)
            check.flush()
            output = run(['env', 'lean', check.name])
        declarations = {}
        for name in names:
            pattern = re.escape(
                "'" + name + "'") + r" (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)"
            match = re.search(pattern, output)
            if not match:
                raise CommandError(f'No axiom result for {name}:\n{output}')
            axioms = [value.strip() for value in (
                match[1] or '').split(',') if value.strip()]
            if set(axioms) - ALLOWED_AXIOMS - {'sorryAx'}:
                raise CommandError(f'{name} uses unapproved axioms: {axioms}')
            declarations[name] = {
                'axioms': axioms, 'status': 'pending' if 'sorryAx' in axioms else 'complete'}
        try:
            after_nodes = load_nodes(root, check_reports=False)
            after_inputs = verification_inputs(root, bound)
            after = {path.relative_to(root).as_posix(): file_hash(
                path) for path in sorted(after_inputs)}
            if before != after or fingerprints != {key: node_fingerprint(node) for key, node in after_nodes.items()}:
                raise CommandError(
                    'Formal inputs changed during verification; rerun the check.')
        except (ValueError, OSError) as error:
            raise CommandError(str(error)) from error
        report = {
            'format_version': REPORT_VERSION, 'build': 'passed', 'checked_on': datetime.now(timezone.utc).isoformat(),
            'command': 'python app/manage.py check_formalizations',
            'nodes': {key: {'fingerprint': fingerprints[key], **declarations[node['declaration']]}
                      for key, node in bound.items()},
            'sha256': before,
            'notes': ['Statement review and correspondence with the human text remain human decisions.',
                      'sorryAx, including transitive use, always means pending.',
                      'Declared node dependencies are checked separately from Lean axiom dependencies.'],
        }
        destination = root / REPORT
        destination.parent.mkdir(parents=True, exist_ok=True)
        with tempfile.NamedTemporaryFile('w', dir=destination.parent, delete=False) as temporary:
            json.dump(report, temporary, indent=2)
            temporary.write('\n')
        Path(temporary.name).replace(destination)
        ready = sum(node['status'] ==
                    'complete' for node in load_nodes(root).values())
        self.stdout.write(self.style.SUCCESS(
            f'Checked {len(bound)} node declarations: {ready} ready, {len(nodes) - ready} pending.'))
