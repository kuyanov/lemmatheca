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

from catalog.files import staged_json
from formalization.lean import verification_inputs
from formalization.nodes import (
    ALLOWED_AXIOMS, ENVIRONMENT, REPORT, REPORT_VERSION, file_hash, load_nodes, node_fingerprint,
)
from formalization.reviews import declaration_hashes, review_target_hash


def input_hashes(root, nodes):
    return {path.relative_to(root).as_posix(): file_hash(path)
            for path in sorted(verification_inputs(root, nodes))}


def check_source(modules, names):
    return '\n'.join([
        *(f'import {module}' for module in modules),
        'import Lemmatheca.ReviewChecks',
        'set_option maxRecDepth 10000',
        'set_option maxHeartbeats 0',
        *(f'#print axioms {name}' for name in names),
        '#review_targets ' + ', '.join(names),
        '',
    ])


def parse_checks(output, names):
    locations = {name: {'module': module, 'line': int(line)}
                 for name, module, line in re.findall(
                     r'^NODE_LOCATION (\S+) (\S+) ([1-9][0-9]*)$', output, re.M)}
    try:
        signatures = {}
        for line in output.splitlines():
            if line.startswith('NODE_SIGNATURE '):
                item = json.loads(line.removeprefix('NODE_SIGNATURE '))
                if not isinstance(item['signature'], str) or not item['signature'].strip():
                    raise ValueError('Empty or invalid declaration signature')
                signatures[item['name']] = item['signature']
        snapshots = [json.loads(line.removeprefix('REVIEW_CONSTANT '))
                     for line in output.splitlines() if line.startswith('REVIEW_CONSTANT ')]
        target_hashes = declaration_hashes(
            {item['name']: item for item in snapshots}, names)
    except (ValueError, KeyError, TypeError) as error:
        raise CommandError(f'Invalid review snapshots: {error}') from error

    declarations = {}
    for name in names:
        if name not in signatures:
            raise CommandError(f'No declaration signature for {name}')
        pattern = re.escape(
            f"'{name}'") + r" (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)"
        match = re.search(pattern, output)
        if not match:
            raise CommandError(f'No axiom result for {name}:\n{output}')
        axioms = [value.strip()
                  for value in (match[1] or '').split(',') if value.strip()]
        if set(axioms) - ALLOWED_AXIOMS - {'sorryAx'}:
            raise CommandError(f'{name} uses unapproved axioms: {axioms}')
        declarations[name] = {'axioms': axioms, 'status': 'pending' if 'sorryAx' in axioms else 'complete',
                              'signature': signatures[name]}
        if name in locations:
            declarations[name]['location'] = locations[name]
    return declarations, target_hashes


class Command(BaseCommand):
    help = 'Check node declarations and transitive axioms; record complete and pending proofs.'

    def handle(self, **options):
        try:
            self.verify_nodes(settings.REPOSITORY_DIR)
        except (ValueError, OSError) as error:
            raise CommandError(str(error)) from error

    def verify_nodes(self, root):
        nodes = load_nodes(root, check_reports=False)
        bound = {key: node for key,
                 node in nodes.items() if node['declaration']}
        if not bound:
            self.stdout.write('No formal node declarations to check.')
            return
        before = input_hashes(root, bound)
        fingerprints = {key: node_fingerprint(
            node) for key, node in nodes.items()}
        modules = sorted({node['module'] for node in bound.values()})
        names = sorted({node['declaration'] for node in bound.values()})
        formal_dir = root / 'formal'
        lake = shutil.which('lake') or str(Path.home() / '.elan/bin/lake')

        def run(args):
            try:
                result = subprocess.run([lake, *args], cwd=formal_dir, text=True,
                                        capture_output=True, timeout=300)
            except subprocess.TimeoutExpired as error:
                raise CommandError(str(error)) from error
            if result.returncode:
                raise CommandError(result.stdout + result.stderr)
            return result.stdout + result.stderr

        self.stdout.write('Building the pinned Lean modules…')
        run(['build', *modules, 'Lemmatheca.ReviewChecks'])
        with tempfile.NamedTemporaryFile('w', suffix='.lean', prefix='NodeCheck', dir=formal_dir) as check:
            check.write(check_source(modules, names))
            check.flush()
            output = run(['env', 'lean', check.name])
        declarations, target_hashes = parse_checks(output, names)

        after_nodes = load_nodes(root, check_reports=False)
        if (before != input_hashes(root, bound)
                or fingerprints != {key: node_fingerprint(node) for key, node in after_nodes.items()}):
            raise CommandError(
                'Formal inputs changed during verification; rerun the check.')

        environment = {name: before[f'formal/{name}'] for name in ENVIRONMENT}
        report = {
            'format_version': REPORT_VERSION,
            'build': 'passed',
            'checked_on': datetime.now(timezone.utc).isoformat(),
            'command': 'python app/manage.py check_formalizations',
            'nodes': {
                key: {
                    'fingerprint': fingerprints[key],
                    **declarations[node['declaration']],
                    'target_sha256': review_target_hash(
                        fingerprints[key], target_hashes[node['declaration']], environment),
                }
                for key, node in bound.items()
            },
            'sha256': before,
            'notes': ['Statement review and correspondence with the human text remain human decisions.',
                      'sorryAx, including transitive use, always means pending.',
                      'Declared node dependencies are checked separately from Lean axiom dependencies.'],
        }
        destination = root / REPORT
        destination.parent.mkdir(parents=True, exist_ok=True)
        with staged_json(destination, report) as temporary:
            temporary.replace(destination)
        ready = sum(node['status'] ==
                    'complete' for node in load_nodes(root).values())
        self.stdout.write(self.style.SUCCESS(
            f'Checked {len(bound)} node declarations: {ready} ready, {len(nodes) - ready} pending.'))
