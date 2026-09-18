"""Check corpus bindings against the pinned Lean environment, including mathlib."""

from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import tempfile

from django.conf import settings
from django.core.management.base import BaseCommand, CommandError

from catalog.content import load_catalog, read_json
from catalog.metadata import formal_source_path
from catalog.sources import ContentError


class Command(BaseCommand):
    help = 'Verify complete proofs, type-check pending dependencies, and write reports.'

    def handle(self, **options):
        root = settings.REPOSITORY_DIR
        formal_dir = root / 'formal'
        try:
            catalog = load_catalog(settings.CORPUS_DIR,
                                   root, check_reports=False)
        except (ContentError, KeyError, ValueError, OSError) as error:
            raise CommandError(str(error)) from error
        bindings = [(entry, block) for entry in catalog.values() for block in entry['blocks']
                    if block['formalization']['status'] == 'complete']
        pending = {dependency['declaration']: dependency
                   for entry in catalog.values() for block in entry['blocks']
                   for dependency in block['formalization']['unformalized_dependencies']}
        if not bindings and not pending:
            self.stdout.write(
                'No complete formalizations or pending dependencies to check.')
            return
        lake = shutil.which('lake') or str(Path.home() / '.elan/bin/lake')
        modules = sorted({block['formalization']['module'] for _, block in bindings}
                         | {dependency['module'] for dependency in pending.values()})
        names = sorted({block['formalization']['declaration']
                       for _, block in bindings})
        source = '\n'.join(f'import {module}' for module in modules) + '\n\n'
        source += '\n'.join(f'#check {name}\n#print axioms {name}'
                            for name in sorted(set(names) | pending.keys())) + '\n'

        def run(args):
            try:
                result = subprocess.run([lake, *args], cwd=formal_dir, text=True,
                                        capture_output=True, timeout=300)
            except (OSError, subprocess.TimeoutExpired) as error:
                raise CommandError(str(error)) from error
            if result.returncode:
                raise CommandError(result.stdout + result.stderr)
            return result.stdout + result.stderr

        self.stdout.write('Building the pinned Lean project…')
        # Pending modules are deliberately not imported by the main library.
        run(['build', 'Lemmatheca', *modules])
        with tempfile.NamedTemporaryFile('w', suffix='.lean', prefix='CorpusCheck', dir=formal_dir) as check:
            check.write(source)
            check.flush()
            output = run(['env', 'lean', check.name])

        def checked_declaration(name, *, allow_sorry=False):
            pattern = re.escape(
                "'" + name + "'") + r" (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)"
            match = re.search(pattern, output)
            if not match:
                raise CommandError(f'No axiom result for {name}:\n{output}')
            axioms = [value.strip() for value in (
                match[1] or '').split(',') if value.strip()]
            allowed = {'propext', 'Classical.choice', 'Quot.sound'}
            if allow_sorry:
                allowed.add('sorryAx')
            if set(axioms) - allowed:
                raise CommandError(f'{name} uses unapproved axioms: {axioms}')
            return {'name': name, 'axioms': axioms}

        declarations = [checked_declaration(name) for name in names]
        pending_declarations = [
            {**checked_declaration(name, allow_sorry=True),
             'module': dependency['module'], 'source': dependency['source']}
            for name, dependency in sorted(pending.items())
        ]
        paths = set(settings.CORPUS_DIR.rglob('entry.json')) | set(
            settings.CORPUS_DIR.rglob('entry.html'))
        paths.update(path for entry in catalog.values() for path in (entry['directory'] / 'assets').rglob('*')
                     if path.is_file())
        paths.update((formal_dir / 'Lemmatheca').rglob('*.lean'))
        paths.add(formal_dir / 'Lemmatheca.lean')
        paths.update(formal_source_path(
            block['formalization'], root) for _, block in bindings)
        paths.update(formal_source_path(dependency, root)
                     for dependency in pending.values())
        paths.update(formal_dir / name for name in ('lean-toolchain',
                     'lake-manifest.json', 'lakefile.toml'))
        manifest = read_json(formal_dir / 'lake-manifest.json')
        mathlib = next(
            package for package in manifest['packages'] if package['name'] == 'mathlib')
        report = {
            'scope': 'local_development_check', 'checked_on': datetime.now(timezone.utc).isoformat(),
            'command': 'python app/manage.py check_formalizations', 'build': 'passed',
            'lean_toolchain': (formal_dir / 'lean-toolchain').read_text().strip(),
            'mathlib_commit': mathlib['rev'], 'declarations': declarations,
            'pending_dependencies': pending_declarations,
            'bindings': [{'entry_id': entry['id'], 'block_id': block['id'],
                          'declaration': block['formalization']['declaration']} for entry, block in bindings],
            'mathematical_dependency_audit': 'not_performed', 'maintainer_review': 'pending',
            'notes': ['Checks declarations and axioms, not correspondence with the human argument.',
                      'Pending dependency statements are type-checked separately; sorryAx is allowed only there.',
                      'Incomplete blocks and pending dependencies are not certified as complete proofs.',
                      'The full mathematical dependency closure is not extracted.'],
            'sha256': {str(path.relative_to(root)): hashlib.sha256(path.read_bytes()).hexdigest()
                       for path in sorted(paths)},
        }
        for filename in {block['formalization']['verification_report'] for _, block in bindings}:
            destination = root / filename
            destination.parent.mkdir(parents=True, exist_ok=True)
            destination.write_text(json.dumps(report, indent=2) + '\n')
        self.stdout.write(self.style.SUCCESS(
            f'Checked {len(bindings)} complete block bindings and {len(names)} declarations; '
            f'type-checked {len(pending)} pending dependencies (proofs may contain sorry).'))
