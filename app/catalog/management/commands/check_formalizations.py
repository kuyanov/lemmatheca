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

from catalog.files import file_signature, read_json, staged_json
from formalization.lean import REVIEW_MODULE, verification_inputs
from formalization.nodes import (
    ALLOWED_AXIOMS, REPORT, REPORT_VERSION, current_node_evidence,
    load_nodes, module_is_current, node_fingerprint, verification_policy_hash,
    verification_group, verification_input_hash,
)
from formalization.reviews import declaration_hashes


def input_hashes(root, modules):
    paths = {path for module in modules for path in verification_inputs(root, module)}
    return {path.relative_to(root).as_posix(): verification_input_hash(path, root)
            for path in sorted(paths)}


def check_source(module, names):
    return '\n'.join([
        f'import {module}',
        f'import {REVIEW_MODULE}',
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
    help = 'Refresh stale project modules and the shared Mathlib audit; check each declaration and its axioms.'

    def add_arguments(self, parser):
        parser.add_argument('--module', nargs='+', metavar='MODULE',
                            help='Select project modules or Mathlib (any registered Mathlib module selects the shared audit).')
        parser.add_argument('--force', action='store_true',
                            help='Recheck selected modules even when their evidence is current.')

    def handle(self, **options):
        try:
            self.verify_nodes(settings.REPOSITORY_DIR, options['module'], force=options['force'])
        except (ValueError, OSError) as error:
            raise CommandError(str(error)) from error

    def verify_nodes(self, root, selected=None, *, force=False):
        nodes = load_nodes(root, check_reports=False)
        bound = {key: node for key,
                 node in nodes.items() if node['declaration']}
        groups = {}
        for key, node in bound.items():
            groups.setdefault(verification_group(node['module']), {})[key] = node
        selectors = set(selected) if selected is not None else set(groups)
        unknown = selectors - (groups.keys() | {node['module'] for node in bound.values()})
        if unknown:
            raise CommandError('Unknown registered modules: ' + ', '.join(sorted(unknown)))
        selected = sorted({verification_group(module) for module in selectors})
        if not bound:
            self.stdout.write('No formal node declarations to check.')
            return
        destination = root / REPORT
        report_signature = file_signature(destination)
        previous = read_json(destination) if destination.exists() else {}
        supported = previous.get('format_version') == REPORT_VERSION
        report = {
            'format_version': REPORT_VERSION,
            'command': 'python app/manage.py check_formalizations',
            'modules': {module: record for module, record in previous.get('modules', {}).items()
                        if supported and module in groups},
            'nodes': {key: record for key, record in previous.get('nodes', {}).items()
                      if supported and key in bound},
        }
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

        checked, reused, failures = [], [], {}
        input_cache = {}
        for module in selected:
            group = groups[module]
            record = report['modules'].get(module)
            if (not force and module_is_current(record, root, module, input_cache=input_cache)
                    and all(current_node_evidence(node, report['nodes'].get(key), record['sha256'])
                            for key, node in group.items())):
                reused.append(module)
                continue
            self.stdout.write(f'Checking {module} ({len(group)} node(s))…')
            before = {}
            try:
                imports = sorted({node['module'] for node in group.values()})
                before = input_hashes(root, imports)
                fingerprints = {key: node_fingerprint(node) for key, node in group.items()}
                run(['build', *imports, REVIEW_MODULE])
                evidence = {}
                # Audit each declared import separately: importing every Mathlib
                # module together could conceal a binding to the wrong module.
                for imported in imports:
                    imported_nodes = {key: node for key, node in group.items() if node['module'] == imported}
                    names = sorted({node['declaration'] for node in imported_nodes.values()})
                    with tempfile.NamedTemporaryFile('w', suffix='.lean', prefix='NodeCheck', dir=formal_dir) as check:
                        check.write(check_source(imported, names))
                        check.flush()
                        output = run(['env', 'lean', check.name])
                    declarations, target_hashes = parse_checks(output, names)
                    evidence.update({key: {
                        'fingerprint': fingerprints[key], **declarations[node['declaration']],
                        'declaration_sha256': target_hashes[node['declaration']],
                    } for key, node in imported_nodes.items()})
                after = load_nodes(root, check_reports=False)
                if (before != input_hashes(root, imports)
                        or fingerprints != {key: node_fingerprint(node) for key, node in after.items()
                                            if verification_group(node['module']) == module}):
                    raise CommandError('Formal inputs changed during verification; rerun the check.')
                report['modules'][module] = {
                    'status': 'passed', 'checked_on': datetime.now(timezone.utc).isoformat(),
                    'policy_sha256': verification_policy_hash(), 'sha256': before,
                }
                report['nodes'].update(evidence)
                checked.append(module)
            except (CommandError, ValueError, OSError) as error:
                failures[module] = str(error)
                report['modules'][module] = {
                    'status': 'failed', 'checked_on': datetime.now(timezone.utc).isoformat(),
                    'policy_sha256': verification_policy_hash(), 'sha256': before, 'error': str(error),
                }
                for key in group:
                    report['nodes'].pop(key, None)

        if file_signature(destination) != report_signature:
            raise CommandError('Verification report changed during checking; rerun the check.')
        if report != previous:
            destination.parent.mkdir(parents=True, exist_ok=True)
            with staged_json(destination, report) as temporary:
                temporary.replace(destination)
        ready = sum(node['status'] ==
                    'complete' for node in load_nodes(root).values())
        style = self.style.ERROR if failures else self.style.SUCCESS
        self.stdout.write(style(
            f'Checked {len(checked)} verification group(s); reused {len(reused)}; failed {len(failures)}. '
            f'{ready} nodes ready, {len(nodes) - ready} pending.'))
        if failures:
            raise CommandError('\n\n'.join(f'{module}: {error}' for module, error in failures.items()))
