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
from formalization.nodes import load_nodes, read_registry
from formalization.verification import (
    ALLOWED_AXIOMS, REPORT, REPORT_VERSION, current_node_evidence,
    module_is_current, node_fingerprint, verification_policy_hash,
    normalize_verification_report, verification_input_hash, successful_module_snapshot,
    comparable_report, report_freshness_errors,
)
from formalization.reviews import declaration_hashes


def input_hashes(root, module):
    paths = verification_inputs(root, module)
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
    help = 'Refresh stale import modules; check each declaration and its axioms.'

    def add_arguments(self, parser):
        parser.add_argument('--module', nargs='+', metavar='MODULE',
                            help='Select registered import modules; Mathlib selects all registered Mathlib modules independently.')
        parser.add_argument('--force', action='store_true',
                            help='Recheck selected modules even when their evidence is current.')
        parser.add_argument('--check', action='store_true',
                            help='Require the whole saved report to be current, without writing it. '
                                 'With --force, also compare fresh Lean evidence, ignoring check dates.')

    def handle(self, **options):
        try:
            self.verify_nodes(settings.REPOSITORY_DIR,
                              options['module'], force=options['force'], check_only=options['check'])
        except (ValueError, OSError) as error:
            raise CommandError(str(error)) from error

    def verify_nodes(self, root, selected=None, *, force=False, check_only=False):
        nodes = read_registry(root)
        bound = {key: node for key,
                 node in nodes.items() if node['declaration']}
        groups = {}
        for key, node in bound.items():
            groups.setdefault(node['module'], {})[key] = node
        selectors = set(selected) if selected is not None else set(groups)
        mathlib = {
            module for module in groups if module.startswith('Mathlib.')}
        if 'Mathlib' in selectors and mathlib:
            selectors = (selectors - {'Mathlib'}) | mathlib
        unknown = selectors - groups.keys()
        if unknown:
            raise CommandError(
                'Unknown registered modules: ' + ', '.join(sorted(unknown)))
        selected = sorted(selectors)
        destination = root / REPORT
        report_signature = file_signature(destination)
        previous = read_json(destination) if destination.exists() else {}

        def stale_report(details):
            raise CommandError(
                f'{REPORT} is out of date:\n' + '\n'.join(details)
                + '\nRun python app/manage.py check_formalizations --force and commit the updated report.')

        if check_only:
            errors = report_freshness_errors(previous, nodes, root)
            if errors:
                stale_report(errors)
        if not bound and not previous:
            self.stdout.write('No formal node declarations to check.')
            return
        normalized = normalize_verification_report(previous, nodes)
        report = {
            'format_version': REPORT_VERSION,
            'command': 'python app/manage.py check_formalizations',
            'modules': {module: record for module, record in sorted(normalized.get('modules', {}).items())
                        if module in groups},
            'nodes': {key: record for key, record in normalized.get('nodes', {}).items()
                      if key in bound},
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
            if (not force and module_is_current(record, root, module, input_cache=input_cache,
                                                require_libraries=True)
                    and all(current_node_evidence(node, report['nodes'].get(key), record['sha256'])
                            for key, node in group.items())):
                reused.append(module)
                continue
            if check_only and not force:
                stale_report(
                    [f'Inputs changed during report validation: {module}'])
            self.stdout.write(f'Checking {module} ({len(group)} node(s))…')
            before = {}
            try:
                before = input_hashes(root, module)
                fingerprints = {key: node_fingerprint(
                    node) for key, node in group.items()}
                run(['build', module, REVIEW_MODULE])
                names = sorted({node['declaration']
                               for node in group.values()})
                with tempfile.NamedTemporaryFile('w', suffix='.lean', prefix='NodeCheck', dir=formal_dir) as check:
                    check.write(check_source(module, names))
                    check.flush()
                    output = run(['env', 'lean', check.name])
                declarations, target_hashes = parse_checks(output, names)
                evidence = {key: {
                    'fingerprint': fingerprints[key], **declarations[node['declaration']],
                    'declaration_sha256': target_hashes[node['declaration']],
                } for key, node in group.items()}
                after = read_registry(root)
                if (before != input_hashes(root, module)
                        or fingerprints != {key: node_fingerprint(node) for key, node in after.items()
                                            if node['module'] == module}):
                    raise CommandError(
                        'Formal inputs changed during verification; rerun the check.')
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
                # Keep node snapshots paired with the inputs that actually passed,
                # not this attempt's inputs. Only one successful snapshot is kept;
                # repeated failures replace the latest error without nesting history.
                successful = successful_module_snapshot(record)
                if successful:
                    report['modules'][module]['last_success'] = successful

        if file_signature(destination) != report_signature:
            raise CommandError(
                'Verification report changed during checking; rerun the check.')
        if check_only and failures:
            raise CommandError('\n\n'.join(
                f'{module}: {error}' for module, error in failures.items()))
        if check_only and comparable_report(report) != comparable_report(previous):
            stale_report(
                ['Saved evidence differs from the current check (excluding check dates).'])
        if not check_only and report != previous:
            destination.parent.mkdir(parents=True, exist_ok=True)
            with staged_json(destination, report) as temporary:
                temporary.replace(destination)
        ready = sum(node['status'] ==
                    'complete' for node in load_nodes(root).values())
        style = self.style.ERROR if failures else self.style.SUCCESS
        self.stdout.write(style(
            f'Checked {len(checked)} verification group(s); reused {len(reused)}; failed {len(failures)}. '
            f'{ready} nodes ready, {len(nodes) - ready} pending.'))
        if check_only:
            self.stdout.write(self.style.SUCCESS(
                'Committed verification report is current; report left unchanged.'))
        if failures:
            raise CommandError('\n\n'.join(
                f'{module}: {error}' for module, error in failures.items()))
