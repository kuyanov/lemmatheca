"""Module-scoped verification, cache reuse, and isolation of failed checks."""

from copy import deepcopy
from io import StringIO
import json
import os
from pathlib import Path
import re
import shutil
from subprocess import CompletedProcess
from unittest.mock import patch

from django.core.management import call_command
from django.core.management.base import CommandError
from django.test import SimpleTestCase

from catalog.content import entries
from catalog.test_formalizations import NodeFixtureMixin
from formalization.lean import ENVIRONMENT, LIBRARY_INPUT, library_revisions
from formalization.nodes import load_nodes
from formalization.verification import (ALLOWED_AXIOMS, REPORT, REPORT_VERSION,
                                        file_hash, library_hash, module_is_current)


class ModuleVerificationTests(NodeFixtureMixin, SimpleTestCase):
    fixture_module = 'Lemmatheca.Fixture'
    independent_module = 'Lemmatheca.Independent'
    importer_module = 'Lemmatheca.UsesFixture'
    transitive_module = 'Lemmatheca.Transitive'

    def setUp(self):
        super().setUp()
        self.independent = self.add_module(
            'independent', self.independent_module)
        self.add_module('uses-fixture', self.importer_module,
                        self.fixture_module)
        self.add_module('transitive', self.transitive_module,
                        self.importer_module)
        self.check(force=True)

    def add_module(self, node_id, module, imported=None):
        path = self.formal / (module.replace('.', '/') + '.lean')
        path.write_text((f'import {imported}\n' if imported else '') +
                        f'theorem {module}.result : True := by trivial\n')
        self.write_node(node_id, declaration=f'{module}.result', module=module)
        return path

    def report(self):
        return json.loads((self.root / REPORT).read_text())

    def check(self, *, modules=None, force=False, failing=(), failing_probes=(), during_check=None):
        self.built = []
        self.probes = []

        def run(args, **kwargs):
            if args[1] == 'build':
                modules = args[2:-1]
                self.built.extend(modules)
                for module in modules:
                    if module in failing:
                        return CompletedProcess(args, 1, stdout=f'Cannot build {module}', stderr='')
                return CompletedProcess(args, 0, stdout='', stderr='')
            source = Path(args[-1]).read_text()
            imports = re.findall(r'^import (\S+)', source, re.M)
            module = imports[0]
            self.probes.append(imports)
            if module in failing_probes:
                return CompletedProcess(args, 1, stdout=f'Cannot audit {module}', stderr='')
            if during_check:
                during_check(module)
            output = []
            for name in re.findall(r'^#print axioms (\S+)', source, re.M):
                axioms = 'sorryAx' if name in (
                    'Lemmatheca.unfinished', 'Lemmatheca.dependent') else ''
                output.extend((f"'{name}' depends on axioms: [{axioms}]",
                               'NODE_SIGNATURE ' +
                               json.dumps(
                                   {'name': name, 'signature': f'{name} : True'}),
                               'REVIEW_CONSTANT ' + json.dumps({'name': name, 'payload': [name], 'references': []})))
            return CompletedProcess(args, 0, stdout='\n'.join(output), stderr='')

        output = StringIO()
        with patch('catalog.management.commands.check_formalizations.subprocess.run', side_effect=run):
            call_command('check_formalizations', module=modules, force=force,
                         stdout=output, stderr=StringIO())
        return output.getvalue()

    def test_edit_invalidates_only_the_module_and_transitive_importers(self):
        before = self.report()
        independent_before = load_nodes(self.root)['independent']
        self.source.write_text(self.source.read_text() +
                               '\n-- A changed proof.\n')
        nodes = load_nodes(self.root)
        for key in ('ready', 'pending', 'dependent', 'uses-fixture', 'transitive'):
            self.assertEqual(nodes[key]['status'], 'verification_needed')
            self.assertIsNone(nodes[key]['checked_on'])
        self.assertEqual(nodes['independent']['status'], 'complete')
        self.assertEqual(nodes['independent']['checked_on'],
                         independent_before['checked_on'])
        self.check()
        self.assertEqual(set(self.built), {
                         self.fixture_module, self.importer_module, self.transitive_module})
        self.assertTrue(all(
            imports == [imports[0], 'Lemmatheca.ReviewChecks'] for imports in self.probes))
        after = self.report()
        self.assertEqual(before['modules'][self.independent_module],
                         after['modules'][self.independent_module])
        self.assertEqual(before['nodes']['independent'],
                         after['nodes']['independent'])
        self.assertEqual(load_nodes(self.root)['ready']['status'], 'complete')
        self.assertEqual(load_nodes(self.root)[
                         'dependent']['status'], 'proof_pending')

    def test_unrelated_file_creation_edit_and_removal_do_not_invalidate_evidence(self):
        before = (self.root / REPORT).read_bytes()
        unrelated = self.formal / 'Lemmatheca/Unregistered.lean'
        for content in ('not Lean code', 'still not Lean code', None):
            with self.subTest(content=content):
                if content is None:
                    unrelated.unlink()
                else:
                    unrelated.write_text(content)
                self.assertEqual(load_nodes(self.root)[
                                 'ready']['status'], 'complete')
                self.check()
                self.assertEqual(self.built, [])
                self.assertEqual((self.root / REPORT).read_bytes(), before)

    def test_failed_modules_do_not_discard_successful_or_cached_checks(self):
        before = self.report()
        self.source.write_text(
            self.source.read_text() + '\n-- Broken module.\n')
        failed = {self.fixture_module,
                  self.importer_module, self.transitive_module}
        with self.assertRaisesRegex(CommandError, 'Cannot build'):
            self.check(failing=failed)
        after = self.report()
        self.assertEqual(after['modules'][self.independent_module],
                         before['modules'][self.independent_module])
        self.assertEqual(after['nodes']['independent'],
                         before['nodes']['independent'])
        for module in failed:
            self.assertEqual(after['modules'][module]['status'], 'failed')
            self.assertEqual(after['modules'][module]
                             ['last_success'], before['modules'][module])
        self.assertEqual(after['nodes'], before['nodes'])
        self.assertEqual(load_nodes(self.root)[
                         'ready']['status'], 'verification_needed')
        self.assertTrue(load_nodes(self.root)[
                        'ready']['review_matches_last_check'])
        self.assertEqual(load_nodes(self.root)[
                         'independent']['status'], 'complete')

        self.independent.write_text(self.independent.read_text() + '\n')
        with self.assertRaises(CommandError):
            self.check(failing=failed)
        updated = self.report()
        for module in failed:
            self.assertEqual(updated['modules'][module]
                             ['last_success'], before['modules'][module])
        self.assertNotEqual(updated['modules'][self.independent_module]['checked_on'],
                            before['modules'][self.independent_module]['checked_on'])
        self.assertEqual(load_nodes(self.root)[
                         'independent']['status'], 'complete')

    def test_missing_local_module_does_not_break_unrelated_nodes_or_pages(self):
        self.source.unlink()
        nodes = load_nodes(self.root)
        self.assertEqual(nodes['ready']['status'], 'verification_needed')
        self.assertEqual(nodes['independent']['status'], 'complete')
        self.assertContains(self.client.get(
            '/formal/nodes/ready/'), 'This source file is missing')
        with self.assertRaisesRegex(CommandError, 'Missing imported Lean source'):
            self.check()
        self.assertEqual(load_nodes(self.root)[
                         'independent']['status'], 'complete')

    def test_shared_exporter_environment_and_policy_changes_invalidate_all_modules(self):
        paths = [self.formal / name for name in ENVIRONMENT]
        paths.append(self.formal / 'Lemmatheca/ReviewChecks.lean')
        for path in paths:
            with self.subTest(path=path.name):
                original = path.read_text()
                path.write_text(original + '\n')
                self.assertTrue(all(
                    node['status'] == 'verification_needed' for node in load_nodes(self.root).values()))
                path.write_text(original)
        with patch('formalization.verification.ALLOWED_AXIOMS', ALLOWED_AXIOMS - {'Quot.sound'}):
            self.assertTrue(all(
                node['status'] == 'verification_needed' for node in load_nodes(self.root).values()))

    def test_module_selection_and_force_preserve_other_module_records(self):
        before = self.report()
        self.check(modules=[self.independent_module])
        self.assertEqual(self.built, [])
        self.check(modules=[self.independent_module], force=True)
        self.assertEqual(self.built, [self.independent_module])
        for module, record in before['modules'].items():
            if module != self.independent_module:
                self.assertEqual(self.report()['modules'][module], record)
        report_before = (self.root / REPORT).read_bytes()
        with self.assertRaisesRegex(CommandError, 'Unknown registered modules'):
            self.check(modules=['Lemmatheca.Unknown'])
        self.assertEqual(self.built, [])
        self.assertEqual((self.root / REPORT).read_bytes(), report_before)

    def test_incomplete_node_evidence_refreshes_only_its_module(self):
        report = self.report()
        del report['nodes']['independent']['declaration_sha256']
        (self.root / REPORT).write_text(json.dumps(report))
        self.check()
        self.assertEqual(self.built, [self.independent_module])
        self.assertEqual(load_nodes(self.root)[
                         'independent']['status'], 'complete')

    def test_old_global_report_is_rechecked_without_changing_approvals(self):
        before = self.report()
        approvals = {path: path.read_bytes()
                     for path in self.node_dir.glob('*.json')}
        old = {
            'format_version': 4, 'build': 'passed', 'checked_on': '2026-09-20T12:00:00+00:00',
            'sha256': {path: value for record in before['modules'].values()
                       for path, value in record['sha256'].items()},
            'nodes': before['nodes'],
        }
        (self.root / REPORT).write_text(json.dumps(old))
        self.assertEqual(load_nodes(self.root)[
                         'independent']['status'], 'verification_needed')
        self.check()
        self.assertEqual(set(self.built), set(before['modules']))
        self.assertEqual(self.report()['format_version'], REPORT_VERSION)
        self.assertTrue(load_nodes(self.root)['independent']['review_current'])
        self.assertEqual(self.report()['nodes'], before['nodes'])
        for path, content in approvals.items():
            self.assertEqual(path.read_bytes(), content)

    def test_old_indexed_report_is_ignored_by_reader_cache_and_rebuilt(self):
        before = self.report()
        approvals = {path: path.read_bytes()
                     for path in self.node_dir.glob('*.json')}
        indexed = deepcopy(before)
        indexed['format_version'] = 6
        indexed['inputs'] = [
            [self.source.relative_to(self.root).as_posix(), 'a' * 64]]
        for record in indexed['modules'].values():
            record['sha256'] = [0]
        (self.root / REPORT).write_text(json.dumps(indexed))
        self.assertEqual(entries()['first']
                         ['formalization']['status'], 'partial')
        self.assertEqual(load_nodes(self.root)[
                         'ready']['status'], 'verification_needed')
        self.assertEqual(self.client.get('/entries/first/').status_code, 200)
        self.check()
        self.assertEqual(self.report()['nodes'], before['nodes'])
        self.assertEqual(load_nodes(self.root)['ready']['status'], 'complete')
        for path, content in approvals.items():
            self.assertEqual(path.read_bytes(), content)

    def test_partial_rechecks_keep_both_versions_of_a_shared_input(self):
        before = self.report()
        source_key = self.source.relative_to(self.root).as_posix()
        old_hash = before['modules'][self.fixture_module]['sha256'][source_key]
        self.source.write_text(self.source.read_text() + '\n-- New proof.\n')
        self.check(modules=[self.fixture_module])
        partial = self.report()
        self.assertNotEqual(
            partial['modules'][self.fixture_module]['sha256'][source_key], old_hash)
        self.assertEqual(
            partial['modules'][self.importer_module]['sha256'][source_key], old_hash)
        self.assertEqual(partial['modules'][self.importer_module],
                         before['modules'][self.importer_module])
        self.assertEqual(partial['modules'][self.independent_module],
                         before['modules'][self.independent_module])
        nodes = load_nodes(self.root)
        self.assertEqual(nodes['ready']['status'], 'complete')
        self.assertEqual(nodes['uses-fixture']
                         ['status'], 'verification_needed')

        self.check()
        self.assertEqual(set(self.built), {
                         self.importer_module, self.transitive_module})
        current = self.report()
        self.assertEqual(current['modules'][self.fixture_module]['sha256'][source_key],
                         current['modules'][self.importer_module]['sha256'][source_key])
        self.assertEqual(current['modules'][self.independent_module],
                         before['modules'][self.independent_module])

    def test_invalid_input_hashes_stale_only_the_affected_module(self):
        original = self.report()
        hashes = original['modules'][self.fixture_module]['sha256']
        path = self.source.relative_to(self.root).as_posix()
        for invalid in ({}, [], None, {**hashes, path: 'invalid hash'}, {**hashes, path: True},
                        {**hashes, 'formal/.lake/packages/mathlib/Mathlib/Old.lean': 'a' * 64},
                        {**hashes, 'formal/Lemmatheca/Bad\x00.lean': 'a' * 64}):
            with self.subTest(hashes=invalid):
                report = deepcopy(original)
                report['modules'][self.fixture_module]['sha256'] = invalid
                (self.root / REPORT).write_text(json.dumps(report))
                nodes = load_nodes(self.root)
                self.assertEqual(nodes['ready']['status'],
                                 'verification_needed')
                self.assertEqual(nodes['independent']['status'], 'complete')
                self.assertEqual(
                    entries()['first']['formalization']['status'], 'partial')

    def test_unreadable_input_invalidates_only_affected_modules(self):
        def read_hash(path):
            if path == self.source:
                raise PermissionError('Cannot read source')
            return file_hash(path)

        with patch('formalization.verification.file_hash', side_effect=read_hash):
            nodes = load_nodes(self.root)
        self.assertEqual(nodes['ready']['status'], 'verification_needed')
        self.assertTrue(nodes['ready']['review_matches_last_check'])
        self.assertEqual(nodes['independent']['status'], 'complete')

    def add_library(self):
        sources = []
        for package, module in (('mathlib', 'Mathlib/Support'), ('aesop', 'Aesop/Constants')):
            path = self.formal / '.lake/packages' / \
                package / (module + '.lean')
            path.parent.mkdir(parents=True)
            path.write_text('-- Library source\n')
            sources.append(path)
            self.commit_library(package)
        self.source.write_text(
            'import Mathlib.Support\n' + self.source.read_text())
        self.check()
        return sources

    def add_library_bindings(self):
        for node_id, module in (('library-first', 'Mathlib.First'), ('library-second', 'Mathlib.Second')):
            path = self.formal / '.lake/packages/mathlib' / \
                (module.replace('.', '/') + '.lean')
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(f'theorem {module}.result : True := by trivial\n')
            self.write_node(node_id, module=module,
                            declaration=f'{module}.result')
        self.commit_library('mathlib')
        self.check()

    def test_partial_rechecks_share_one_current_library_snapshot(self):
        mathlib, _ = self.add_library()
        mathlib.write_text(mathlib.read_text() + '-- Updated library\n')
        self.commit_library('mathlib')
        self.check(modules=[self.fixture_module])
        with patch('formalization.verification.library_revisions', wraps=library_revisions) as revisions:
            nodes = load_nodes(self.root)
        revisions.assert_called_once_with(self.root, required=False)
        self.assertEqual(nodes['ready']['status'], 'complete')
        self.assertEqual(nodes['uses-fixture']['status'], 'verification_needed')
        self.assertEqual(nodes['independent']['status'], 'complete')

    def test_reader_cache_cannot_bypass_required_dependency_checkouts(self):
        self.add_library_bindings()
        record = self.report()['modules']['Mathlib.First']
        shutil.rmtree(self.formal / '.lake/packages')
        cache = {}
        self.assertTrue(module_is_current(record, self.root, 'Mathlib.First', input_cache=cache))
        self.assertFalse(module_is_current(record, self.root, 'Mathlib.First',
                                           input_cache=cache, require_libraries=True))

    def test_mathlib_bindings_have_separate_records_and_import_probes(self):
        self.add_library_bindings()
        report = self.report()
        self.assertNotIn('Mathlib', report['modules'])
        self.assertNotIn('inputs', report)
        self.assertEqual(set(self.built), {'Mathlib.First', 'Mathlib.Second'})
        self.assertEqual(self.probes, [['Mathlib.First', 'Lemmatheca.ReviewChecks'],
                                       ['Mathlib.Second', 'Lemmatheca.ReviewChecks']])
        nodes = load_nodes(self.root)
        for key in ('library-first', 'library-second'):
            node = nodes[key]
            record = report['modules'][node['module']]
            self.assertEqual(node['status'], 'complete')
            self.assertEqual(node['checked_on'], record['checked_on'])
            self.assertIn(LIBRARY_INPUT, record['sha256'])
            self.assertFalse(any(path.startswith(LIBRARY_INPUT + '/')
                             for path in record['sha256']))
        self.assertEqual(report['modules']['Mathlib.First']['sha256'][LIBRARY_INPUT],
                         report['modules']['Mathlib.Second']['sha256'][LIBRARY_INPUT])

    def test_mathlib_selectors_and_new_bindings_only_refresh_selected_modules(self):
        self.add_library_bindings()
        before = self.report()
        self.check(modules=['Mathlib.First'], force=True)
        self.assertEqual(self.built, ['Mathlib.First'])
        for name, record in before['modules'].items():
            if name != 'Mathlib.First':
                self.assertEqual(self.report()['modules'][name], record)
        self.check(modules=['Mathlib', 'Mathlib.First'], force=True)
        self.assertEqual(self.built, ['Mathlib.First', 'Mathlib.Second'])
        self.check(modules=['Mathlib'])
        self.assertEqual(self.built, [])
        with self.assertRaisesRegex(CommandError, 'Unknown registered modules'):
            self.check(modules=['Mathlib.Unregistered'])
        before = self.report()['modules']['Mathlib.Second']
        self.write_node('another-library-binding',
                        module='Mathlib.First', declaration='Mathlib.First.another')
        self.check()
        self.assertEqual(self.built, ['Mathlib.First'])
        self.assertEqual(self.report()['modules']['Mathlib.Second'], before)
        self.assertEqual(load_nodes(self.root)[
                         'another-library-binding']['status'], 'complete')

    def test_local_proof_edits_preserve_mathlib_verification(self):
        self.add_library_bindings()
        before = self.report()
        self.source.write_text(self.source.read_text() +
                               '\n-- Local proof edit\n')
        nodes = load_nodes(self.root)
        self.assertEqual(nodes['ready']['status'], 'verification_needed')
        self.assertEqual(nodes['library-first']['status'], 'complete')
        self.check()
        for module in ('Mathlib.First', 'Mathlib.Second'):
            self.assertNotIn(module, self.built)
            self.assertEqual(
                self.report()['modules'][module], before['modules'][module])

    def test_failed_mathlib_module_preserves_other_modules_and_historical_review(self):
        self.add_library_bindings()
        before = self.report()
        # An early failure must not prevent a later independent module succeeding.
        with self.assertRaisesRegex(CommandError, 'Cannot audit Mathlib.First'):
            self.check(modules=['Mathlib'], force=True,
                       failing_probes=['Mathlib.First'])
        report = self.report()
        self.assertEqual(report['modules']
                         ['Mathlib.First']['status'], 'failed')
        self.assertEqual(report['modules']['Mathlib.First']
                         ['last_success'], before['modules']['Mathlib.First'])
        self.assertEqual(report['nodes'], before['nodes'])
        nodes = load_nodes(self.root)
        node = nodes['library-first']
        self.assertEqual(node['status'], 'verification_needed')
        self.assertTrue(node['review_matches_last_check'])
        self.assertFalse(node['review_current'])
        self.assertFalse(node['verification_complete'])
        self.assertIsNone(node['target_sha256'])
        self.assertIsNone(node['signature'])
        self.assertIsNone(node['checked_on'])
        page = self.client.get(node['url'])
        self.assertContains(page, 'Reviewed on <time')
        self.assertContains(page, 'Not verified')
        self.assertNotContains(page, 'Under review')
        self.assertEqual(nodes['library-second']['status'], 'complete')
        self.assertNotEqual(report['modules']['Mathlib.Second']['checked_on'],
                            before['modules']['Mathlib.Second']['checked_on'])
        self.assertEqual(report['modules'][self.fixture_module],
                         before['modules'][self.fixture_module])

        # Failed modules are retried even at unchanged inputs; successful ones reuse evidence.
        self.check(modules=['Mathlib'])
        self.assertEqual(self.built, ['Mathlib.First'])
        self.assertNotIn('last_success', self.report()
                         ['modules']['Mathlib.First'])
        self.assertEqual(
            self.report()['modules']['Mathlib.Second'], report['modules']['Mathlib.Second'])
        self.assertEqual(load_nodes(self.root)[
                         'library-first']['status'], 'complete')

    def shared_mathlib_report(self, *, failed=False):
        report = self.report()
        modules = report['modules']
        shared = deepcopy(modules['Mathlib.First'])
        shared['sha256'] = {path: value for module, record in modules.items()
                            if module.startswith('Mathlib.') for path, value in record['sha256'].items()}
        if failed:
            shared = {**shared, 'status': 'failed', 'error': 'Previous shared audit failed',
                      'last_success': deepcopy(shared)}
        report.update(format_version=7, modules={
            **{module: record for module, record in modules.items() if not module.startswith('Mathlib.')},
            'Mathlib': shared,
        })
        (self.root / REPORT).write_text(json.dumps(report))
        return report

    def test_shared_audit_migration_preserves_checks_dates_snapshots_and_approvals(self):
        self.add_library_bindings()
        old = self.shared_mathlib_report()
        approvals = {path: path.read_bytes()
                     for path in self.node_dir.glob('*.json')}
        nodes = load_nodes(self.root)
        for key in ('library-first', 'library-second'):
            self.assertEqual(nodes[key]['status'], 'complete')
        # Reader never writes.
        self.assertEqual(self.report()['format_version'], 7)
        self.check()
        migrated = self.report()
        self.assertEqual(self.built, [])
        self.assertEqual(migrated['format_version'], REPORT_VERSION)
        self.assertNotIn('Mathlib', migrated['modules'])
        for module in ('Mathlib.First', 'Mathlib.Second'):
            self.assertEqual(migrated['modules']
                             [module], old['modules']['Mathlib'])
        self.assertEqual(migrated['nodes'], old['nodes'])
        self.assertEqual({path: path.read_bytes()
                         for path in approvals}, approvals)

    def test_failed_shared_audit_migration_keeps_history_and_requires_individual_rechecks(self):
        self.add_library_bindings()
        old = self.shared_mathlib_report(failed=True)
        for key in ('library-first', 'library-second'):
            node = load_nodes(self.root)[key]
            self.assertEqual(node['status'], 'verification_needed')
            self.assertTrue(node['review_matches_last_check'])
        self.check(modules=['Mathlib.First'])
        self.assertEqual(self.built, ['Mathlib.First'])
        self.assertEqual(
            self.report()['modules']['Mathlib.Second'], old['modules']['Mathlib'])
        nodes = load_nodes(self.root)
        self.assertEqual(nodes['library-first']['status'], 'complete')
        self.assertEqual(nodes['library-second']
                         ['status'], 'verification_needed')
        self.assertTrue(nodes['library-second']['review_matches_last_check'])
        self.check(modules=['Mathlib'])
        self.assertEqual(self.built, ['Mathlib.Second'])

    def test_shared_audit_migration_cannot_certify_a_changed_binding(self):
        self.add_library_bindings()
        self.shared_mathlib_report()
        self.write_node('library-second', module='Mathlib.Second',
                        declaration='Mathlib.Second.missing')
        nodes = load_nodes(self.root)
        self.assertEqual(nodes['library-first']['status'], 'complete')
        self.assertEqual(nodes['library-second']
                         ['status'], 'verification_needed')
        with self.assertRaisesRegex(CommandError, 'Cannot audit Mathlib.Second'):
            self.check(failing_probes=['Mathlib.Second'])
        self.assertEqual(self.built, ['Mathlib.Second'])
        self.assertEqual(load_nodes(self.root)[
                         'library-first']['status'], 'complete')

    def test_bad_binding_and_description_edits_cannot_match_saved_review_snapshots(self):
        self.add_library_bindings()
        before = self.report()
        path = self.node_dir / 'library-second.json'
        original = path.read_text()
        binding = json.loads(original)
        binding['declaration'] = 'Mathlib.Second.missing'
        path.write_text(json.dumps(binding))
        with self.assertRaisesRegex(CommandError, 'Cannot audit Mathlib.Second'):
            self.check(modules=['Mathlib'], failing_probes=['Mathlib.Second'])
        self.assertEqual(self.report()['nodes'], before['nodes'])
        nodes = load_nodes(self.root)
        self.assertTrue(nodes['library-first']['review_matches_last_check'])
        self.assertEqual(nodes['library-first']['status'], 'complete')
        self.assertEqual(self.built, ['Mathlib.Second'])
        self.assertEqual(
            self.report()['modules']['Mathlib.First'], before['modules']['Mathlib.First'])
        self.assertFalse(nodes['library-second']['review_matches_last_check'])
        self.assertContains(self.client.get(
            nodes['library-second']['url']), 'Under review')

        path.write_text(original)
        self.assertTrue(load_nodes(self.root)[
                        'library-second']['review_matches_last_check'])
        binding = json.loads(original)
        binding['description'] = 'A changed claim that needs another correspondence review.'
        path.write_text(json.dumps(binding))
        self.assertFalse(load_nodes(self.root)[
                         'library-second']['review_matches_last_check'])
        self.assertTrue(load_nodes(self.root)[
                        'library-first']['review_matches_last_check'])

    def test_failed_attempts_retain_original_inputs_even_when_new_inputs_are_unavailable(self):
        self.add_library()
        before = self.report()
        original = self.source.read_text()
        self.source.write_text(
            original + '\n-- Changed since the successful check\n')
        with self.assertRaisesRegex(CommandError, 'Cannot build'):
            self.check(modules=[self.fixture_module],
                       failing=[self.fixture_module])
        failed = self.report()['modules'][self.fixture_module]
        self.assertNotEqual(failed['sha256'], failed['last_success']['sha256'])
        self.assertEqual(failed['last_success'],
                         before['modules'][self.fixture_module])

        self.source.unlink()
        with self.assertRaisesRegex(CommandError, 'Missing imported Lean source'):
            self.check(modules=[self.fixture_module])
        failed = self.report()['modules'][self.fixture_module]
        self.assertEqual(failed['sha256'], {})
        self.assertEqual(failed['last_success'],
                         before['modules'][self.fixture_module])
        self.assertEqual(self.report()['nodes'], before['nodes'])
        self.assertTrue(load_nodes(self.root)[
                        'ready']['review_matches_last_check'])
        self.write_html(('data-formal="ready"',))
        self.assertEqual(entries()['first']
                         ['formalization']['status'], 'partial')

        self.source.write_text(original)
        self.assertFalse(load_nodes(self.root)[
                         'ready']['verification_complete'])
        self.check(modules=[self.fixture_module])
        self.assertNotIn('last_success', self.report()[
                         'modules'][self.fixture_module])
        self.assertEqual(load_nodes(self.root)['ready']['status'], 'complete')

    def test_first_failure_has_no_successful_history_and_does_not_create_snapshots(self):
        self.add_module('new-node', 'Lemmatheca.New')
        with self.assertRaisesRegex(CommandError, 'Cannot build'):
            self.check(modules=['Lemmatheca.New'], failing=['Lemmatheca.New'])
        failed = self.report()['modules']['Lemmatheca.New']
        self.assertEqual(failed['status'], 'failed')
        self.assertNotIn('last_success', failed)
        self.assertNotIn('new-node', self.report()['nodes'])
        node = load_nodes(self.root)['new-node']
        self.assertFalse(node['review_matches_last_check'])
        self.assertFalse(node['verification_complete'])

    def test_clean_cached_evidence_uses_git_without_python_scans_or_source_hashes(self):
        _, aesop = self.add_library()
        ignore = aesop.parents[1] / '.gitignore'
        ignore.write_text('.lake/\n')
        self.commit_library('aesop')
        self.check()
        report = self.report()
        hashes = report['modules'][self.fixture_module]['sha256']
        self.assertIn(LIBRARY_INPUT, hashes)
        self.assertFalse(any(path.startswith(LIBRARY_INPUT + '/')
                         for path in hashes))
        build = ignore.parent / '.lake/build'
        build.mkdir(parents=True)
        (build / 'Constants.olean').write_text('Ignored build output')
        read_bytes, walk = Path.read_bytes, os.walk

        def read_local(path):
            self.assertFalse(path.is_relative_to(
                self.formal / '.lake/packages'))
            return read_bytes(path)

        def walk_local(path):
            self.assertFalse(path.is_relative_to(
                self.formal / '.lake/packages'))
            return walk(path)

        with patch.object(Path, 'read_bytes', read_local), patch('formalization.lean.os.walk', walk_local):
            self.assertEqual(load_nodes(self.root)[
                             'ready']['status'], 'complete')
            self.check()
        self.assertEqual(self.built, [])
        self.assertEqual(self.report(), report)

    def test_dirty_packages_invalidate_reader_cache_and_block_verification(self):
        _, aesop = self.add_library()
        self.library_git('aesop', 'config', 'status.showUntrackedFiles', 'no')
        self.write_html(('data-formal="ready"',))
        original = aesop.read_text()
        for change in ('unstaged', 'staged', 'deleted', 'untracked'):
            with self.subTest(change=change):
                self.assertEqual(
                    entries()['first']['formalization']['status'], 'complete')
                added = aesop.with_name('New.lean')
                if change in ('unstaged', 'staged'):
                    aesop.write_text(original + '-- An uncommitted edit\n')
                    if change == 'staged':
                        self.library_git('aesop', 'add', '.')
                elif change == 'deleted':
                    aesop.unlink()
                else:
                    added.write_text('-- Untracked library source\n')
                self.assertEqual(load_nodes(self.root)[
                                 'ready']['status'], 'verification_needed')
                self.assertEqual(
                    entries()['first']['formalization']['status'], 'partial')
                self.assertEqual(load_nodes(self.root)[
                                 'independent']['status'], 'complete')
                with self.assertRaisesRegex(CommandError, 'aesop: uncommitted or untracked files'):
                    self.check(modules=[self.fixture_module])
                self.assertEqual(self.built, [])
                self.assertEqual(
                    self.report()['modules'][self.fixture_module]['status'], 'failed')
                self.library_git('aesop', 'reset', '--mixed', 'HEAD')
                aesop.write_text(original)
                added.unlink(missing_ok=True)
                self.check(modules=[self.fixture_module])
                self.assertEqual(
                    entries()['first']['formalization']['status'], 'complete')

    def test_archives_cannot_be_verified_and_dirty_changes_during_check_fail(self):
        _, aesop = self.add_library()
        original = aesop.read_text()
        with self.assertRaisesRegex(CommandError, 'aesop: uncommitted or untracked files'):
            self.check(modules=[self.fixture_module], force=True,
                       during_check=lambda module: aesop.write_text(original + '-- Changed during check\n'))
        self.assertEqual(self.report()['modules']
                         [self.fixture_module]['status'], 'failed')
        aesop.write_text(original)
        self.check(modules=[self.fixture_module])
        shutil.rmtree(aesop.parents[1] / '.git')
        self.assertEqual(load_nodes(self.root)[
                         'ready']['status'], 'verification_needed')
        with self.assertRaisesRegex(CommandError, 'aesop: missing Git checkout metadata'):
            self.check(modules=[self.fixture_module])
        self.assertEqual(self.built, [])

    def test_web_only_evidence_can_be_read_but_not_reused_for_verification(self):
        self.add_library_bindings()
        shutil.rmtree(self.formal / '.lake/packages')
        self.assertEqual(load_nodes(self.root)[
                         'library-first']['status'], 'complete')
        with self.assertRaisesRegex(CommandError, 'Missing imported Lean source'):
            self.check(modules=['Mathlib'])
        self.assertEqual(self.built, [])

    def test_unavailable_git_makes_library_evidence_stale(self):
        self.add_library()
        with patch('formalization.lean.run_git', side_effect=FileNotFoundError('git')):
            self.assertEqual(load_nodes(self.root)[
                             'ready']['status'], 'verification_needed')
            self.assertEqual(load_nodes(self.root)[
                             'independent']['status'], 'complete')
            with self.assertRaisesRegex(CommandError, 'cannot read Git checkout status'):
                self.check(modules=[self.fixture_module])
        self.assertEqual(self.built, [])

    def test_installed_revision_and_package_inventory_changes_invalidate_library_users(self):
        self.add_library()
        original = self.library_git('aesop', 'rev-parse', 'HEAD')
        self.write_html(('data-formal="ready"',))
        self.assertEqual(entries()['first']
                         ['formalization']['status'], 'complete')
        self.commit_library('aesop')
        self.assertEqual(load_nodes(self.root)[
                         'ready']['status'], 'verification_needed')
        self.assertEqual(load_nodes(self.root)[
                         'independent']['status'], 'complete')
        self.assertEqual(entries()['first']
                         ['formalization']['status'], 'partial')
        self.library_git('aesop', 'checkout', '--detach', original)
        self.assertEqual(entries()['first']
                         ['formalization']['status'], 'complete')

        package = self.formal / '.lake/packages/aesop'
        removed = self.root / 'removed-aesop'
        package.rename(removed)
        self.assertEqual(load_nodes(self.root)[
                         'ready']['status'], 'verification_needed')
        removed.rename(package)
        self.assertEqual(load_nodes(self.root)['ready']['status'], 'complete')
        self.commit_library('extra-package')
        self.assertEqual(load_nodes(self.root)[
                         'ready']['status'], 'verification_needed')

    def test_unreadable_installed_revision_cannot_be_verified(self):
        self.add_library()
        (self.formal / '.lake/packages/aesop/.git/HEAD').write_text('not a revision\n')
        self.assertEqual(load_nodes(self.root)[
                         'ready']['status'], 'verification_needed')
        with self.assertRaisesRegex(CommandError, 'clean Git checkouts'):
            self.check(modules=[self.fixture_module])
        self.assertEqual(load_nodes(self.root)[
                         'independent']['status'], 'complete')

    def test_git_branches_packed_refs_and_worktrees_resolve_to_commits(self):
        self.add_library()
        first = self.library_git('aesop', 'rev-parse', 'HEAD')
        self.assertEqual(library_revisions(self.root)['aesop'], first)
        second = self.commit_library('aesop')
        self.assertNotEqual(first, second)
        self.assertEqual(load_nodes(self.root)[
                         'ready']['status'], 'verification_needed')
        self.assertEqual(load_nodes(self.root)[
                         'independent']['status'], 'complete')
        fingerprint = library_hash(self.root)
        self.library_git('aesop', 'pack-refs', '--all', '--prune')
        self.assertEqual(library_revisions(self.root)['aesop'], second)
        self.assertEqual(library_hash(self.root), fingerprint)
        linked = self.formal / '.lake/packages/linked'
        self.library_git('aesop', 'worktree', 'add',
                         '--detach', str(linked), first)
        self.assertEqual(library_revisions(self.root)['linked'], first)
        (linked / 'Aesop/Constants.lean').write_text('-- Edited linked checkout\n')
        self.assertIsNone(library_revisions(self.root)['linked'])

    def test_library_snapshots_remain_distinct_across_partial_rechecks(self):
        self.add_library()
        before = self.report()
        self.commit_library('aesop')
        self.check(modules=[self.fixture_module])
        partial = self.report()
        self.assertNotEqual(partial['modules'][self.fixture_module]['sha256'][LIBRARY_INPUT],
                            partial['modules'][self.importer_module]['sha256'][LIBRARY_INPUT])
        self.assertEqual(partial['modules'][self.importer_module],
                         before['modules'][self.importer_module])
        self.assertEqual(load_nodes(self.root)['ready']['status'], 'complete')
        self.assertEqual(load_nodes(self.root)[
                         'uses-fixture']['status'], 'verification_needed')
        self.check()
        self.assertEqual(set(self.built), {
                         self.importer_module, self.transitive_module})
        current = self.report()
        self.assertEqual(current['modules'][self.fixture_module]['sha256'][LIBRARY_INPUT],
                         current['modules'][self.importer_module]['sha256'][LIBRARY_INPUT])
        self.assertEqual(current['modules'][self.independent_module],
                         before['modules'][self.independent_module])

    def test_library_revision_change_during_verification_cannot_produce_passing_evidence(self):
        self.add_library()
        with self.assertRaisesRegex(CommandError, 'changed during verification'):
            self.check(modules=[self.fixture_module], force=True,
                       during_check=lambda module: self.commit_library('aesop'))
        self.assertEqual(self.report()['modules']
                         [self.fixture_module]['status'], 'failed')
        self.assertEqual(load_nodes(self.root)[
                         'ready']['status'], 'verification_needed')

    def test_changes_during_check_are_scoped_to_that_modules_inputs(self):
        before = self.report()
        self.check(modules=[self.independent_module], force=True,
                   during_check=lambda module: self.source.write_text(self.source.read_text() + '\n'))
        self.assertEqual(load_nodes(self.root)[
                         'independent']['status'], 'complete')
        self.assertEqual(self.report()[
                         'modules'][self.fixture_module], before['modules'][self.fixture_module])
        with self.assertRaisesRegex(CommandError, 'changed during verification'):
            self.check(modules=[self.independent_module], force=True,
                       during_check=lambda module: self.independent.write_text(self.independent.read_text() + '\n'))
        self.assertEqual(
            self.report()['modules'][self.independent_module]['status'], 'failed')

    def test_concurrent_report_write_is_not_overwritten(self):
        concurrent = deepcopy(self.report())
        concurrent['command'] = 'Another verification process'
        path = self.root / REPORT
        with self.assertRaisesRegex(CommandError, 'report changed during checking'):
            self.check(modules=[self.independent_module], force=True,
                       during_check=lambda module: path.write_text(json.dumps(concurrent)))
        self.assertEqual(self.report(), concurrent)

    def test_new_shadowing_source_invalidates_importers_and_the_catalog_cache(self):
        external = self.formal / '.lake/packages/mathlib/Mathlib/Support.lean'
        external.parent.mkdir(parents=True)
        external.write_text('-- Pinned source\n')
        self.commit_library('mathlib')
        self.source.write_text(
            'import Mathlib.Support\n' + self.source.read_text())
        self.check()
        self.write_html(('data-formal="ready"',))
        self.assertEqual(entries()['first']
                         ['formalization']['status'], 'complete')
        local = self.formal / 'Mathlib/Support.lean'
        local.parent.mkdir()
        local.write_text('-- A different source with the same module name\n')
        self.assertEqual(entries()['first']
                         ['formalization']['status'], 'partial')
        self.assertEqual(load_nodes(self.root)[
                         'independent']['status'], 'complete')

    def test_accept_refresh_selects_only_the_requested_nodes_modules(self):
        self.independent.write_text(self.independent.read_text() + '\n')
        with patch('catalog.management.commands.review.call_command') as check:
            with self.assertRaisesRegex(CommandError, 'Current target hashes are unavailable'):
                call_command('review', '--accept',
                             node=['independent'], stdout=StringIO())
        self.assertEqual(check.call_args.kwargs['module'], [
                         self.independent_module])
