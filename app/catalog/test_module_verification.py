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
from formalization.lean import LIBRARY_INPUT, library_revisions, run_git
from formalization.nodes import ALLOWED_AXIOMS, ENVIRONMENT, REPORT, REPORT_VERSION, library_hash, load_nodes


class ModuleVerificationTests(NodeFixtureMixin, SimpleTestCase):
    fixture_module = 'Lemmatheca.Fixture'
    independent_module = 'Lemmatheca.Independent'
    importer_module = 'Lemmatheca.UsesFixture'
    transitive_module = 'Lemmatheca.Transitive'

    def setUp(self):
        super().setUp()
        self.independent = self.add_module('independent', self.independent_module)
        self.add_module('uses-fixture', self.importer_module, self.fixture_module)
        self.add_module('transitive', self.transitive_module, self.importer_module)
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
                axioms = 'sorryAx' if name in ('Lemmatheca.unfinished', 'Lemmatheca.dependent') else ''
                output.extend((f"'{name}' depends on axioms: [{axioms}]",
                               'NODE_SIGNATURE ' + json.dumps({'name': name, 'signature': f'{name} : True'}),
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
        self.source.write_text(self.source.read_text() + '\n-- A changed proof.\n')
        nodes = load_nodes(self.root)
        for key in ('ready', 'pending', 'dependent', 'uses-fixture', 'transitive'):
            self.assertEqual(nodes[key]['status'], 'verification_needed')
            self.assertIsNone(nodes[key]['checked_on'])
        self.assertEqual(nodes['independent']['status'], 'complete')
        self.assertEqual(nodes['independent']['checked_on'], independent_before['checked_on'])
        self.check()
        self.assertEqual(set(self.built), {self.fixture_module, self.importer_module, self.transitive_module})
        self.assertTrue(all(imports == [imports[0], 'Lemmatheca.ReviewChecks'] for imports in self.probes))
        after = self.report()
        self.assertEqual(before['modules'][self.independent_module], after['modules'][self.independent_module])
        self.assertEqual(before['nodes']['independent'], after['nodes']['independent'])
        self.assertEqual(load_nodes(self.root)['ready']['status'], 'complete')
        self.assertEqual(load_nodes(self.root)['dependent']['status'], 'proof_pending')

    def test_unrelated_file_creation_edit_and_removal_do_not_invalidate_evidence(self):
        before = (self.root / REPORT).read_bytes()
        unrelated = self.formal / 'Lemmatheca/Unregistered.lean'
        for content in ('not Lean code', 'still not Lean code', None):
            with self.subTest(content=content):
                if content is None:
                    unrelated.unlink()
                else:
                    unrelated.write_text(content)
                self.assertEqual(load_nodes(self.root)['ready']['status'], 'complete')
                self.check()
                self.assertEqual(self.built, [])
                self.assertEqual((self.root / REPORT).read_bytes(), before)

    def test_failed_modules_do_not_discard_successful_or_cached_checks(self):
        before = self.report()
        self.source.write_text(self.source.read_text() + '\n-- Broken module.\n')
        failed = {self.fixture_module, self.importer_module, self.transitive_module}
        with self.assertRaisesRegex(CommandError, 'Cannot build'):
            self.check(failing=failed)
        after = self.report()
        self.assertEqual(after['modules'][self.independent_module], before['modules'][self.independent_module])
        self.assertEqual(after['nodes']['independent'], before['nodes']['independent'])
        for module in failed:
            self.assertEqual(after['modules'][module]['status'], 'failed')
        self.assertEqual(load_nodes(self.root)['ready']['status'], 'verification_needed')
        self.assertEqual(load_nodes(self.root)['independent']['status'], 'complete')

        self.independent.write_text(self.independent.read_text() + '\n')
        with self.assertRaises(CommandError):
            self.check(failing=failed)
        updated = self.report()
        self.assertNotEqual(updated['modules'][self.independent_module]['checked_on'],
                            before['modules'][self.independent_module]['checked_on'])
        self.assertEqual(load_nodes(self.root)['independent']['status'], 'complete')

    def test_missing_local_module_does_not_break_unrelated_nodes_or_pages(self):
        self.source.unlink()
        nodes = load_nodes(self.root)
        self.assertEqual(nodes['ready']['status'], 'verification_needed')
        self.assertEqual(nodes['independent']['status'], 'complete')
        self.assertContains(self.client.get('/formal/nodes/ready/'), 'This source file is missing')
        with self.assertRaisesRegex(CommandError, 'Missing imported Lean source'):
            self.check()
        self.assertEqual(load_nodes(self.root)['independent']['status'], 'complete')

    def test_shared_exporter_environment_and_policy_changes_invalidate_all_modules(self):
        paths = [self.formal / name for name in ENVIRONMENT]
        paths.append(self.formal / 'Lemmatheca/ReviewChecks.lean')
        for path in paths:
            with self.subTest(path=path.name):
                original = path.read_text()
                path.write_text(original + '\n')
                self.assertTrue(all(node['status'] == 'verification_needed' for node in load_nodes(self.root).values()))
                path.write_text(original)
        with patch('formalization.nodes.ALLOWED_AXIOMS', ALLOWED_AXIOMS - {'Quot.sound'}):
            self.assertTrue(all(node['status'] == 'verification_needed' for node in load_nodes(self.root).values()))

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
        self.assertEqual(load_nodes(self.root)['independent']['status'], 'complete')

    def test_old_global_report_is_rechecked_without_changing_approvals(self):
        before = self.report()
        approvals = {path: path.read_bytes() for path in self.node_dir.glob('*.json')}
        old = {
            'format_version': 4, 'build': 'passed', 'checked_on': '2026-09-20T12:00:00+00:00',
            'sha256': {path: value for record in before['modules'].values()
                       for path, value in record['sha256'].items()},
            'nodes': before['nodes'],
        }
        (self.root / REPORT).write_text(json.dumps(old))
        self.assertEqual(load_nodes(self.root)['independent']['status'], 'verification_needed')
        self.check()
        self.assertEqual(set(self.built), set(before['modules']))
        self.assertEqual(self.report()['format_version'], REPORT_VERSION)
        self.assertTrue(load_nodes(self.root)['independent']['review_current'])
        self.assertEqual(self.report()['nodes'], before['nodes'])
        for path, content in approvals.items():
            self.assertEqual(path.read_bytes(), content)

    def test_old_indexed_report_is_ignored_by_reader_cache_and_rebuilt(self):
        before = self.report()
        approvals = {path: path.read_bytes() for path in self.node_dir.glob('*.json')}
        indexed = deepcopy(before)
        indexed['format_version'] = 6
        indexed['inputs'] = [[self.source.relative_to(self.root).as_posix(), 'a' * 64]]
        for record in indexed['modules'].values():
            record['sha256'] = [0]
        (self.root / REPORT).write_text(json.dumps(indexed))
        self.assertEqual(entries()['first']['formalization']['status'], 'partial')
        self.assertEqual(load_nodes(self.root)['ready']['status'], 'verification_needed')
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
        self.assertNotEqual(partial['modules'][self.fixture_module]['sha256'][source_key], old_hash)
        self.assertEqual(partial['modules'][self.importer_module]['sha256'][source_key], old_hash)
        self.assertEqual(partial['modules'][self.importer_module], before['modules'][self.importer_module])
        self.assertEqual(partial['modules'][self.independent_module], before['modules'][self.independent_module])
        nodes = load_nodes(self.root)
        self.assertEqual(nodes['ready']['status'], 'complete')
        self.assertEqual(nodes['uses-fixture']['status'], 'verification_needed')

        self.check()
        self.assertEqual(set(self.built), {self.importer_module, self.transitive_module})
        current = self.report()
        self.assertEqual(current['modules'][self.fixture_module]['sha256'][source_key],
                         current['modules'][self.importer_module]['sha256'][source_key])
        self.assertEqual(current['modules'][self.independent_module], before['modules'][self.independent_module])

    def test_invalid_input_hashes_stale_only_the_affected_module(self):
        original = self.report()
        hashes = original['modules'][self.fixture_module]['sha256']
        path = self.source.relative_to(self.root).as_posix()
        for invalid in ({}, [], None, {**hashes, path: 'invalid hash'}, {**hashes, path: True},
                        {**hashes, 'formal/.lake/packages/mathlib/Mathlib/Old.lean': 'a' * 64}):
            with self.subTest(hashes=invalid):
                report = deepcopy(original)
                report['modules'][self.fixture_module]['sha256'] = invalid
                (self.root / REPORT).write_text(json.dumps(report))
                nodes = load_nodes(self.root)
                self.assertEqual(nodes['ready']['status'], 'verification_needed')
                self.assertEqual(nodes['independent']['status'], 'complete')
                self.assertEqual(entries()['first']['formalization']['status'], 'partial')

    def add_library(self):
        sources = []
        for package, module in (('mathlib', 'Mathlib/Support'), ('aesop', 'Aesop/Constants')):
            path = self.formal / '.lake/packages' / package / (module + '.lean')
            path.parent.mkdir(parents=True)
            path.write_text('-- Library source\n')
            sources.append(path)
            self.set_library_revision(package, 'a' * 40)
        self.source.write_text('import Mathlib.Support\n' + self.source.read_text())
        self.check()
        return sources

    def set_library_revision(self, package, revision):
        git = self.formal / '.lake/packages' / package / '.git'
        git.mkdir(parents=True, exist_ok=True)
        (git / 'HEAD').write_text(revision + '\n')

    def add_library_bindings(self):
        for node_id, module in (('library-first', 'Mathlib.First'), ('library-second', 'Mathlib.Second')):
            path = self.formal / '.lake/packages/mathlib' / (module.replace('.', '/') + '.lean')
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(f'theorem {module}.result : True := by trivial\n')
            self.write_node(node_id, module=module, declaration=f'{module}.result')
        self.check()

    def test_mathlib_bindings_share_one_record_but_check_their_own_imports(self):
        self.add_library_bindings()
        report = self.report()
        self.assertIn('Mathlib', report['modules'])
        self.assertFalse(any(name.startswith('Mathlib.') for name in report['modules']))
        self.assertNotIn('inputs', report)
        self.assertEqual(set(self.built), {'Mathlib.First', 'Mathlib.Second'})
        self.assertEqual(self.probes, [['Mathlib.First', 'Lemmatheca.ReviewChecks'],
                                     ['Mathlib.Second', 'Lemmatheca.ReviewChecks']])
        self.assertIsInstance(report['modules']['Mathlib']['sha256'], dict)
        nodes = load_nodes(self.root)
        for key in ('library-first', 'library-second'):
            self.assertEqual(nodes[key]['status'], 'complete')
            self.assertEqual(nodes[key]['checked_on'], report['modules']['Mathlib']['checked_on'])
        self.assertEqual(nodes['library-first']['module'], 'Mathlib.First')
        self.assertEqual(nodes['library-second']['module'], 'Mathlib.Second')

    def test_mathlib_selector_refreshes_the_shared_audit_and_preserves_local_records(self):
        self.add_library_bindings()
        before = self.report()
        self.check(modules=['Mathlib.First'], force=True)
        self.assertEqual(set(self.built), {'Mathlib.First', 'Mathlib.Second'})
        for name, record in before['modules'].items():
            if name != 'Mathlib':
                self.assertEqual(self.report()['modules'][name], record)
        self.check(modules=['Mathlib'])
        self.assertEqual(self.built, [])
        with self.assertRaisesRegex(CommandError, 'Unknown registered modules'):
            self.check(modules=['Mathlib.Unregistered'])
        self.write_node('another-library-binding', module='Mathlib.First', declaration='Mathlib.First.another')
        self.check()
        self.assertEqual(set(self.built), {'Mathlib.First', 'Mathlib.Second'})
        self.assertEqual(load_nodes(self.root)['another-library-binding']['status'], 'complete')

    def test_local_proof_edits_preserve_mathlib_verification(self):
        self.add_library_bindings()
        before = self.report()['modules']['Mathlib']
        self.source.write_text(self.source.read_text() + '\n-- Local proof edit\n')
        nodes = load_nodes(self.root)
        self.assertEqual(nodes['ready']['status'], 'verification_needed')
        self.assertEqual(nodes['library-first']['status'], 'complete')
        self.check()
        self.assertNotIn('Mathlib.First', self.built)
        self.assertEqual(self.report()['modules']['Mathlib'], before)

    def test_failed_mathlib_audit_discards_no_local_evidence(self):
        self.add_library_bindings()
        before = self.report()
        with self.assertRaisesRegex(CommandError, 'Cannot audit Mathlib.Second'):
            self.check(modules=['Mathlib'], force=True, failing_probes=['Mathlib.Second'])
        report = self.report()
        self.assertEqual(report['modules']['Mathlib']['status'], 'failed')
        for key in ('library-first', 'library-second'):
            self.assertNotIn(key, report['nodes'])
            self.assertEqual(load_nodes(self.root)[key]['status'], 'verification_needed')
        self.assertEqual(load_nodes(self.root)['ready']['status'], 'complete')
        self.assertEqual(report['modules'][self.fixture_module], before['modules'][self.fixture_module])

    def test_reused_evidence_does_not_scan_or_hash_library_sources(self):
        _, aesop = self.add_library()
        report = self.report()
        self.assertNotIn('inputs', report)
        hashes = report['modules'][self.fixture_module]['sha256']
        self.assertIn(LIBRARY_INPUT, hashes)
        self.assertFalse(any(path.startswith(LIBRARY_INPUT + '/') for path in hashes))
        self.write_html(('data-formal="ready"',))
        self.assertEqual(entries()['first']['formalization']['status'], 'complete')
        original = aesop.read_text()
        read_bytes = Path.read_bytes
        walk = os.walk

        def read_local(path):
            self.assertFalse(path.is_relative_to(self.formal / '.lake/packages'))
            return read_bytes(path)

        def walk_local(path):
            self.assertFalse(path.is_relative_to(self.formal / '.lake/packages'))
            return walk(path)

        for change in ('edit', 'remove', 'add'):
            with self.subTest(change=change):
                added = aesop.with_name('New.lean')
                if change == 'edit':
                    aesop.write_text(original + '-- Edited without changing the revision pin.\n')
                elif change == 'remove':
                    aesop.unlink()
                else:
                    added.write_text('-- Added library source\n')
                with patch.object(Path, 'read_bytes', read_local), patch('formalization.lean.os.walk', walk_local):
                    self.assertEqual(load_nodes(self.root)['ready']['status'], 'complete')
                    self.assertEqual(entries()['first']['formalization']['status'], 'complete')
                    self.check()
                self.assertEqual(self.built, [])
                self.assertEqual(self.report(), report)
                aesop.write_text(original)
                added.unlink(missing_ok=True)
                self.assertEqual(load_nodes(self.root)['ready']['status'], 'complete')

    def test_installed_revision_and_package_inventory_changes_invalidate_library_users(self):
        self.add_library()
        self.write_html(('data-formal="ready"',))
        self.assertEqual(entries()['first']['formalization']['status'], 'complete')
        self.set_library_revision('aesop', 'b' * 40)
        self.assertEqual(load_nodes(self.root)['ready']['status'], 'verification_needed')
        self.assertEqual(load_nodes(self.root)['independent']['status'], 'complete')
        self.assertEqual(entries()['first']['formalization']['status'], 'partial')
        self.set_library_revision('aesop', 'a' * 40)
        self.assertEqual(entries()['first']['formalization']['status'], 'complete')

        package = self.formal / '.lake/packages/aesop'
        removed = self.root / 'removed-aesop'
        package.rename(removed)
        self.assertEqual(load_nodes(self.root)['ready']['status'], 'verification_needed')
        removed.rename(package)
        self.assertEqual(load_nodes(self.root)['ready']['status'], 'complete')
        self.set_library_revision('extra-package', 'c' * 40)
        self.assertEqual(load_nodes(self.root)['ready']['status'], 'verification_needed')

    def test_unreadable_installed_revision_cannot_be_verified(self):
        self.add_library()
        self.set_library_revision('aesop', 'not a revision')
        self.assertEqual(load_nodes(self.root)['ready']['status'], 'verification_needed')
        with self.assertRaisesRegex(CommandError, 'unreadable package revisions'):
            self.check(modules=[self.fixture_module])
        self.assertEqual(load_nodes(self.root)['independent']['status'], 'complete')

    def test_git_branches_packed_refs_and_worktrees_resolve_to_commits(self):
        self.add_library()
        package = self.formal / '.lake/packages/aesop'
        shutil.rmtree(package / '.git')

        def git(*args):
            return run_git(['git', '-C', str(package), *args], check=True,
                           capture_output=True, text=True).stdout.strip()

        def commit():
            git('-c', 'user.name=Test', '-c', 'user.email=test@example.com',
                '-c', 'commit.gpgsign=false', 'commit', '--allow-empty', '-m', 'Test revision')
            return git('rev-parse', 'HEAD')

        git('init', '--initial-branch=main')
        first = commit()
        self.assertEqual(library_revisions(self.root)['aesop'], first)
        self.check()
        second = commit()
        self.assertNotEqual(first, second)
        self.assertEqual(load_nodes(self.root)['ready']['status'], 'verification_needed')
        self.assertEqual(load_nodes(self.root)['independent']['status'], 'complete')
        fingerprint = library_hash(self.root)
        git('pack-refs', '--all', '--prune')
        self.assertEqual(library_revisions(self.root)['aesop'], second)
        self.assertEqual(library_hash(self.root), fingerprint)
        git('worktree', 'add', '--detach', str(package.with_name('linked')), first)
        self.assertEqual(library_revisions(self.root)['linked'], first)

    def test_library_snapshots_remain_distinct_across_partial_rechecks(self):
        self.add_library()
        before = self.report()
        self.set_library_revision('aesop', 'b' * 40)
        self.check(modules=[self.fixture_module])
        partial = self.report()
        self.assertNotEqual(partial['modules'][self.fixture_module]['sha256'][LIBRARY_INPUT],
                            partial['modules'][self.importer_module]['sha256'][LIBRARY_INPUT])
        self.assertEqual(partial['modules'][self.importer_module], before['modules'][self.importer_module])
        self.assertEqual(load_nodes(self.root)['ready']['status'], 'complete')
        self.assertEqual(load_nodes(self.root)['uses-fixture']['status'], 'verification_needed')
        self.check()
        self.assertEqual(set(self.built), {self.importer_module, self.transitive_module})
        current = self.report()
        self.assertEqual(current['modules'][self.fixture_module]['sha256'][LIBRARY_INPUT],
                         current['modules'][self.importer_module]['sha256'][LIBRARY_INPUT])
        self.assertEqual(current['modules'][self.independent_module], before['modules'][self.independent_module])

    def test_library_revision_change_during_verification_cannot_produce_passing_evidence(self):
        self.add_library()
        with self.assertRaisesRegex(CommandError, 'changed during verification'):
            self.check(modules=[self.fixture_module], force=True,
                       during_check=lambda module: self.set_library_revision('aesop', 'b' * 40))
        self.assertEqual(self.report()['modules'][self.fixture_module]['status'], 'failed')
        self.assertEqual(load_nodes(self.root)['ready']['status'], 'verification_needed')

    def test_changes_during_check_are_scoped_to_that_modules_inputs(self):
        before = self.report()
        self.check(modules=[self.independent_module], force=True,
                   during_check=lambda module: self.source.write_text(self.source.read_text() + '\n'))
        self.assertEqual(load_nodes(self.root)['independent']['status'], 'complete')
        self.assertEqual(self.report()['modules'][self.fixture_module], before['modules'][self.fixture_module])
        with self.assertRaisesRegex(CommandError, 'changed during verification'):
            self.check(modules=[self.independent_module], force=True,
                       during_check=lambda module: self.independent.write_text(self.independent.read_text() + '\n'))
        self.assertEqual(self.report()['modules'][self.independent_module]['status'], 'failed')

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
        self.source.write_text('import Mathlib.Support\n' + self.source.read_text())
        self.check()
        self.write_html(('data-formal="ready"',))
        self.assertEqual(entries()['first']['formalization']['status'], 'complete')
        local = self.formal / 'Mathlib/Support.lean'
        local.parent.mkdir()
        local.write_text('-- A different source with the same module name\n')
        self.assertEqual(entries()['first']['formalization']['status'], 'partial')
        self.assertEqual(load_nodes(self.root)['independent']['status'], 'complete')

    def test_accept_refresh_selects_only_the_requested_nodes_modules(self):
        self.independent.write_text(self.independent.read_text() + '\n')
        with patch('catalog.management.commands.review.call_command') as check:
            with self.assertRaisesRegex(CommandError, 'Current target hashes are unavailable'):
                call_command('review', '--accept', node=['independent'], stdout=StringIO())
        self.assertEqual(check.call_args.kwargs['module'], [self.independent_module])
