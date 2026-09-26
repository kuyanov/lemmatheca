"""Approval records bind to current targets, independently of proof completion."""

from copy import deepcopy
from io import StringIO
import json
from unittest.mock import patch

from django.core.management import call_command
from django.core.management.base import CommandError
from django.test import SimpleTestCase

from catalog.sources import ContentError
from catalog.test_formalizations import NodeFixtureMixin
from formalization.nodes import load_nodes
from formalization.verification import REPORT
from formalization.reviews import declaration_hashes, review_target_hash


class ReviewHashTests(SimpleTestCase):
    def test_reachable_definitions_and_inductive_cycles_affect_the_target(self):
        records = {
            'target': {'payload': ['theorem', 'P'], 'references': ['P']},
            'P': {'payload': ['definition', 'True'], 'references': ['T']},
            'T': {'payload': ['inductive', 'mk'], 'references': ['mk']},
            'mk': {'payload': ['constructor', 'T'], 'references': ['T']},
            'unrelated': {'payload': ['definition', 1], 'references': []},
        }
        original = declaration_hashes(records, ['target'])['target']
        for name in ('target', 'P', 'T', 'mk'):
            changed = deepcopy(records)
            changed[name]['payload'].append('changed')
            self.assertNotEqual(declaration_hashes(
                changed, ['target'])['target'], original)
        records['unrelated']['payload'].append('changed')
        self.assertEqual(declaration_hashes(
            records, ['target'])['target'], original)
        del records['P']
        with self.assertRaisesRegex(ContentError, 'Missing review snapshot'):
            declaration_hashes(records, ['target'])

    def test_review_covers_description_and_declaration_but_not_id_or_proof_planning(self):
        node = {'id': 'node', 'description': 'Every element has property P.',
                'declaration': 'Theorem', 'module': 'Old.Module', 'dependencies': []}
        original = review_target_hash(node, 'declaration')
        for field in ('description', 'declaration'):
            with self.subTest(field=field):
                self.assertNotEqual(original, review_target_hash(
                    {**node, field: 'changed'}, 'declaration'))
        for changes in ({'id': 'renamed-node'}, {'module': 'New.Module'}, {'dependencies': ['prerequisite']},
                        {'review': {'sha256': original, 'recorded_at': 'today'}}):
            with self.subTest(changes=changes):
                self.assertEqual(original, review_target_hash(
                    {**node, **changes}, 'declaration'))
        self.assertNotEqual(original, review_target_hash(node, 'changed'))


class ReviewCommandTests(NodeFixtureMixin, SimpleTestCase):
    def setUp(self):
        super().setUp()
        self.write_node('ready', accepted=False)
        self.write_node(
            'pending', declaration='Lemmatheca.unfinished', accepted=False)

    def node_records(self):
        return {path.name: path.read_bytes() for path in self.node_dir.glob('*.json')}

    def review(self, action, **options):
        output = StringIO()
        call_command('review', f'--{action}', stdout=output, **options)
        return output.getvalue()

    def accept(self, **options):
        return self.review('accept', **options)

    def retract(self, **options):
        return self.review('retract', **options)

    def test_requires_exactly_one_action_and_one_selection(self):
        before = self.node_records()
        for arguments in (
                ('--node', 'ready'),
                ('--accept', '--retract', '--node', 'ready'),
                ('--accept',), ('--retract',),
                ('--accept', '--node', 'ready', '--entry', 'first'),
                ('--accept', '--nodes-from-entry', 'first', '--entry', 'first'),
                ('--accept', '--nodes-from-entry', 'first', '--node', 'ready'),
                ('--retract', '--node', 'ready', '--entry', 'first')):
            with self.subTest(arguments=arguments), self.assertRaises(CommandError):
                call_command('review', *arguments,
                             stdout=StringIO(), stderr=StringIO())
        self.assertEqual(self.node_records(), before)

    def test_accept_node_is_scoped_and_idempotent_with_pending_proofs_allowed(self):
        report = (self.root / REPORT).read_bytes()
        pending_before = (self.node_dir / 'pending.json').read_bytes()
        self.assertIn('1 node(s)', self.accept(node=['ready', 'ready']))
        node = load_nodes(self.root)['ready']
        self.assertEqual(node['review']['sha256'], node['target_sha256'])
        self.assertEqual(node['status'], 'complete')
        self.assertEqual(
            (self.node_dir / 'pending.json').read_bytes(), pending_before)
        before = self.node_records()
        self.assertIn('1 skipped', self.accept(node=['ready']))
        self.assertEqual(self.node_records(), before)
        self.accept(node=['pending'])
        self.assertEqual(load_nodes(self.root)[
                         'pending']['status'], 'proof_pending')
        self.assertEqual((self.root / REPORT).read_bytes(), report)

    def test_accept_nodes_from_entry_deduplicates_nodes_and_does_not_change_unlinked_nodes(self):
        self.write_node('dependent', declaration='Lemmatheca.dependent',
                        dependencies=['pending'], accepted=False)
        self.write_html(('data-formal="ready pending"',
                        'data-formal="ready"', 'data-formal=""'))
        unlinked = (self.node_dir / 'dependent.json').read_bytes()
        metadata = self.html.with_suffix('.json').read_bytes()
        self.assertIn('2 node(s)', self.accept(nodes_from_entry='first'))
        self.assertEqual(self.html.with_suffix('.json').read_bytes(), metadata)
        nodes = load_nodes(self.root)
        self.assertTrue(nodes['ready']['review_current'])
        self.assertTrue(nodes['pending']['review_current'])
        self.assertIsNone(nodes['dependent']['review'])
        self.assertEqual(
            (self.node_dir / 'dependent.json').read_bytes(), unlinked)

    def test_accept_updated_description_uses_current_text_without_rechecking_lean(self):
        self.accept(node=['ready'])
        path = self.node_dir / 'ready.json'
        node = json.loads(path.read_text())
        previous_review = node['review']
        node['description'] = 'The updated statement to review.'
        path.write_text(json.dumps(node))
        expected = load_nodes(self.root)['ready']['target_sha256']
        report = (self.root / REPORT).read_bytes()
        with patch('catalog.management.commands.review.call_command') as check:
            self.accept(node=['ready'])
        check.assert_not_called()
        current = load_nodes(self.root)['ready']
        self.assertEqual(current['review']['sha256'], expected)
        self.assertNotEqual(
            current['review']['sha256'], previous_review['sha256'])
        self.assertTrue(current['review_current'])
        self.assertEqual((self.root / REPORT).read_bytes(), report)

    def test_dry_run_and_invalid_selections_do_not_accept_anything(self):
        before = self.node_records()
        self.assertIn('Would accept review for 2', self.accept(
            nodes_from_entry='first', dry_run=True))
        self.assertEqual(self.node_records(), before)
        for options in ({'node': ['ready', 'missing']}, {'nodes_from_entry': 'missing'}):
            with self.subTest(options=options), self.assertRaises(CommandError):
                self.accept(**options)
            self.assertEqual(self.node_records(), before)
        self.write_node('unwritten', declaration=None,
                        module=None, accepted=False)
        before = self.node_records()
        with self.assertRaisesRegex(CommandError, 'Declarations missing'):
            self.accept(node=['ready', 'unwritten'])
        self.assertEqual(self.node_records(), before)
        self.write_html(('data-formal="ready"', ''))
        with self.assertRaisesRegex(CommandError, 'without formal mappings'):
            self.accept(nodes_from_entry='first')
        self.assertEqual(self.node_records(), before)

    def test_refresh_required_checks_and_reject_changes_during_acceptance(self):
        self.source.write_text(self.source.read_text() + '\n')
        with patch('catalog.management.commands.review.call_command',
                   side_effect=lambda *a, **kw: self.write_report()) as check:
            self.accept(node=['ready'])
        check.assert_called_once()
        self.assertEqual(check.call_args.args, ('check_formalizations',))
        self.assertTrue(load_nodes(self.root)['ready']['review_current'])

        self.source.write_text(self.source.read_text() + '\n')

        def edit_during_check(*args, **kwargs):
            self.write_node(
                'ready', declaration='Lemmatheca.unfinished', accepted=False)
            self.write_report()
        with patch('catalog.management.commands.review.call_command', side_effect=edit_during_check):
            with self.assertRaisesRegex(CommandError, 'records changed during review'):
                self.accept(node=['ready'])
        self.assertIsNone(load_nodes(self.root)['ready']['review'])

    def test_statement_changes_need_new_review_but_proof_only_refreshes_keep_it(self):
        self.accept(node=['ready'])
        accepted = (self.node_dir / 'ready.json').read_bytes()
        self.source.write_text(self.source.read_text().replace(
            'by trivial', 'by exact True.intro'))
        self.assertEqual(load_nodes(self.root)[
                         'ready']['status'], 'verification_needed')
        # A successful recheck with the same target hash retains statement approval.
        self.write_report()
        self.assertEqual(load_nodes(self.root)['ready']['status'], 'complete')
        self.assertEqual((self.node_dir / 'ready.json').read_bytes(), accepted)

        path = self.root / REPORT
        report = json.loads(path.read_text())
        report['nodes']['ready']['declaration_sha256'] = 'b' * 64
        path.write_text(json.dumps(report))
        node = load_nodes(self.root)['ready']
        self.assertEqual(node['status'], 'review_outdated')
        self.assertFalse(node['review_current'])
        response = self.client.get('/formal/nodes/ready/')
        self.assertContains(response, 'Review outdated')
        self.assertEqual((self.node_dir / 'ready.json').read_bytes(), accepted)
        self.accept(node=['ready'])
        self.assertEqual(load_nodes(self.root)['ready']['status'], 'complete')
        self.assertEqual(load_nodes(self.root)[
                         'ready']['review']['sha256'], node['target_sha256'])

    def test_description_edit_during_refresh_cannot_be_accepted(self):
        self.source.write_text(self.source.read_text() + '\n')

        def edit_during_check(*args, **kwargs):
            path = self.node_dir / 'ready.json'
            node = json.loads(path.read_text())
            node['description'] = 'Changed while acceptance was running.'
            path.write_text(json.dumps(node))
            self.write_report()

        with patch('catalog.management.commands.review.call_command', side_effect=edit_during_check):
            with self.assertRaisesRegex(CommandError, 'records changed during review'):
                self.accept(node=['ready'])
        self.assertIsNone(load_nodes(self.root)['ready']['review'])

    def test_changed_binding_cannot_carry_forward_an_old_approval(self):
        self.accept(node=['ready'])
        path = self.node_dir / 'ready.json'
        node = json.loads(path.read_text())
        old_review = node['review']
        node['declaration'] = 'Lemmatheca.unfinished'
        path.write_text(json.dumps(node))
        self.assertEqual(load_nodes(self.root)[
                         'ready']['status'], 'verification_needed')
        self.write_report()
        current = load_nodes(self.root)['ready']
        self.assertEqual(current['status'], 'review_outdated')
        self.assertEqual(current['review'], old_review)

    def test_entry_edits_during_refresh_leave_all_approvals_unchanged(self):
        self.source.write_text(self.source.read_text() + '\n')
        before = self.node_records()

        def edit_during_check(*args, **kwargs):
            self.write_html(('data-formal="ready"', 'data-formal=""'))
            self.write_report()
        with patch('catalog.management.commands.review.call_command', side_effect=edit_during_check):
            with self.assertRaisesRegex(CommandError, 'inputs changed'):
                self.accept(nodes_from_entry='first')
        self.assertEqual(self.node_records(), before)

    def test_retract_node_is_scoped_idempotent_and_preserves_verification(self):
        self.accept(node=['ready', 'pending'])
        before = self.node_records()
        report = (self.root / REPORT).read_bytes()
        with patch('catalog.management.commands.review.call_command') as check:
            self.assertIn('Retracted review for 1 node(s)',
                          self.retract(node=['ready', 'ready']))
            after = self.node_records()
            self.assertIn('0 node(s); 1 skipped', self.retract(node=['ready']))
        check.assert_not_called()
        self.assertEqual(self.node_records(), after)
        expected = json.loads(before['ready.json'])
        expected['review'] = None
        self.assertEqual(json.loads(after['ready.json']), expected)
        for name in ('pending.json', 'dependent.json'):
            self.assertEqual(after[name], before[name])
        nodes = load_nodes(self.root)
        self.assertEqual(nodes['ready']['status'], 'review_pending')
        self.assertIsNotNone(nodes['ready']['target_sha256'])
        self.assertTrue(nodes['pending']['review_current'])
        self.assertEqual((self.root / REPORT).read_bytes(), report)
        self.accept(node=['ready'])
        self.assertEqual(load_nodes(self.root)['ready']['status'], 'complete')

    def test_retract_nodes_from_entry_deduplicates_and_allows_unplanned_blocks(self):
        self.accept(nodes_from_entry='first')
        self.accept(entry='first')
        metadata = self.html.with_suffix('.json').read_bytes()
        self.write_html(('data-formal="ready pending"',
                        'data-formal="ready"', 'data-formal=""', ''))
        unlinked = (self.node_dir / 'dependent.json').read_bytes()
        self.assertIn('Retracted review for 2 node(s)',
                      self.retract(nodes_from_entry='first'))
        self.assertEqual(self.html.with_suffix('.json').read_bytes(), metadata)
        nodes = load_nodes(self.root)
        self.assertIsNone(nodes['ready']['review'])
        self.assertIsNone(nodes['pending']['review'])
        self.assertEqual(
            (self.node_dir / 'dependent.json').read_bytes(), unlinked)

    def test_retract_dry_run_and_invalid_selections_preserve_reviews(self):
        self.accept(nodes_from_entry='first')
        before = self.node_records()
        report = (self.root / REPORT).read_bytes()
        with patch('catalog.management.commands.review.call_command') as check:
            self.assertIn('Would retract review for 2', self.retract(
                nodes_from_entry='first', dry_run=True))
            self.assertEqual(self.node_records(), before)
            for options in ({'node': ['ready', 'missing']}, {'nodes_from_entry': 'missing'}):
                with self.subTest(options=options), self.assertRaises(CommandError):
                    self.retract(**options)
                self.assertEqual(self.node_records(), before)
        check.assert_not_called()
        self.assertEqual((self.root / REPORT).read_bytes(), report)

    def test_retract_needs_no_current_verification_or_matching_hash(self):
        path = self.root / REPORT
        for state in ('stale', 'missing', 'outdated'):
            with self.subTest(state=state):
                self.write_node('ready')
                self.write_report()
                if state == 'stale':
                    self.source.write_text(self.source.read_text() + '\n')
                elif state == 'missing':
                    path.unlink()
                else:
                    report = json.loads(path.read_text())
                    report['nodes']['ready']['declaration_sha256'] = 'b' * 64
                    path.write_text(json.dumps(report))
                report_before = path.read_bytes() if path.exists() else None
                with patch('catalog.management.commands.review.call_command') as check:
                    self.assertIn('Retracted review for 1',
                                  self.retract(node=['ready']))
                check.assert_not_called()
                self.assertIsNone(load_nodes(self.root)['ready']['review'])
                self.assertEqual(path.read_bytes()
                                 if path.exists() else None, report_before)

    def test_retract_skips_nodes_without_a_declaration(self):
        self.write_node('unwritten', declaration=None,
                        module=None, accepted=False)
        before = self.node_records()
        with patch('catalog.management.commands.review.call_command') as check:
            self.assertIn('0 node(s); 1 skipped',
                          self.retract(node=['unwritten']))
        check.assert_not_called()
        self.assertEqual(self.node_records(), before)

    def test_retract_does_not_change_a_verified_dependent_node(self):
        self.accept(node=['ready'])
        self.write_node(
            'dependent', declaration='Lemmatheca.dependent', dependencies=['ready'])
        self.write_report()
        path = self.root / REPORT
        report = json.loads(path.read_text())
        report['nodes']['dependent'].update(status='complete', axioms=[])
        path.write_text(json.dumps(report))
        self.assertEqual(load_nodes(self.root)[
                         'dependent']['status'], 'complete')
        dependent_before = (self.node_dir / 'dependent.json').read_bytes()
        report_before = path.read_bytes()
        self.retract(node=['ready'])
        nodes = load_nodes(self.root)
        self.assertEqual(nodes['ready']['status'], 'review_pending')
        self.assertEqual(nodes['dependent']['status'], 'complete')
        self.assertTrue(nodes['dependent']['review_current'])
        self.assertTrue(nodes['dependent']['verification_complete'])
        self.assertEqual(
            (self.node_dir / 'dependent.json').read_bytes(), dependent_before)
        self.assertEqual(path.read_bytes(), report_before)

    def test_failed_staging_preserves_all_reviews_and_removes_temporary_files(self):
        dump = json.dump
        for action in ('accept', 'retract'):
            with self.subTest(action=action):
                self.write_node('ready', accepted=action == 'retract')
                self.write_node(
                    'pending', declaration='Lemmatheca.unfinished', accepted=action == 'retract')
                before = self.node_records()
                files = set(self.node_dir.iterdir())
                writes = 0

                def fail_second_write(*args, **kwargs):
                    nonlocal writes
                    writes += 1
                    if writes == 2:
                        raise OSError('Cannot stage review')
                    return dump(*args, **kwargs)

                with patch('catalog.files.json.dump', side_effect=fail_second_write):
                    with self.assertRaisesRegex(CommandError, 'Cannot stage review'):
                        self.review(action, nodes_from_entry='first')
                self.assertEqual(self.node_records(), before)
                self.assertEqual(set(self.node_dir.iterdir()), files)


class EntryReviewCommandTests(NodeFixtureMixin, SimpleTestCase):
    def setUp(self):
        super().setUp()
        self.metadata_path = self.html.with_suffix('.json')
        self.write_node(
            'pending', declaration='Lemmatheca.unfinished', accepted=False)

    def review_entry(self, action, entry='first', dry_run=False):
        output = StringIO()
        arguments = ['review', f'--{action}', '--entry', entry]
        if dry_run:
            arguments.append('--dry-run')
        call_command(*arguments, stdout=output)
        return output.getvalue()

    def test_entry_approval_is_independent_of_node_reviews_and_proofs(self):
        before = json.loads(self.metadata_path.read_text())
        formal_before = {path: path.read_bytes()
                         for path in self.formal.rglob('*') if path.is_file()}
        self.assertEqual(load_nodes(self.root)[
                         'pending']['status'], 'review_pending')
        with patch('catalog.management.commands.review.call_command') as check:
            self.assertIn(
                'Accepted entry review for first; status: final', self.review_entry('accept'))
            accepted = self.metadata_path.read_bytes()
            self.assertIn('already final; skipped',
                          self.review_entry('accept'))
        check.assert_not_called()
        self.assertEqual(json.loads(accepted), {**before, 'status': 'final'})
        self.assertEqual(self.metadata_path.read_bytes(), accepted)
        self.assertEqual({path: path.read_bytes()
                         for path in formal_before}, formal_before)

    def test_draft_badge_and_note_disappear_and_return(self):
        for action in ('accept', 'retract'):
            with self.subTest(action=action):
                self.review_entry(action)
                for url in ('/entries/first/', '/areas/math/sets/'):
                    response = self.client.get(url)
                    if action == 'accept':
                        self.assertNotContains(
                            response, '<span class="pill">Draft</span>', html=True)
                        self.assertNotContains(
                            response, 'awaiting maintainer review')
                    else:
                        self.assertContains(
                            response, '<span class="pill">Draft</span>', html=True)
                    self.assertNotContains(
                        response, '<span class="pill">Final</span>', html=True)
                    self.assertContains(response, 'formalization-badge')
                if action == 'retract':
                    self.assertContains(self.client.get(
                        '/entries/first/'), 'awaiting maintainer review')

    def test_dry_run_and_retraction_preserve_formal_records(self):
        formal_before = {path: path.read_bytes()
                         for path in self.formal.rglob('*') if path.is_file()}
        for action, desired in (('accept', 'final'), ('retract', 'draft')):
            with self.subTest(action=action):
                before = self.metadata_path.read_bytes()
                self.assertIn(f'Would {action} entry review',
                              self.review_entry(action, dry_run=True))
                self.assertEqual(self.metadata_path.read_bytes(), before)
                self.review_entry(action)
                self.assertEqual(json.loads(self.metadata_path.read_text())[
                                 'status'], desired)
                after = self.metadata_path.read_bytes()
                self.assertIn('skipped', self.review_entry(action))
                self.assertEqual(self.metadata_path.read_bytes(), after)
        self.assertEqual({path: path.read_bytes()
                         for path in formal_before}, formal_before)

    def test_entry_approval_needs_mappings_and_declarations_but_no_lean_evidence(self):
        before = self.metadata_path.read_bytes()
        self.write_html(('data-formal="ready"', ''))
        with self.assertRaisesRegex(CommandError, 'without formal mappings: block-1'):
            self.review_entry('accept')
        self.assertEqual(self.metadata_path.read_bytes(), before)
        self.write_node('unwritten', declaration=None,
                        module=None, accepted=False)
        self.write_html(('data-formal="unwritten"',))
        with self.assertRaisesRegex(CommandError, 'Declarations missing: unwritten'):
            self.review_entry('accept')
        self.assertEqual(self.metadata_path.read_bytes(), before)
        self.write_html()
        (self.root / REPORT).unlink()
        with patch('catalog.management.commands.review.call_command') as check:
            self.review_entry('accept')
        check.assert_not_called()
        self.assertFalse((self.root / REPORT).exists())

    def test_all_empty_mappings_can_be_reviewed(self):
        self.write_html(('data-formal=""', 'data-formal=""'))
        self.review_entry('accept')
        self.assertEqual(json.loads(self.metadata_path.read_text())[
                         'status'], 'final')

    def test_invalid_entries_cannot_be_accepted(self):
        before = self.metadata_path.read_bytes()
        for entry_id in ('missing', '../first'):
            with self.subTest(entry_id=entry_id), self.assertRaisesRegex(CommandError, 'Unknown entry'):
                self.review_entry('accept', entry=entry_id)
        for source in ('<section', self.html.read_text().replace('ready pending', 'missing')):
            self.html.write_text(source)
            with self.subTest(source=source), self.assertRaises(CommandError):
                self.review_entry('accept')
            self.assertEqual(self.metadata_path.read_bytes(), before)
        self.write_html()
        metadata = json.loads(before)
        metadata['status'] = 'published'
        self.metadata_path.write_text(json.dumps(metadata))
        with self.assertRaisesRegex(CommandError, 'status must be draft or final'):
            call_command('validate_corpus', stdout=StringIO())

    def test_retraction_allows_unplanned_or_broken_content(self):
        for source in ('<section', '<section id="unplanned" data-kind="definition"><p>A claim.</p></section>'):
            with self.subTest(source=source):
                self.write_html()
                self.review_entry('accept')
                self.html.write_text(source)
                self.review_entry('retract')
                self.assertEqual(json.loads(self.metadata_path.read_text())[
                                 'status'], 'draft')

    def test_concurrent_edits_are_not_overwritten_or_approved(self):
        dump = json.dump
        for path in (self.metadata_path, self.html, self.html.parent / 'assets/diagram.svg',
                     self.node_dir / 'pending.json'):
            with self.subTest(path=path):
                before = self.metadata_path.read_bytes()
                original = path.read_bytes()
                files = set(self.html.parent.iterdir())

                def edit_during_staging(*args, **kwargs):
                    path.write_bytes(original + b'\n')
                    return dump(*args, **kwargs)

                with patch('catalog.files.json.dump', side_effect=edit_during_staging):
                    with self.assertRaisesRegex(CommandError, 'Entry review inputs changed'):
                        self.review_entry('accept')
                expected = before + b'\n' if path == self.metadata_path else before
                self.assertEqual(self.metadata_path.read_bytes(), expected)
                self.assertEqual(set(self.html.parent.iterdir()), files)
                path.write_bytes(original)

    def test_failed_staging_preserves_metadata_and_cleans_up(self):
        before = self.metadata_path.read_bytes()
        files = set(self.html.parent.iterdir())
        with patch('catalog.files.json.dump', side_effect=OSError('Cannot stage review')):
            with self.assertRaisesRegex(CommandError, 'Cannot stage review'):
                self.review_entry('accept')
        self.assertEqual(self.metadata_path.read_bytes(), before)
        self.assertEqual(set(self.html.parent.iterdir()), files)
