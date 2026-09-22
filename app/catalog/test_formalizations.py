"""Node storage, derived progress, source navigation, and verification boundaries."""

from io import StringIO
import json
import os
from pathlib import Path
import shutil
from subprocess import CompletedProcess
from tempfile import TemporaryDirectory
from unittest.mock import patch

from django.conf import settings
from django.core.management import call_command
from django.core.management.base import CommandError
from django.test import SimpleTestCase, override_settings

from catalog.content import entries, load_catalog
from catalog.sources import ContentError
from catalog.testing import CorpusFixtureMixin
from formalization.lean import pinned_lean_version, verification_inputs
from formalization.nodes import ENVIRONMENT, REPORT, REPORT_VERSION, file_hash, load_nodes, node_fingerprint
from formalization.reviews import declaration_hashes, review_target_hash


class EmptyRegistryTests(SimpleTestCase):
    def test_empty_registry_needs_no_lean(self):
        output = StringIO()
        with TemporaryDirectory() as directory, override_settings(REPOSITORY_DIR=Path(directory)):
            with patch('catalog.management.commands.check_formalizations.subprocess.run') as lean:
                call_command('check_formalizations', stdout=output)
            self.assertEqual(self.client.get(
                '/api/formal/nodes/').json(), {'nodes': []})
        lean.assert_not_called()
        self.assertIn('No formal node declarations to check.',
                      output.getvalue())


class NodeFixtureMixin(CorpusFixtureMixin):
    entry_sources = {'first': ''}

    def setUp(self):
        repository = settings.REPOSITORY_DIR
        super().setUp()
        self.formal = self.root / 'formal'
        self.node_dir = self.formal / 'nodes'
        self.node_dir.mkdir(parents=True)
        for name in ('lean-toolchain', 'lake-manifest.json', 'lakefile.toml'):
            shutil.copyfile(repository / 'formal' / name, self.formal / name)
        self.source = self.formal / 'Lemmatheca/Fixture.lean'
        self.source.parent.mkdir()
        self.source.write_text('-- <script>alert("source")</script>\nnamespace Lemmatheca\n'
                               'theorem ready : True := by trivial\n'
                               'theorem unfinished : True := by sorry\n'
                               'theorem dependent : True := unfinished\nend Lemmatheca\n')
        self.html = self.root / 'corpus/entries/first/entry.html'
        self.write_node('ready', declaration='Lemmatheca.ready')
        self.write_node('pending', declaration='Lemmatheca.unfinished')
        self.write_node(
            'dependent', declaration='Lemmatheca.dependent', dependencies=['pending'])
        self.write_html()
        self.write_report()

    def target_hash(self, node):
        name = node['declaration']
        snapshots = {name: {'payload': [name], 'references': []}}
        return review_target_hash(node_fingerprint(node), declaration_hashes(snapshots, [name])[name],
                                  {name: file_hash(self.formal / name) for name in ENVIRONMENT})

    def write_node(self, node_id, *, accepted=True, **changes):
        data = {'id': node_id, 'description': 'The proposition True holds.',
                'declaration': 'Lemmatheca.ready', 'module': 'Lemmatheca.Fixture',
                'dependencies': [], 'review': None, **changes}
        if accepted and 'review' not in changes:
            data['review'] = {'sha256': self.target_hash(
                data), 'recorded_at': '2026-09-20T12:00:00+00:00'}
        (self.node_dir / f'{node_id}.json').write_text(json.dumps(data))

    def write_html(self, attributes=('data-formal="ready pending"', 'data-formal=""')):
        self.html.write_text('\n'.join(
            f'<section id="block-{i}" data-kind="question" {attribute}>'
            f'<h2>Block {i}</h2><p>A mathematical claim.</p>'
            '<details class="question-answer"><summary>Answer</summary><p>Explanation.</p></details></section>'
            for i, attribute in enumerate(attributes)))

    def write_report(self):
        nodes = load_nodes(self.root, check_reports=False)
        paths = verification_inputs(self.root, nodes)
        report = {'format_version': REPORT_VERSION, 'build': 'passed', 'checked_on': '2026-09-20T12:00:00+00:00',
                  'sha256': {path.relative_to(self.root).as_posix(): file_hash(path) for path in paths},
                  'nodes': {key: {'fingerprint': node_fingerprint(node),
                                  'target_sha256': self.target_hash(node),
                                  'status': 'complete' if key == 'ready' else 'pending',
                                  'axioms': [] if key == 'ready' else ['sorryAx']}
                            for key, node in nodes.items()}}
        path = self.root / REPORT
        path.parent.mkdir(exist_ok=True)
        path.write_text(json.dumps(report))


class NodeTests(NodeFixtureMixin, SimpleTestCase):
    def test_attribute_states_and_concise_header_progress(self):
        self.write_html(('data-formal="ready pending"', 'data-formal=""', ''))
        response = self.client.get('/entries/first/')
        blocks = response.context['entry']['blocks']
        self.assertEqual([item['formalization']['status'] for item in blocks],
                         ['partial', 'not_applicable', 'not_started'])
        self.assertEqual(blocks[0]['formalization']['label'], '50%')
        self.assertEqual(
            response.context['entry']['formalization']['unplanned'], 1)
        self.assertEqual(
            response.context['entry']['formalization']['label'], 'Partial')
        self.assertNotIn('percent', response.context['entry']['formalization'])
        self.assertContains(response, 'Formalization: Partial', count=1)
        self.assertContains(response, 'class="formal-nodes"', count=1)
        self.assertContains(response, '50%')
        self.assertContains(response, '◷')
        self.assertContains(response, '✓')
        self.assertNotContains(response, 'class="formal-nodes" open')
        text = response.content.decode()
        title_start = text.index('id="block-0-title"')
        self.assertLess(text.index('class="formal-nodes"'), title_start)
        self.assertContains(response, 'href="/formal/nodes/ready/"')

    def test_shared_nodes_are_counted_once_and_unknown_coverage_prevents_complete(self):
        self.write_html(('data-formal="ready"', 'data-formal="ready"', ''))
        progress = entries()['first']['formalization']
        self.assertEqual((progress['complete'], progress['total']), (1, 1))
        self.assertEqual(progress['status'], 'partial')
        self.assertEqual(progress['label'], 'Partial')
        self.write_html(
            ('data-formal="ready"', 'data-formal="ready"', 'data-formal=""'))
        self.assertEqual(entries()['first']
                         ['formalization']['status'], 'complete')
        self.assertEqual(entries()['first']
                         ['formalization']['label'], 'Complete')
        self.write_html(('',))
        self.assertEqual(entries()['first']
                         ['formalization']['label'], 'Not started')
        self.write_html(('data-formal=""',))
        self.assertEqual(
            entries()['first']['formalization']['status'], 'not_applicable')

    def test_mapping_validation_and_html_references_without_json_records(self):
        for attr in ('data-formal="unknown"', 'data-formal="ready ready"',
                     'data-formal="../ready"', 'data-formal', 'data-formal="" data-formal="ready"'):
            with self.subTest(attr=attr):
                self.write_html((attr,))
                with self.assertRaises(ContentError):
                    load_catalog(self.root / 'corpus', self.root)
        self.write_html(('data-formal="ready"', ''))
        self.html.write_text(self.html.read_text().replace(
            'A mathematical claim.', '<a href="#block-1">See the answer</a>', 1))
        response = self.client.get('/entries/first/')
        self.assertContains(response, '?from=first&amp;at=block-0#block-1')

    def test_node_page_escapes_source_and_infers_line(self):
        response = self.client.get('/formal/nodes/ready/')
        self.assertContains(response, 'Lemmatheca.ready')
        self.assertContains(response, '&lt;script&gt;')
        self.assertNotContains(response, '<script>alert')
        self.assertContains(response, 'href="#L3"')
        self.assertContains(
            response, 'class="source-line declaration-line" id="L3"')
        self.assertEqual(response.context['declaration_line'], 3)

    def test_description_is_escaped_math_ready_and_available_in_api(self):
        description = r'For \(x < y\), <script>alert("description")</script> is text.'
        self.write_node('ready', description=description)
        response = self.client.get('/formal/nodes/ready/')
        self.assertContains(response, r'For \(x &lt; y\)')
        self.assertContains(
            response, '&lt;script&gt;alert(&quot;description&quot;)&lt;/script&gt;')
        self.assertNotContains(response, '<script>alert("description")')
        self.assertContains(response, 'class="node-description" data-math')
        self.assertContains(response, '/static/vendor/katex/katex.min.js')
        self.assertContains(response, '/static/js/formal-node.js')
        text = response.content.decode()
        self.assertLess(text.index('class="node-description"'),
                        text.index('id="declaration-title"'))
        self.assertContains(
            response, '<details class="node-source-browser" id="source-browser">')
        self.assertEqual(self.client.get(
            '/api/formal/nodes/ready/').json()['description'], description)
        listed = self.client.get('/api/formal/nodes/').json()['nodes']
        self.assertEqual(next(node for node in listed if node['id'] == 'ready')[
                         'description'], description)

    def test_description_edits_preserve_review_and_current_lean_evidence(self):
        before = load_nodes(self.root)['ready']
        report = (self.root / REPORT).read_bytes()
        path = self.node_dir / 'ready.json'
        record = json.loads(path.read_text())
        record['description'] = 'An updated human description.'
        path.write_text(json.dumps(record))
        with patch('subprocess.run') as lean:
            updated = self.client.get('/api/formal/nodes/ready/').json()
            page = self.client.get('/formal/nodes/ready/')
        lean.assert_not_called()
        self.assertContains(page, record['description'])
        for key in ('review', 'review_current', 'target_sha256', 'checked_on', 'status'):
            self.assertEqual(updated[key], before[key])
        self.assertEqual(updated['status'], 'complete')
        self.assertEqual((self.root / REPORT).read_bytes(), report)

    def test_description_is_required_and_nonempty(self):
        for value in (None, '', ' \n ', 3, [], {}):
            with self.subTest(value=value):
                self.write_node('ready', description=value)
                with self.assertRaisesRegex(ContentError, 'description must be nonempty text'):
                    load_nodes(self.root)
        path = self.node_dir / 'ready.json'
        record = json.loads(path.read_text())
        del record['description']
        path.write_text(json.dumps(record))
        with self.assertRaisesRegex(ContentError, 'Expected fields:.*description'):
            load_nodes(self.root)

    def test_proof_dependencies_show_links_and_statuses_without_descriptions(self):
        description = r'A prerequisite involving \(A\subseteq B\).'
        self.write_node(
            'pending', declaration='Lemmatheca.unfinished', description=description)
        response = self.client.get('/formal/nodes/dependent/')
        self.assertContains(response, 'Dependencies')
        self.assertContains(response, 'href="/formal/nodes/pending/"')
        self.assertContains(
            response, 'class="node-status formalization-proof_pending"')
        self.assertNotContains(response, description)
        self.assertContains(self.client.get(
            '/formal/nodes/pending/'), description)

    def test_anonymous_instance_uses_current_checked_location(self):
        self.source.write_text('namespace Lemmatheca\n'
                               'instance : EmptyCollection (Set α) := ⟨fun _ => False⟩\n'
                               'end Lemmatheca\n')
        self.write_node('ready', declaration='Lemmatheca.instEmptyCollection')
        self.write_report()
        path = self.root / REPORT
        report = json.loads(path.read_text())
        report['nodes']['ready']['location'] = {
            'module': 'Lemmatheca.Fixture', 'line': 2}
        path.write_text(json.dumps(report))
        with patch('subprocess.run') as lean:
            response = self.client.get('/formal/nodes/ready/')
        lean.assert_not_called()
        self.assertEqual(response.context['declaration_line'], 2)
        self.assertContains(response, 'href="#L2"')
        self.assertContains(
            response, 'class="source-line declaration-line" id="L2"')
        self.assertEqual(self.client.get(
            '/api/formal/nodes/ready/').json()['declaration_line'], 2)

        for location in (None, {'module': 'Mathlib.Other', 'line': 2},
                         {'module': 'Lemmatheca.Fixture', 'line': True},
                         {'module': 'Lemmatheca.Fixture', 'line': 0},
                         {'module': 'Lemmatheca.Fixture', 'line': 99}):
            with self.subTest(location=location):
                report['nodes']['ready']['location'] = location
                path.write_text(json.dumps(report))
                response = self.client.get('/formal/nodes/ready/')
                self.assertIsNone(response.context['declaration_line'])

        report['nodes']['ready']['location'] = {
            'module': 'Lemmatheca.Fixture', 'line': 2}
        path.write_text(json.dumps(report))
        self.source.write_text('\n' + self.source.read_text())
        response = self.client.get('/formal/nodes/ready/')
        self.assertIsNone(response.context['declaration_line'])

    def test_generated_declaration_shows_its_signature_above_the_source_origin(self):
        mathlib = self.formal / '.lake/packages/mathlib/Mathlib/Test.lean'
        mathlib.parent.mkdir(parents=True)
        original = ('@[to_additive]\n'
                    'lemma IsSquare.one [MulOneClass α] : IsSquare (1 : α) := by simp\n')
        mathlib.write_text(original)
        self.write_node('ready', module='Mathlib.Test',
                        declaration='Even.zero', accepted=False)
        self.write_report()
        path = self.root / REPORT
        report = json.loads(path.read_text())
        signature = 'Even.zero.{u} {α : Type u} [AddZeroClass α] :\n  Even (0 : α)'
        report['nodes']['ready'].update(
            signature=signature, location={'module': 'Mathlib.Test', 'line': 1})
        path.write_text(json.dumps(report))
        node_before = (self.node_dir / 'ready.json').read_bytes()
        report_before = path.read_bytes()

        with patch('subprocess.run') as lean:
            response = self.client.get('/formal/nodes/ready/')
            self.assertContains(response, signature)
            self.assertContains(
                response, 'aria-label="Checked Lean declaration"')
            self.assertContains(response, 'Source origin:')
            self.assertContains(response, 'IsSquare.one')
            self.assertContains(response, 'href="#L1"')
            self.assertLess(response.content.decode().index(signature),
                            response.content.decode().index('IsSquare.one'))
            node = self.client.get('/api/formal/nodes/ready/').json()
            self.assertEqual(node['signature'], signature)
            self.assertEqual(node['status'], 'review_pending')

            # Web-only deployments can still show the generated declaration.
            mathlib.unlink()
            response = self.client.get('/formal/nodes/ready/')
            self.assertContains(response, signature)
            self.assertContains(response, '/Mathlib/Test.lean#L1')

            # Stale evidence must not display a previously checked statement.
            mathlib.write_text('-- changed\n' + original)
            response = self.client.get('/formal/nodes/ready/')
            self.assertNotContains(response, signature)
            self.assertIsNone(response.context['node']['signature'])
        lean.assert_not_called()
        self.assertEqual(
            (self.node_dir / 'ready.json').read_bytes(), node_before)
        self.assertEqual(path.read_bytes(), report_before)

    def test_api_is_independent_of_corpus_and_read_only(self):
        self.html.unlink()
        response = self.client.get('/api/formal/nodes/ready/')
        self.assertEqual(response.json()['status'], 'complete')
        self.assertEqual(
            len(self.client.get('/api/formal/nodes/').json()['nodes']), 3)
        for url in ('/api/formal/nodes/', '/api/formal/nodes/ready/', '/formal/nodes/ready/'):
            self.assertEqual(self.client.post(url).status_code, 405)
            self.assertEqual(self.client.head(url).status_code, 200)
        for url in ('/api/formal/nodes/absent/', '/formal/nodes/absent/'):
            self.assertEqual(self.client.get(url).status_code, 404)

    def test_node_statuses_identify_the_next_step_in_api_and_badge(self):
        self.write_node('unwritten', declaration=None,
                        module=None, accepted=False)
        self.write_node('review', accepted=False)
        self.write_node('unchecked')
        cases = (
            ('unwritten', 'declaration_missing', 'Declaration missing'),
            ('review', 'review_pending', 'Pending review'),
            ('unchecked', 'verification_needed', 'Verification needed'),
            ('pending', 'proof_pending', 'Proof pending'),
            ('ready', 'complete', 'Complete'),
        )
        for node_id, status, label in cases:
            with self.subTest(node=node_id):
                node = self.client.get(f'/api/formal/nodes/{node_id}/').json()
                self.assertEqual(
                    (node['status'], node['status_label']), (status, label))
                self.assertNotIn('reason', node)
                page = self.client.get(f'/formal/nodes/{node_id}/')
                self.assertContains(
                    page, f'class="formalization-badge formalization-{status}"')
                self.assertContains(page, label, count=1)
        self.write_node('ready', dependencies=['pending'])
        self.write_report()
        self.assertEqual(self.client.get(
            '/api/formal/nodes/ready/').json()['status'], 'dependencies_pending')
        self.assertContains(self.client.get(
            '/formal/nodes/ready/'), 'Dependencies pending', count=1)
        response = self.client.get('/entries/first/')
        self.assertContains(response, 'Dependencies pending')
        self.assertContains(response, 'Proof pending')
        self.assertEqual(
            response.context['entry']['blocks'][0]['formalization']['percent'], 0)

    def test_review_and_verification_labels_are_independent(self):
        outdated = {'sha256': 'a' * 64, 'recorded_at': '2026-09-20T12:00:00+00:00'}
        cases = (
            ('ready', {}, True, True),
            ('pending', None, True, False),
            ('ready', {'accepted': False}, False, True),
            ('ready', {'review': outdated}, False, True),
            ('unchecked', {}, False, False),
            ('unwritten', {'declaration': None, 'module': None, 'accepted': False}, False, False),
        )
        for node_id, changes, accepted, verified in cases:
            with self.subTest(node=node_id, accepted=accepted, verified=verified):
                if changes is not None:
                    self.write_node(node_id, **changes)
                response = self.client.get(f'/formal/nodes/{node_id}/')
                self.assertEqual(response.context['node']['review_current'], accepted)
                self.assertEqual(response.context['node']['verification_complete'], verified)
                self.assertContains(response, 'Reviewed on <time' if accepted else 'Under review')
                self.assertNotContains(response, 'Under review' if accepted else 'Reviewed on')
                self.assertContains(response, 'Verified on <time' if verified else 'Not verified')
                self.assertNotContains(response, 'Not verified' if verified else 'Verified on')
                if accepted or verified:
                    self.assertContains(response,
                                        '<time datetime="2026-09-20T12:00:00+00:00">2026-09-20</time>',
                                        html=True)
                self.assertEqual(self.client.get(f'/api/formal/nodes/{node_id}/').json()[
                    'verification_complete'], verified)

    def test_stale_evidence_hides_review_and_verification_dates(self):
        self.source.write_text(self.source.read_text() + '\n-- Source changed after verification.\n')
        response = self.client.get('/formal/nodes/ready/')
        self.assertContains(response, 'Under review')
        self.assertContains(response, 'Not verified')
        self.assertNotContains(response, '<time')
        self.assertFalse(response.context['node']['verification_complete'])

    def test_forged_status_cycles_and_unknown_dependencies_are_rejected(self):
        for changes in ({'status': 'complete'}, {'review': True}, {'declaration': 'bad name'},
                        {'review': {'sha256': 'bad',
                                    'recorded_at': '2026-09-20T12:00:00+00:00'}},
                        {'review': {'sha256': 'a' * 64, 'recorded_at': '2026-09-20'}},
                        {'module': '../secret'}, {'dependencies': ['missing']},
                        {'dependencies': ['ready']}, {'dependencies': ['pending', 'pending']}):
            with self.subTest(changes=changes):
                self.write_node('ready', **changes)
                with self.assertRaises(ContentError):
                    load_nodes(self.root)
        self.write_node('ready', dependencies=['dependent'])
        self.write_node('pending', dependencies=['ready'])
        with self.assertRaisesRegex(ContentError, 'cycle'):
            load_nodes(self.root)

    def test_incomplete_or_inconsistent_evidence_cannot_complete_a_node(self):
        path = self.root / REPORT
        report = json.loads(path.read_text())
        checked = report['nodes']['ready']
        for evidence in (None, {}, {**checked, 'target_sha256': None},
                         {**checked, 'axioms': 'propext'}, {**
                                                            checked, 'axioms': [None]},
                         {**checked, 'axioms': ['untrustedAxiom']},
                         {**checked, 'axioms': ['sorryAx']}):
            with self.subTest(evidence=evidence):
                report['nodes']['ready'] = evidence
                path.write_text(json.dumps(report))
                node = load_nodes(self.root)['ready']
                self.assertEqual(node['status'], 'verification_needed')
                self.assertIsNone(node['target_sha256'])
                self.assertFalse(node['review_current'])
                self.assertFalse(node['verification_complete'])

    def test_review_record_updates_progress_without_invalidating_lean_evidence(self):
        report = (self.root / REPORT).read_bytes()
        for accepted, percent, label in ((False, 0, 'Pending review'), (True, 50, 'Complete'),
                                         (False, 0, 'Pending review')):
            with self.subTest(accepted=accepted):
                self.write_node('ready', accepted=accepted)
                node = self.client.get('/api/formal/nodes/ready/').json()
                self.assertEqual(node['status_label'], label)
                self.assertEqual(
                    node['status'], 'complete' if accepted else 'review_pending')
                self.assertIsNotNone(node['checked_on'])
                response = self.client.get('/entries/first/')
                self.assertEqual(
                    response.context['entry']['blocks'][0]['formalization']['percent'], percent)
                self.assertEqual(
                    response.context['entry']['formalization']['label'], 'Partial')
                self.assertContains(response, label)
                self.assertEqual((self.root / REPORT).read_bytes(), report)
        self.assertEqual(self.client.get(
            '/api/formal/nodes/pending/').json()['status_label'], 'Proof pending')
        self.assertEqual(self.client.get(
            '/api/formal/nodes/pending/').json()['status'], 'proof_pending')

    def test_stale_sources_environment_metadata_and_reports_invalidate_cached_progress(self):
        self.write_html(('data-formal="ready"',))
        for path in (self.source, self.formal / 'lean-toolchain', self.node_dir / 'ready.json', self.root / REPORT):
            with self.subTest(path=path.name):
                original = path.read_text()
                self.assertEqual(
                    entries()['first']['formalization']['status'], 'complete')
                if path.name == 'ready.json':
                    data = json.loads(original)
                    data['declaration'] = 'Lemmatheca.unfinished'
                    path.write_text(json.dumps(data))
                elif path.name == 'nodes.json':
                    data = json.loads(original)
                    data['nodes']['ready']['axioms'] = ['sorryAx']
                    path.write_text(json.dumps(data))
                else:
                    path.write_text(original + '\n')
                self.assertEqual(
                    entries()['first']['formalization']['status'], 'partial')
                path.write_text(original)
        self.write_node('ready', dependencies=['pending'])
        self.write_report()
        self.assertEqual(load_nodes(self.root)[
                         'ready']['status'], 'dependencies_pending')

    def test_missing_mathlib_checkout_uses_pinned_source_and_installed_edits_invalidate(self):
        mathlib = self.formal / '.lake/packages/mathlib/Mathlib/Test.lean'
        mathlib.parent.mkdir(parents=True)
        mathlib.write_text(
            'namespace Mathlib\ntheorem test : True := by trivial\nend Mathlib\n')
        self.write_node('ready', module='Mathlib.Test',
                        declaration='Mathlib.test')
        self.write_report()
        path = self.root / REPORT
        report = json.loads(path.read_text())
        report['nodes']['ready']['location'] = {
            'module': 'Mathlib.Test', 'line': 2}
        path.write_text(json.dumps(report))
        mathlib.unlink()
        self.assertEqual(load_nodes(self.root)['ready']['status'], 'complete')
        response = self.client.get('/formal/nodes/ready/')
        self.assertContains(response, 'This mathlib source is not installed')
        self.assertContains(
            response, 'github.com/leanprover-community/mathlib4/blob/')
        self.assertContains(response, '/Mathlib/Test.lean#L2')
        self.assertNotContains(response, 'href="#L2"')
        mathlib.write_text('-- Changed\n')
        self.assertEqual(load_nodes(self.root)[
                         'ready']['status'], 'verification_needed')

    def test_imported_lean_declaration_uses_its_actual_source_and_pinned_fallback(self):
        mathlib = self.formal / '.lake/packages/mathlib/Mathlib/Test.lean'
        mathlib.parent.mkdir(parents=True)
        mathlib.write_text('public import Init.Data.Function\n')
        self.write_node('ready', module='Mathlib.Test',
                        declaration='Function.Injective')
        self.write_report()
        report_path = self.root / REPORT
        report = json.loads(report_path.read_text())
        report['nodes']['ready']['location'] = {
            'module': 'Init.Data.Function', 'line': 2}
        report_path.write_text(json.dumps(report))
        review_before = (self.node_dir / 'ready.json').read_bytes()
        report_before = report_path.read_bytes()

        version = pinned_lean_version(self.root)
        elan = self.root / 'elan'
        source = elan / \
            f'toolchains/leanprover--lean4---{version}/src/lean/Init/Data/Function.lean'
        source.parent.mkdir(parents=True)
        source.write_text('namespace Function\ndef Injective (f : α → β) : Prop :=\n'
                          '  ∀ ⦃a₁ a₂⦄, f a₁ = f a₂ → a₁ = a₂\nend Function\n')
        upstream = f'https://github.com/leanprover/lean4/blob/{version}/src/Init/Data/Function.lean#L2'
        with patch.dict(os.environ, {'ELAN_HOME': str(elan)}), patch('subprocess.run') as lean:
            response = self.client.get('/formal/nodes/ready/')
            self.assertContains(response, 'Init/Data/Function.lean')
            self.assertContains(response, 'href="#L2"')
            self.assertContains(
                response, 'class="source-line declaration-line" id="L2"')
            self.assertContains(response, 'Pinned Lean source')
            self.assertContains(response, upstream)
            node = self.client.get('/api/formal/nodes/ready/').json()
            self.assertEqual(node['module'], 'Mathlib.Test')
            self.assertEqual(node['source'], 'Init/Data/Function.lean')
            self.assertEqual(node['declaration_line'], 2)
            self.assertEqual(node['status'], 'complete')

            source.unlink()
            response = self.client.get('/formal/nodes/ready/')
            self.assertContains(response, 'This Lean source is not installed')
            self.assertContains(
                response, f'<a href="{upstream}">line 2</a>', html=True)
            self.assertNotContains(response, 'href="#L2"')
            self.assertEqual(load_nodes(self.root)[
                             'ready']['status'], 'complete')

            mathlib.write_text('-- changed\n' + mathlib.read_text())
            node = self.client.get('/api/formal/nodes/ready/').json()
            self.assertEqual(node['status'], 'verification_needed')
            self.assertEqual(node['source'], 'Mathlib/Test.lean')
            self.assertIsNone(node['declaration_line'])
            self.assertNotContains(self.client.get(
                '/formal/nodes/ready/'), upstream)
        lean.assert_not_called()
        self.assertEqual(
            (self.node_dir / 'ready.json').read_bytes(), review_before)
        self.assertEqual(report_path.read_bytes(), report_before)

    def test_reexported_mathlib_declaration_uses_a_fingerprinted_source(self):
        mathlib = self.formal / '.lake/packages/mathlib/Mathlib'
        mathlib.mkdir(parents=True)
        (mathlib / 'Import.lean').write_text('public import Mathlib.Definition\n')
        (mathlib / 'Definition.lean').write_text(
            'namespace Function\ndef test : Prop := True\nend Function\n')
        self.write_node('ready', module='Mathlib.Import',
                        declaration='Function.test')
        self.write_report()
        path = self.root / REPORT
        report = json.loads(path.read_text())
        report['nodes']['ready']['location'] = {
            'module': 'Mathlib.Definition', 'line': 2}
        path.write_text(json.dumps(report))
        response = self.client.get('/formal/nodes/ready/')
        self.assertContains(response, 'Mathlib/Definition.lean')
        self.assertContains(response, 'href="#L2"')
        self.assertNotContains(response, 'Mathlib/Import.lean')
        self.assertEqual(response.context['node']['status'], 'complete')

    def test_import_closure_includes_public_meta_and_all_imports_but_not_comments(self):
        external = self.formal / '.lake/packages/mathlib/Mathlib'
        external.mkdir(parents=True)
        (external / 'A.lean').write_text('public meta import all Mathlib.B\n')
        (external / 'B.lean').write_text('-- import Missing\nimport all Init.Control.Option\n')
        self.source.write_text(
            'public import Mathlib.A\n' + self.source.read_text())
        self.write_report()
        self.assertEqual(load_nodes(self.root)['ready']['status'], 'complete')
        report = json.loads((self.root / REPORT).read_text())
        self.assertIn(
            'formal/.lake/packages/mathlib/Mathlib/B.lean', report['sha256'])
        (external / 'B.lean').write_text('-- changed\n')
        self.assertEqual(load_nodes(self.root)[
                         'ready']['status'], 'verification_needed')


class FormalizationCommandTests(NodeFixtureMixin, SimpleTestCase):
    def run_check(self, axiom='sorryAx', side_effect=None, *, include_signatures=True):
        output = ("'Lemmatheca.ready' does not depend on any axioms\n"
                  f"'Lemmatheca.unfinished' depends on axioms: [{axiom}]\n"
                  f"'Lemmatheca.dependent' depends on axioms: [{axiom}]\n"
                  'NODE_LOCATION Lemmatheca.ready Lemmatheca.Fixture 3\n')
        for name in ('Lemmatheca.ready', 'Lemmatheca.unfinished', 'Lemmatheca.dependent'):
            if include_signatures:
                output += 'NODE_SIGNATURE ' + json.dumps(
                    {'name': name, 'signature': f'{name} : True'}) + '\n'
            output += 'REVIEW_CONSTANT ' + json.dumps(
                {'name': name, 'payload': [name], 'references': []}) + '\n'
        result = CompletedProcess([], 0, stdout=output, stderr='')

        def execute(*args, **kwargs):
            if side_effect:
                side_effect()
            return result
        with patch('catalog.management.commands.check_formalizations.subprocess.run', side_effect=execute):
            call_command('check_formalizations', stdout=StringIO())

    def test_transitive_sorry_is_recorded_as_pending_never_complete(self):
        self.run_check()
        report = json.loads((self.root / REPORT).read_text())
        self.assertEqual(report['nodes']['ready']['status'], 'complete')
        self.assertEqual(report['nodes']['dependent']['status'], 'pending')
        self.assertEqual(report['nodes']['pending']['axioms'], ['sorryAx'])
        self.assertEqual(report['nodes']['ready']['location'],
                         {'module': 'Lemmatheca.Fixture', 'line': 3})
        self.assertEqual(report['nodes']['ready']
                         ['signature'], 'Lemmatheca.ready : True')
        self.assertNotIn('location', report['nodes']['pending'])
        self.assertEqual(load_nodes(self.root)[
                         'dependent']['status'], 'proof_pending')

    def test_missing_signature_cannot_replace_verification_report(self):
        path = self.root / REPORT
        original = path.read_bytes()
        with self.assertRaisesRegex(CommandError, 'No declaration signature'):
            self.run_check(include_signatures=False)
        self.assertEqual(path.read_bytes(), original)

    def test_custom_axiom_and_mid_run_source_changes_cannot_write_passing_report(self):
        original = (self.root / REPORT).read_text()
        with self.assertRaisesRegex(CommandError, 'unapproved axioms'):
            self.run_check('untrustedAxiom')
        self.assertEqual((self.root / REPORT).read_text(), original)
        with self.assertRaisesRegex(CommandError, 'changed during verification'):
            self.run_check(side_effect=lambda: self.source.write_text(
                self.source.read_text() + '\n'))
        self.assertEqual((self.root / REPORT).read_text(), original)
        self.assertEqual(load_nodes(self.root)[
                         'ready']['status'], 'verification_needed')

    def test_failed_report_replacement_preserves_evidence_and_cleans_staged_json(self):
        path = self.root / REPORT
        original = path.read_bytes()
        with patch.object(Path, 'replace', side_effect=OSError('Cannot replace report')):
            with self.assertRaisesRegex(CommandError, 'Cannot replace report'):
                self.run_check()
        self.assertEqual(path.read_bytes(), original)
        self.assertEqual(set(path.parent.iterdir()), {path})
