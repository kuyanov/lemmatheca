"""Node storage, derived progress, source navigation, and verification boundaries."""

from io import StringIO
import json
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
from formalization.lean import declaration_line, verification_inputs
from formalization.nodes import REPORT, REPORT_VERSION, file_hash, load_nodes, node_fingerprint


class ActiveFormalizationTests(SimpleTestCase):
    def test_empty_registry_needs_no_lean(self):
        output = StringIO()
        with TemporaryDirectory() as directory, override_settings(REPOSITORY_DIR=Path(directory)):
            with patch('catalog.management.commands.check_formalizations.subprocess.run') as lean:
                call_command('check_formalizations', stdout=output)
            self.assertEqual(self.client.get('/api/formal/nodes/').json(), {'nodes': []})
        lean.assert_not_called()
        self.assertIn('No formal node declarations to check.', output.getvalue())

    def test_definition_one_nodes_display_with_sources_and_current_status(self):
        entry = entries()['sets-and-maps']
        first, *others = entry['blocks']
        self.assertEqual(first['id'], 'sets-and-elements')
        self.assertEqual(len(first['formal_ids']), 9)
        self.assertEqual(entry['formalization']['unplanned'], 20)
        self.assertEqual(entry['formalization']['label'], 'Partial')
        self.assertNotIn('percent', entry['formalization'])
        self.assertTrue(all(block['formal_ids'] is None for block in others))
        response = self.client.get('/entries/sets-and-maps/')
        self.assertNotContains(response, 'verification-note')
        self.assertContains(response, 'class="formal-nodes"', count=1)
        self.assertContains(response, 'class="block-title"', count=21)
        nodes = self.client.get('/api/formal/nodes/').json()['nodes']
        self.assertEqual({node['id'] for node in nodes}, set(first['formal_ids']))
        self.assertEqual(first['formalization']['complete'], sum(node['status'] == 'complete' for node in nodes))
        for node in nodes:
            with self.subTest(node=node['id']):
                url = f"/formal/nodes/{node['id']}/"
                self.assertContains(response, f'href="{url}"')
                page = self.client.get(url)
                self.assertContains(page, node['status_label'])
                self.assertNotIn('reason', node)
                self.assertNotContains(page, 'href="/lean/')
                if page.context['lean_source'] is not None:
                    self.assertIsNotNone(page.context['declaration_line'])


class NodeFixtureMixin:
    def setUp(self):
        super().setUp()
        temporary = TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.formal = self.root / 'formal'
        self.node_dir = self.formal / 'nodes'
        self.node_dir.mkdir(parents=True)
        shutil.copytree(settings.CORPUS_DIR / 'entries', self.root / 'corpus/entries')
        for name in ('taxonomy.json', 'reading-order.json'):
            shutil.copyfile(settings.CORPUS_DIR / name, self.root / 'corpus' / name)
        for name in ('lean-toolchain', 'lake-manifest.json', 'lakefile.toml'):
            shutil.copyfile(settings.REPOSITORY_DIR / 'formal' / name, self.formal / name)
        self.source = self.formal / 'Lemmatheca/Fixture.lean'
        self.source.parent.mkdir()
        self.source.write_text('-- <script>alert("source")</script>\nnamespace Lemmatheca\n'
                               'theorem ready : True := by trivial\n'
                               'theorem unfinished : True := by sorry\n'
                               'theorem dependent : True := unfinished\nend Lemmatheca\n')
        self.html = self.root / 'corpus/entries/sets-and-maps/entry.html'
        self.write_node('ready', declaration='Lemmatheca.ready')
        self.write_node('pending', declaration='Lemmatheca.unfinished')
        self.write_node('dependent', declaration='Lemmatheca.dependent', dependencies=['pending'])
        self.write_html()
        configured = override_settings(REPOSITORY_DIR=self.root, CORPUS_DIR=self.root / 'corpus')
        configured.enable()
        self.addCleanup(configured.disable)
        self.write_report()

    def write_node(self, node_id, **changes):
        data = {'id': node_id, 'declaration': 'Lemmatheca.ready', 'module': 'Lemmatheca.Fixture',
                'dependencies': [], 'reviewed': True, **changes}
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
                                  'status': 'complete' if key == 'ready' else 'pending',
                                  'axioms': [] if key == 'ready' else ['sorryAx']}
                            for key, node in nodes.items()}}
        path = self.root / REPORT
        path.parent.mkdir(exist_ok=True)
        path.write_text(json.dumps(report))


class NodeTests(NodeFixtureMixin, SimpleTestCase):
    def test_attribute_states_and_concise_header_progress(self):
        self.write_html(('data-formal="ready pending"', 'data-formal=""', ''))
        response = self.client.get('/entries/sets-and-maps/')
        blocks = response.context['entry']['blocks']
        self.assertEqual([item['formalization']['status'] for item in blocks],
                         ['partial', 'not_applicable', 'not_started'])
        self.assertEqual(blocks[0]['formalization']['label'], '50%')
        self.assertEqual(response.context['entry']['formalization']['unplanned'], 1)
        self.assertEqual(response.context['entry']['formalization']['label'], 'Partial')
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
        progress = entries()['sets-and-maps']['formalization']
        self.assertEqual((progress['complete'], progress['total']), (1, 1))
        self.assertEqual(progress['status'], 'partial')
        self.assertEqual(progress['label'], 'Partial')
        self.write_html(('data-formal="ready"', 'data-formal="ready"', 'data-formal=""'))
        self.assertEqual(entries()['sets-and-maps']['formalization']['status'], 'complete')
        self.assertEqual(entries()['sets-and-maps']['formalization']['label'], 'Complete')
        self.write_html(('',))
        self.assertEqual(entries()['sets-and-maps']['formalization']['label'], 'Not started')
        self.write_html(('data-formal=""',))
        self.assertEqual(entries()['sets-and-maps']['formalization']['status'], 'not_applicable')

    def test_mapping_validation_and_html_references_without_json_records(self):
        for attr in ('data-formal="unknown"', 'data-formal="ready ready"',
                     'data-formal="../ready"', 'data-formal', 'data-formal="" data-formal="ready"'):
            with self.subTest(attr=attr):
                self.write_html((attr,))
                with self.assertRaises(ContentError):
                    load_catalog(self.root / 'corpus', self.root)
        self.write_html(('data-formal="ready"', ''))
        self.html.write_text(self.html.read_text().replace('A mathematical claim.', '<a href="#block-1">See the answer</a>', 1))
        response = self.client.get('/entries/sets-and-maps/')
        self.assertContains(response, '?from=sets-and-maps&amp;at=block-0#block-1')

    def test_node_page_escapes_source_and_infers_line(self):
        response = self.client.get('/formal/nodes/ready/')
        self.assertContains(response, 'Lemmatheca.ready')
        self.assertContains(response, '&lt;script&gt;')
        self.assertNotContains(response, '<script>alert')
        self.assertContains(response, 'href="#L3"')
        self.assertContains(response, 'class="source-line declaration-line" id="L3"')
        self.assertEqual(response.context['declaration_line'], 3)
        self.assertContains(self.client.get('/formal/nodes/pending/'), 'Proof pending')
        self.assertContains(self.client.get('/formal/nodes/dependent/'), '/formal/nodes/pending/')

    def test_api_is_independent_of_corpus_and_read_only(self):
        self.html.unlink()
        response = self.client.get('/api/formal/nodes/ready/')
        self.assertEqual(response.json()['status'], 'complete')
        self.assertEqual(len(self.client.get('/api/formal/nodes/').json()['nodes']), 3)
        for url in ('/api/formal/nodes/', '/api/formal/nodes/ready/', '/formal/nodes/ready/'):
            self.assertEqual(self.client.post(url).status_code, 405)
            self.assertEqual(self.client.head(url).status_code, 200)
        for url in ('/api/formal/nodes/absent/', '/formal/nodes/absent/'):
            self.assertEqual(self.client.get(url).status_code, 404)

    def test_declaration_and_review_can_be_pending_independently(self):
        self.write_node('unwritten', declaration=None, module=None, reviewed=False)
        self.assertContains(self.client.get('/formal/nodes/unwritten/'), 'No Lean declaration has been written')
        self.write_node('ready', reviewed=False)
        self.write_report()
        node = load_nodes(self.root)['ready']
        self.assertEqual(node['status'], 'review_pending')
        self.assertEqual(node['status_label'], 'Pending review')
        self.source.write_text('')
        response = self.client.get('/formal/nodes/ready/')
        self.assertContains(response, '<pre')
        self.assertNotContains(response, 'This mathlib source is not installed')

    def test_node_statuses_identify_the_next_step_in_api_and_badge(self):
        self.write_node('unwritten', declaration=None, module=None, reviewed=False)
        self.write_node('review', reviewed=False)
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
                self.assertEqual((node['status'], node['status_label']), (status, label))
                self.assertNotIn('reason', node)
                page = self.client.get(f'/formal/nodes/{node_id}/')
                self.assertContains(page, f'class="formalization-badge formalization-{status}"')
                self.assertContains(page, label, count=1)
        self.write_node('ready', dependencies=['pending'])
        self.write_report()
        self.assertEqual(self.client.get('/api/formal/nodes/ready/').json()['status'], 'dependencies_pending')
        self.assertContains(self.client.get('/formal/nodes/ready/'), 'Dependencies pending', count=1)
        response = self.client.get('/entries/sets-and-maps/')
        self.assertContains(response, 'Dependencies pending')
        self.assertContains(response, 'Proof pending')
        self.assertEqual(response.context['entry']['blocks'][0]['formalization']['percent'], 0)

    def test_forged_status_cycles_and_unknown_dependencies_are_rejected(self):
        for changes in ({'status': 'complete'}, {'reviewed': 'yes'}, {'declaration': 'bad name'},
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

    def test_review_toggle_updates_progress_without_invalidating_lean_evidence(self):
        report = (self.root / REPORT).read_bytes()
        for reviewed, percent, label in ((False, 0, 'Pending review'), (True, 50, 'Complete'),
                                        (False, 0, 'Pending review')):
            with self.subTest(reviewed=reviewed):
                self.write_node('ready', reviewed=reviewed)
                node = self.client.get('/api/formal/nodes/ready/').json()
                self.assertEqual(node['status_label'], label)
                self.assertEqual(node['status'], 'complete' if reviewed else 'review_pending')
                self.assertIsNotNone(node['checked_on'])
                response = self.client.get('/entries/sets-and-maps/')
                self.assertEqual(response.context['entry']['blocks'][0]['formalization']['percent'], percent)
                self.assertEqual(response.context['entry']['formalization']['label'], 'Partial')
                self.assertContains(response, label)
                self.assertEqual((self.root / REPORT).read_bytes(), report)
        self.assertEqual(self.client.get('/api/formal/nodes/pending/').json()['status_label'], 'Proof pending')
        self.assertEqual(self.client.get('/api/formal/nodes/pending/').json()['status'], 'proof_pending')

    def test_old_report_and_changed_declaration_require_reverification(self):
        path = self.root / REPORT
        original = path.read_text()
        report = json.loads(original)
        report['format_version'] = 1
        path.write_text(json.dumps(report))
        self.assertEqual(load_nodes(self.root)['ready']['status'], 'verification_needed')
        path.write_text(original)
        self.write_node('ready', declaration='Lemmatheca.dependent')
        self.assertEqual(load_nodes(self.root)['ready']['status'], 'verification_needed')
        self.write_node('pending', declaration='Lemmatheca.ready')
        self.assertEqual(load_nodes(self.root)['pending']['status'], 'verification_needed')

    def test_stale_sources_environment_metadata_and_reports_invalidate_cached_progress(self):
        self.write_html(('data-formal="ready"',))
        for path in (self.source, self.formal / 'lean-toolchain', self.node_dir / 'ready.json', self.root / REPORT):
            with self.subTest(path=path.name):
                original = path.read_text()
                self.assertEqual(entries()['sets-and-maps']['formalization']['status'], 'complete')
                if path.name == 'ready.json':
                    data = json.loads(original)
                    data['dependencies'] = ['pending']
                    path.write_text(json.dumps(data))
                elif path.name == 'nodes.json':
                    data = json.loads(original)
                    data['nodes']['ready']['axioms'] = ['sorryAx']
                    path.write_text(json.dumps(data))
                else:
                    path.write_text(original + '\n')
                self.assertEqual(entries()['sets-and-maps']['formalization']['status'], 'partial')
                path.write_text(original)
        self.write_node('ready', dependencies=['pending'])
        self.write_report()
        self.assertEqual(load_nodes(self.root)['ready']['status'], 'dependencies_pending')

    def test_missing_mathlib_checkout_uses_pinned_source_and_installed_edits_invalidate(self):
        mathlib = self.formal / '.lake/packages/mathlib/Mathlib/Test.lean'
        mathlib.parent.mkdir(parents=True)
        mathlib.write_text('namespace Mathlib\ntheorem test : True := by trivial\nend Mathlib\n')
        self.write_node('ready', module='Mathlib.Test', declaration='Mathlib.test')
        self.write_report()
        mathlib.unlink()
        self.assertEqual(load_nodes(self.root)['ready']['status'], 'complete')
        response = self.client.get('/formal/nodes/ready/')
        self.assertContains(response, 'This mathlib source is not installed')
        self.assertContains(response, 'github.com/leanprover-community/mathlib4/blob/')
        mathlib.write_text('-- Changed\n')
        self.assertEqual(load_nodes(self.root)['ready']['status'], 'verification_needed')

    def test_pending_local_and_unrelated_namespace_declaration_lines(self):
        text = ('/- theorem Outside.wrong : True := by trivial\n/- nested -/ -/\n'
                'namespace Outside\nsection\nnamespace Inside\n'
                '-- theorem target : True := by trivial\n'
                'def text := "theorem target : True"\n'
                '@[simp] theorem target\n : True := by trivial\n'
                'end Inside\nend\nend Outside\n'
                'theorem rootTarget : True := by trivial\n')
        self.assertEqual(declaration_line(text, 'Outside.Inside.target'), 8)
        self.assertEqual(declaration_line(text, 'rootTarget'), 13)
        self.assertIsNone(declaration_line(text, 'Outside.wrong'))
        self.assertIsNone(declaration_line(text, 'Other.target'))

    def test_import_closure_includes_public_meta_and_all_imports_but_not_comments(self):
        external = self.formal / '.lake/packages/mathlib/Mathlib'
        external.mkdir(parents=True)
        (external / 'A.lean').write_text('public meta import all Mathlib.B\n')
        (external / 'B.lean').write_text('-- import Missing\nimport all Init.Control.Option\n')
        self.source.write_text('public import Mathlib.A\n' + self.source.read_text())
        self.write_report()
        self.assertEqual(load_nodes(self.root)['ready']['status'], 'complete')
        report = json.loads((self.root / REPORT).read_text())
        self.assertIn('formal/.lake/packages/mathlib/Mathlib/B.lean', report['sha256'])
        (external / 'B.lean').write_text('-- changed\n')
        self.assertEqual(load_nodes(self.root)['ready']['status'], 'verification_needed')


class FormalizationCommandTests(NodeFixtureMixin, SimpleTestCase):
    def run_check(self, axiom='sorryAx', side_effect=None):
        output = ("'Lemmatheca.ready' does not depend on any axioms\n"
                  f"'Lemmatheca.unfinished' depends on axioms: [{axiom}]\n"
                  f"'Lemmatheca.dependent' depends on axioms: [{axiom}]\n")
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
        self.assertEqual(load_nodes(self.root)['dependent']['status'], 'proof_pending')

    def test_custom_axiom_and_mid_run_source_changes_cannot_write_passing_report(self):
        original = (self.root / REPORT).read_text()
        with self.assertRaisesRegex(CommandError, 'unapproved axioms'):
            self.run_check('untrustedAxiom')
        self.assertEqual((self.root / REPORT).read_text(), original)
        with self.assertRaisesRegex(CommandError, 'changed during verification'):
            self.run_check(side_effect=lambda: self.source.write_text(self.source.read_text() + '\n'))
        self.assertEqual((self.root / REPORT).read_text(), original)
        self.assertEqual(load_nodes(self.root)['ready']['status'], 'verification_needed')
