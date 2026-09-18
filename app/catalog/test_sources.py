"""Exercise the new file contract, independently of the example page templates."""

import json
from pathlib import Path
import shutil
from tempfile import TemporaryDirectory

from django.conf import settings
from django.contrib.staticfiles import finders
from django.test import SimpleTestCase, override_settings
from django.urls import reverse
from django.utils.html import escape

from .content import entries, load_catalog
from .lean import lean_source_url
from .sources import ContentError, render_block


FIRST = "thm-sumset-lower-bound"
SECOND = "thm-triple-sumset-lower-bound"


class CorpusSourceTests(SimpleTestCase):
    def setUp(self):
        temporary = TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.corpus = Path(temporary.name) / "corpus"
        shutil.copytree(settings.CORPUS_DIR, self.corpus)
        self.source = self.corpus / "entries" / FIRST / "entry.html"
        self.metadata = self.source.with_suffix(".json")
        second = json.loads((self.corpus / 'entries' / SECOND / 'entry.json').read_text())
        self.pending = second['blocks']['integer-triple-sumset-bound']['formalization']['unformalized_dependencies']

    def load(self):
        return load_catalog(self.corpus, settings.REPOSITORY_DIR)

    def test_html_order_controls_numbers_and_saving_invalidates_the_cache(self):
        with override_settings(CORPUS_DIR=self.corpus):
            original = entries()[FIRST]
            self.assertEqual(original["blocks_by_id"]
                             ["sumset"]["label"], "Definition 1")
            source = self.source.read_text()
            first, second, remainder = source.split("</section>", 2)
            self.source.write_text(
                second.strip() + "</section>\n" + first + "</section>" + remainder)
            updated = entries()[FIRST]
            self.assertEqual(updated["blocks_by_id"]
                             ["sumset"]["label"], "Definition 2")
            self.assertEqual(updated["blocks_by_id"]
                             ["translation"]["label"], "Definition 1")
            rendered = render_block(
                updated["blocks_by_id"]["sumset-lower-bound"], updated, entries())
            self.assertIn('href="#translation"', rendered)
            self.assertIn('>Definition 1</a>', rendered)

    def test_reading_order_controls_listing_and_next_entry(self):
        path = self.corpus / "reading-order.json"
        order = json.loads(path.read_text())
        order["areas"]["sumsets"].reverse()
        path.write_text(json.dumps(order))
        with override_settings(CORPUS_DIR=self.corpus):
            self.assertEqual(list(entries()), [SECOND, FIRST])
            response = self.client.get(
                reverse("catalog:entry", args=[SECOND]))
            self.assertEqual(response.context["next_entry"]["id"], FIRST)
            response = self.client.get(
                reverse("catalog:entry", args=[FIRST]))
            self.assertIsNone(response.context["next_entry"])

    def test_broken_html_references_and_assets_fail_validation(self):
        original = self.source.read_text()
        changes = [
            ('id="translation"', 'id="sumset"', "duplicate anchor"),
            ('href="#translation"', 'href="#missing"', "Broken source link"),
            ('assets/sumset-translation.svg',
             'assets/missing.svg', "Missing or escaped asset"),
            ('assets/sumset-translation.svg',
             'assets/../../taxonomy.json', "entry-local"),
            ('</figure>', '</figcaption>', "Unbalanced closing tag"),
        ]
        for before, after, message in changes:
            with self.subTest(change=after):
                self.source.write_text(original.replace(before, after))
                with self.assertRaisesRegex(ContentError, message):
                    self.load()

    def test_missing_bindings_broken_references_and_lean_paths_fail_validation(self):
        original = self.metadata.read_text()
        for change in ("binding", "target", "lean", "references"):
            metadata = json.loads(original)
            if change == "binding":
                metadata["blocks"]["missing"] = {}
            elif change == "target":
                metadata["blocks"]["sumset-lower-bound"]["references"][0]["block_id"] = "missing"
            elif change == "lean":
                metadata["blocks"]["sumset-lower-bound"]["formalization"]["source"] = "missing.lean"
            else:
                metadata["blocks"]["sumset-lower-bound"]["references"] = []
            with self.subTest(change=change):
                self.metadata.write_text(json.dumps(metadata))
                with self.assertRaises(ContentError):
                    self.load()

    def test_missing_and_duplicate_reading_order_entries_fail_validation(self):
        path = self.corpus / "reading-order.json"
        for ordered in ([FIRST], [FIRST, SECOND, FIRST], [FIRST, "missing"]):
            with self.subTest(order=ordered):
                path.write_text(json.dumps(
                    {"format_version": 1, "areas": {"sumsets": ordered}}))
                with self.assertRaises(ContentError):
                    self.load()

    def test_source_is_not_executed_as_a_django_template(self):
        self.source.write_text(self.source.read_text().replace(
            "Throughout this note", "{% include 'missing.html' %} {{ request.path }} Throughout this note"))
        catalog = self.load()
        entry = catalog[FIRST]
        html = render_block(entry["blocks_by_id"]["sumset"], entry, catalog)
        self.assertIn("{% include 'missing.html' %}", html)
        self.assertIn("{{ request.path }}", html)

    def test_answer_state_does_not_leak_between_requests(self):
        catalog = self.load()
        entry = catalog[SECOND]
        block = entry["blocks_by_id"]["strict-growth-question"]
        self.assertIn('class="question-answer" open',
                      render_block(block, entry, catalog, block["id"]))
        self.assertNotIn('class="question-answer" open',
                         render_block(block, entry, catalog))

    def test_only_entry_assets_are_collected_as_static_files(self):
        relative = f"entries/{FIRST}/sumset-translation.svg"
        found = Path(finders.find(relative))
        self.assertEqual(found, settings.CORPUS_DIR / "entries" /
                         FIRST / "assets/sumset-translation.svg")
        self.assertIsNone(finders.find(f"entries/{FIRST}/entry.json"))
        self.assertIsNone(finders.find(f"entries/{FIRST}/entry.html"))

    def test_supplementary_files_use_the_same_entry_local_asset_paths(self):
        (self.source.parent / "assets/notes.txt").write_text("Supplementary notes")
        self.source.write_text(self.source.read_text().replace(
            "Throughout this note", '<a href="assets/notes.txt">Notes</a> Throughout this note'))
        catalog = self.load()
        entry = catalog[FIRST]
        html = render_block(entry["blocks_by_id"]["sumset"], entry, catalog)
        self.assertIn(f'href="/static/entries/{FIRST}/notes.txt"', html)

    def test_metadata_has_only_the_essential_fields(self):
        from .metadata import ENTRY_FIELDS, FORMAL_FIELDS
        for path in (self.corpus / 'entries').glob('*/entry.json'):
            metadata = json.loads(path.read_text())
            self.assertEqual(set(metadata), ENTRY_FIELDS)
            for block in metadata['blocks'].values():
                self.assertEqual(set(block), {'formalization', 'references'})
                self.assertEqual(set(block['formalization']), FORMAL_FIELDS)
                for reference in block['references']:
                    self.assertEqual(set(reference), {'entry_id', 'block_id'})

    def test_formalization_badge_is_derived_from_all_blocks_including_answers(self):
        metadata = json.loads(self.metadata.read_text())
        with override_settings(CORPUS_DIR=self.corpus):
            url = reverse('catalog:entry', args=[FIRST])
            response = self.client.get(url)
            self.assertEqual(response.context['entry']['formalization']['status'], 'complete')
            self.assertContains(response, 'formalization-complete')
            self.assertContains(response, '✓')
            metadata['blocks']['nonempty-question']['formalization']['status'] = 'partial'
            self.metadata.write_text(json.dumps(metadata))
            response = self.client.get(url)
            self.assertEqual(response.context['entry']['formalization']['status'], 'partial')
            self.assertContains(response, 'Partially formalized')
            for block in metadata['blocks'].values():
                block['formalization']['status'] = 'not_started'
            self.metadata.write_text(json.dumps(metadata))
            response = self.client.get(url)
            self.assertEqual(response.context['entry']['formalization']['status'], 'not_started')
            self.assertContains(response, 'Not formalized')

    def test_partial_formalizations_allow_missing_declarations(self):
        metadata = json.loads(self.metadata.read_text())
        formal = metadata['blocks']['translation']['formalization']
        formal.update(status='partial', declaration=None, source=None, module=None, verification_report=None)
        self.metadata.write_text(json.dumps(metadata))
        self.assertEqual(self.load()[FIRST]['formalization']['status'], 'partial')
        formal['status'] = 'complete'
        self.metadata.write_text(json.dumps(metadata))
        with self.assertRaisesRegex(ContentError, 'Complete formalizations need'):
            self.load()

    def test_complete_formalizations_reject_pending_dependencies_even_without_report_checks(self):
        original = self.metadata.read_text()
        for block_id in ('translation', 'nonempty-sumset'):
            for check_reports in (True, False):
                with self.subTest(block=block_id, check_reports=check_reports):
                    metadata = json.loads(original)
                    metadata['blocks'][block_id]['formalization']['unformalized_dependencies'] = self.pending
                    self.metadata.write_text(json.dumps(metadata))
                    with self.assertRaisesRegex(ContentError, 'cannot have unformalized dependencies'):
                        load_catalog(self.corpus, settings.REPOSITORY_DIR, check_reports=check_reports)

    def test_pending_dependencies_require_valid_unique_local_lean_bindings(self):
        metadata = json.loads(self.metadata.read_text())
        formal = metadata['blocks']['translation']['formalization']
        formal.update(declaration=None, source=None, module=None, verification_report=None)
        for status in ('partial', 'not_started'):
            formal.update(status=status, unformalized_dependencies=self.pending)
            self.metadata.write_text(json.dumps(metadata))
            self.assertEqual(self.load()[FIRST]['blocks_by_id']['translation']['formalization']['status'], status)
        for invalid in (
                None, 'A statement', [None], [1], ['A statement'], [{}],
                [self.pending[0], self.pending[0]],
                [{**self.pending[0], 'declaration': 'not a Lean name'}],
                [{**self.pending[0], 'source': '../../secrets.lean'}],
                [{**self.pending[0], 'source': None}],
                [{**self.pending[0], 'module': 'Mathlib.Data.Finset.Card'}]):
            with self.subTest(dependencies=invalid):
                formal['unformalized_dependencies'] = invalid
                self.metadata.write_text(json.dumps(metadata))
                with self.assertRaises(ContentError):
                    self.load()

    def test_partial_integer_bound_displays_pending_statements_and_entry_badge(self):
        with override_settings(CORPUS_DIR=self.corpus):
            response = self.client.get(reverse('catalog:entry', args=[SECOND]))
            entry = response.context['entry']
            self.assertEqual(entry['formalization']['status'], 'partial')
            self.assertEqual(entry['formalization']['complete'], 4)
            self.assertEqual(entry['formalization']['total'], 5)
            block = entry['blocks_by_id']['integer-triple-sumset-bound']
            self.assertEqual(block['label'], 'Theorem 2')
            self.assertEqual(block['formalization']['status'], 'partial')
            self.assertIsNone(block['formalization']['declaration'])
            self.assertIsNone(block['formalization']['verification_report'])
            self.assertContains(response, 'formalization-partial')
            self.assertContains(response, '2 statements pending')
            self.assertContains(response, 'Unproved dependencies')
            for dependency in block['formalization']['unformalized_dependencies']:
                url = dependency['source_url']
                self.assertTrue(url.startswith('/lean/formal/'))
                self.assertContains(response, f'href="{escape(url)}"')
                self.assertContains(response, dependency['declaration'])
            self.assertEqual(entries()[FIRST]['formalization']['status'], 'complete')

    def test_dependency_links_show_escaped_lean_source_and_return_to_the_block(self):
        block_id = 'integer-triple-sumset-bound'
        with override_settings(CORPUS_DIR=self.corpus):
            for dependency in self.pending:
                url = lean_source_url(dependency, entry_id=SECOND, block_id=block_id)
                response = self.client.get(url)
                self.assertContains(response, 'Proof incomplete')
                self.assertContains(response, 'sorry')
                self.assertContains(response, dependency['declaration'])
                source = (settings.REPOSITORY_DIR / dependency['source']).read_text()
                self.assertContains(response, escape(source))
                self.assertContains(response, f'href="/entries/{SECOND}/#{block_id}"')
                self.assertNotContains(response, 'katex.min.js')
                self.assertEqual(self.client.head(url).status_code, 200)
                self.assertEqual(self.client.post(url).status_code, 405)

    def test_complete_formalizations_link_to_local_and_mathlib_source_files(self):
        with override_settings(CORPUS_DIR=self.corpus):
            record = entries()[FIRST]
            response = self.client.get(reverse('catalog:entry', args=[FIRST]))
            for block_id in ('sumset-lower-bound', 'nonempty-sumset', 'nonempty-question'):
                block = record['blocks_by_id'][block_id]
                formal = block['formalization']
                self.assertContains(response, f'href="{escape(formal["source_url"])}"')
                viewer = self.client.get(formal['source_url'])
                self.assertContains(viewer, 'Formalization complete')
                self.assertContains(viewer, formal['declaration'])
                return_url = reverse('catalog:entry', args=[FIRST])
                if block['kind'] == 'question':
                    return_url += '?answer=' + block_id
                self.assertEqual(viewer.context['return_url'], return_url + '#' + block_id)
                if formal['is_mathlib']:
                    self.assertContains(viewer, 'github.com/leanprover-community/mathlib4/blob/')

    def test_authors_license_and_optional_material_source_are_displayed(self):
        metadata = json.loads(self.metadata.read_text())
        metadata['authors'] = ['Example Author', 'Second Author']
        metadata['source'] = {'title': 'Original lecture notes', 'url': 'https://example.org/notes'}
        self.metadata.write_text(json.dumps(metadata))
        with override_settings(CORPUS_DIR=self.corpus):
            response = self.client.get(reverse('catalog:entry', args=[FIRST]))
            self.assertContains(response, 'Example Author, Second Author')
            self.assertContains(response, 'https://spdx.org/licenses/Apache-2.0.html')
            self.assertContains(response, 'https://example.org/notes')
            self.assertContains(response, 'Original lecture notes')
            self.assertNotContains(response, 'Mathematical note')
        metadata['source']['url'] = 'javascript:alert(1)'
        self.metadata.write_text(json.dumps(metadata))
        with self.assertRaisesRegex(ContentError, 'HTTP'):
            self.load()

    def test_mathlib_declarations_do_not_require_a_local_proof(self):
        catalog = self.load()
        formal = catalog[FIRST]['blocks_by_id']['nonempty-sumset']['formalization']
        self.assertEqual(formal['declaration'], 'Finset.Nonempty.add')
        self.assertEqual(formal['source'], 'Mathlib/Algebra/Group/Pointwise/Finset/Basic.lean')
        self.assertTrue(formal['is_mathlib'])
        self.assertTrue(formal['source_url'].startswith('/lean/Mathlib/'))
        metadata = json.loads(self.metadata.read_text())
        metadata['blocks']['nonempty-sumset']['formalization']['declaration'] = 'Finset.missing_declaration'
        self.metadata.write_text(json.dumps(metadata))
        with self.assertRaisesRegex(ContentError, 'Declaration missing'):
            self.load()

    def test_equation_references_and_tables_render_with_math_and_accessible_links(self):
        entry = self.load()[FIRST]
        html = render_block(entry['blocks_by_id']['sumset-lower-bound'], entry, self.load())
        self.assertIn('id="eq:left-bound"', html)
        self.assertIn(r'\tag{1}', html)
        self.assertIn('href="#eq:left-bound"', html)
        self.assertIn('>(1)</a>', html)
        self.assertNotIn(r'\label', html)
        self.assertNotIn(r'\eqref', html)
        table = render_block(entry['blocks_by_id']['sumset'], entry, self.load())
        self.assertIn('class="table-scroll"', table)
        self.assertIn('tabindex="0"', table)
        self.assertIn('<caption>', table)
        self.assertIn('scope="col"', table)
        self.assertIn(r'\(a+b\)', table)

    def test_equation_reference_errors_fail_before_rendering(self):
        original = self.source.read_text()
        for before, after, message in [
            (r'\eqref{eq:left-bound}', r'\eqref{missing}', 'Unknown equation reference'),
            (r'\label{eq:left-bound}', r'\label{eq:left-bound}\tag{9}', 'numbered automatically'),
            (r'\label{eq:left-bound}', r'\label{eq:left-bound}\label{eq:other}', 'one equation label'),
        ]:
            with self.subTest(change=after):
                self.source.write_text(original.replace(before, after))
                with self.assertRaisesRegex(ContentError, message):
                    self.load()

    def test_equation_references_work_forward_and_inside_inline_math(self):
        original = self.source.read_text()
        self.source.write_text(original.replace('Throughout this note,',
            r'Use \eqref{eq:left-bound}, \(\eqref{eq:left-bound}\), or \(1+\eqref{eq:left-bound}\). Throughout this note,'))
        catalog = self.load()
        entry = catalog[FIRST]
        html = render_block(entry['blocks_by_id']['sumset'], entry, catalog)
        self.assertEqual(html.count('href="#eq:left-bound"'), 2)
        self.assertIn(r'\(1+\text{(1)}\)', html)
