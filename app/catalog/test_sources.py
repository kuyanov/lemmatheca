"""Exercise the corpus contract independently of the page templates."""

import json
from pathlib import Path

from django.conf import settings
from django.contrib.staticfiles import finders
from django.test import SimpleTestCase, override_settings
from django.urls import reverse

from .content import entries, load_catalog
from .sources import ContentError, render_block
from .testing import ExampleCorpusMixin


FIRST = "thm-sumset-lower-bound"
SECOND = "thm-triple-sumset-lower-bound"
THIRD = "thm-erdos-szekeres"


class CorpusSourceTests(ExampleCorpusMixin, SimpleTestCase):
    def setUp(self):
        super().setUp()
        self.source = self.corpus / "entries" / FIRST / "entry.html"
        self.metadata = self.source.with_suffix(".json")

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
            self.assertIn(
                'href="/entries/thm-sumset-lower-bound/?from=thm-sumset-lower-bound&amp;at=sumset-lower-bound#translation"', rendered)
            self.assertIn('>Definition 1</a>', rendered)

    def test_reading_order_controls_listing_and_next_entry(self):
        path = self.corpus / "reading-order.json"
        order = json.loads(path.read_text())
        order["areas"]["sumsets"].reverse()
        path.write_text(json.dumps(order))
        with override_settings(CORPUS_DIR=self.corpus):
            self.assertEqual([entry['id'] for entry in entries().values()
                              if entry['primary_area'] == 'sumsets'], [SECOND, FIRST])
            response = self.client.get(
                reverse("catalog:entry", args=[SECOND]))
            self.assertEqual(response.context["next_entry"]["id"], FIRST)
            response = self.client.get(
                reverse("catalog:entry", args=[FIRST]))
            self.assertIsNone(response.context["next_entry"])

    def test_figure_labels_and_references_follow_source_order(self):
        path = self.corpus / 'entries/sets-and-maps/entry.html'
        original = path.read_text()
        earlier = '<figure id="earlier"><figcaption>A preceding figure.</figcaption></figure>'
        for prefix, number in ((earlier, 2), ('', 1)):
            path.write_text(original.replace(
                '<figure id="map-picture"', prefix + '<figure id="map-picture"'))
            catalog = self.load()
            entry = catalog['sets-and-maps']
            self.assertEqual(
                entry['figures']['map-picture'], f'Figure {number}')
            caption = render_block(
                entry['blocks_by_id']['maps'], entry, catalog)
            reference = render_block(
                entry['blocks_by_id']['kinds-of-maps'], entry, catalog)
            self.assertIn(
                f'<span class="figure-label">Figure {number}</span>', caption)
            self.assertIn(f'>Figure {number}</a>', reference)
            self.assertNotIn('Figure 01', caption)
        path.write_text(original.replace(
            'href="#map-picture"', 'href="#missing-figure"'))
        with self.assertRaisesRegex(ContentError, 'Broken source link'):
            self.load()

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
        from .metadata import ENTRY_FIELDS
        for path in (self.corpus / 'entries').glob('*/entry.json'):
            metadata = json.loads(path.read_text())
            self.assertEqual(set(metadata), ENTRY_FIELDS)
            self.assertNotIn('blocks', metadata)


    def test_citations_display_compact_authors_titles_years_and_source_links(self):
        metadata = json.loads(self.metadata.read_text())
        metadata['based_on'] = [
            {'authors': ['Example Author', 'Second Author'], 'title': 'Original lecture notes',
             'url': 'https://example.org/notes', 'year': 2020, 'venue': 'Example Journal',
             'volume': '2', 'issue': '3', 'pages': '4–5', 'doi': '10.1234/notes'},
            {'authors': ['Third Author'], 'title': 'A printed source'}]
        self.metadata.write_text(json.dumps(metadata))
        with override_settings(CORPUS_DIR=self.corpus):
            response = self.client.get(reverse('catalog:entry', args=[FIRST]))
            self.assertContains(response, 'Based on:', count=1)
            self.assertContains(response, 'Example Author, Second Author')
            self.assertContains(response, 'href="https://example.org/notes"')
            self.assertContains(
                response, 'href="https://doi.org/10.1234/notes"')
            self.assertContains(response, 'Original lecture notes')
            self.assertNotContains(response, 'Example Journal')
            self.assertNotContains(response, 'p. 4–5.')
            self.assertContains(response, '(2020)')
            self.assertContains(response, 'A printed source')
            self.assertNotContains(response, 'rel="license"')
            self.assertNotContains(response, 'Mathematical note')

    def test_original_entries_omit_the_bibliography(self):
        with override_settings(CORPUS_DIR=self.corpus):
            response = self.client.get(reverse('catalog:entry', args=[FIRST]))
            self.assertNotContains(response, 'Based on:')
            self.assertNotContains(response, 'entry-bibliography')

    def test_invalid_citations_and_removed_entry_fields_are_rejected(self):
        original = self.metadata.read_text()
        citation = {'authors': ['An Author'], 'title': 'A paper'}
        changes = [
            {'based_on': None}, {'based_on': [None]},
            *({'based_on': [{**citation, **change}]} for change in [
                {'authors': []}, {'authors': 'An Author'}, {'title': ''},
                {'year': True}, {'year': '1959'}, {'pages': 352},
                {'doi': 'https://doi.org/10.1234/paper'}, {'doi': '10.1234/a b'},
                {'url': 'javascript:alert(1)'}, {'url': '//example.org/paper'},
                {'url': 'https://'}, {'unexpected': 'field'}]),
            {'authors': ['An Author']}, {'license': 'Apache-2.0'},
            {'source': {'title': 'Old source', 'url': 'https://example.org'}}]
        for change in changes:
            with self.subTest(change=change):
                metadata = {**json.loads(original), **change}
                self.metadata.write_text(json.dumps(metadata))
                with self.assertRaises(ContentError):
                    self.load()

    def test_paper_example_is_entirely_unformalized(self):
        with override_settings(CORPUS_DIR=self.corpus):
            response = self.client.get(reverse('catalog:entry', args=[THIRD]))
            entry = response.context['entry']
            self.assertEqual(entry['formalization']['status'], 'not_started')
            self.assertEqual(entry['formalization']['complete'], 0)
            self.assertContains(response, 'Formalization: Not started')
            self.assertContains(
                response, 'href="https://doi.org/10.1112/jlms/s1-34.3.352"')
            self.assertNotContains(response, 'href="/lean/')
            for block in entry['blocks']:
                formal = block['formalization']
                self.assertEqual(formal['status'], 'not_started')
                self.assertIsNone(block['formal_ids'])

    def test_equation_references_and_tables_render_with_math_and_accessible_links(self):
        entry = self.load()[FIRST]
        html = render_block(entry['blocks_by_id']
                            ['sumset-lower-bound'], entry, self.load())
        self.assertIn('id="eq:left-bound"', html)
        self.assertIn(r'\tag{1}', html)
        self.assertIn('href="#eq:left-bound"', html)
        self.assertIn('>(1)</a>', html)
        self.assertNotIn(r'\label', html)
        self.assertNotIn(r'\eqref', html)
        table = render_block(entry['blocks_by_id']
                             ['sumset'], entry, self.load())
        self.assertIn('class="table-scroll"', table)
        self.assertIn('tabindex="0"', table)
        self.assertIn('<caption>', table)
        self.assertIn('scope="col"', table)
        self.assertIn(r'\(a+b\)', table)

    def test_equation_reference_errors_fail_before_rendering(self):
        original = self.source.read_text()
        for before, after, message in [
            (r'\eqref{eq:left-bound}', r'\eqref{missing}',
             'Unknown equation reference'),
            (r'\label{eq:left-bound}', r'\label{eq:left-bound}\tag{9}',
             'numbered automatically'),
            (r'\label{eq:left-bound}',
             r'\label{eq:left-bound}\label{eq:other}', 'one equation label'),
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
