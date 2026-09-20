"""Essential source validation and mathematical rendering contracts."""

import json

from django.contrib.staticfiles import finders
from django.test import SimpleTestCase

from .content import entries, load_catalog
from .sources import ContentError, render_block
from .testing import CorpusFixtureMixin


class SourceTests(CorpusFixtureMixin, SimpleTestCase):
    def setUp(self):
        super().setUp()
        self.source = self.corpus / 'entries/first/entry.html'

    def load(self):
        return load_catalog(self.corpus, self.root)

    def test_source_edits_refresh_numbering_and_references(self):
        original = entries()['first']
        self.assertEqual(original['blocks_by_id']
                         ['sets']['label'], 'Definition 1')
        first, second, remainder = self.source.read_text().split('</section>', 2)
        self.source.write_text(second + '</section>' +
                               first + '</section>' + remainder)
        catalog = entries()
        entry = catalog['first']
        self.assertEqual(entry['blocks_by_id']['sets']
                         ['label'], 'Definition 2')
        self.assertIn('>Definition 2</a>',
                      render_block(entry['blocks_by_id']['bound'], entry, catalog))

    def test_equations_tables_figures_and_assets_render(self):
        catalog = self.load()
        entry = catalog['first']
        proof = render_block(entry['blocks_by_id']['bound'], entry, catalog)
        self.assertIn('id="eq:bound"', proof)
        self.assertIn(r'\tag{1}', proof)
        self.assertEqual(proof.count('href="#eq:bound"'), 2)
        self.assertIn(r'\(1+\text{(1)}\)', proof)
        self.assertNotIn(r'\eqref', proof)
        self.assertNotIn(r'\label', proof)
        definition = render_block(
            entry['blocks_by_id']['sets'], entry, catalog)
        self.assertIn('class="table-scroll"', definition)
        self.assertIn('<caption>Notation</caption>', definition)
        self.assertIn(r'\(a+b\)', definition)
        self.assertIn('<span class="figure-label">Figure 1</span>', definition)
        self.assertIn('>Figure 1</a>', proof)
        self.assertIn('/static/entries/first/diagram.svg', definition)
        self.assertIsNotNone(finders.find('entries/first/diagram.svg'))
        self.assertIsNone(finders.find('entries/first/entry.json'))

    def test_invalid_references_assets_and_markup_are_rejected(self):
        original = self.source.read_text()
        for before, after, message in (
            ('id="equality"', 'id="sets"', 'duplicate anchor'),
            ('href="#sets"', 'href="#missing"', 'Broken source link'),
            ('../second/entry.html#result',
             '../missing/entry.html#result', 'Broken source link'),
            ('assets/diagram.svg', 'assets/missing.svg', 'Missing or escaped asset'),
            ('assets/diagram.svg', 'assets/../../taxonomy.json', 'entry-local'),
            (r'\eqref{eq:bound}', r'\eqref{missing}',
             'Unknown equation reference'),
            ('</figure>', '</figcaption>', 'Unbalanced closing tag'),
        ):
            with self.subTest(change=after):
                self.source.write_text(original.replace(before, after))
                with self.assertRaisesRegex(ContentError, message):
                    self.load()

    def test_reading_order_requires_each_entry_once(self):
        for order in (['first'], ['first', 'second', 'first'], ['first', 'missing']):
            with self.subTest(order=order):
                (self.corpus / 'reading-order.json').write_text(json.dumps(
                    {'format_version': 1, 'areas': {'sets': order}}))
                with self.assertRaises(ContentError):
                    self.load()

    def test_entry_html_is_not_executed_as_a_template(self):
        self.source.write_text(self.source.read_text().replace(
            'Some sets', "{% include 'missing.html' %} {{ request.path }} Some sets"))
        response = self.client.get('/entries/first/')
        self.assertContains(response, "{% include 'missing.html' %}")
        self.assertContains(response, '{{ request.path }}')

    def test_citations_render_and_reject_invalid_metadata(self):
        path = self.source.with_suffix('.json')
        metadata = json.loads(path.read_text())
        citation = {'authors': ['An Author'], 'title': 'A source', 'year': 2020,
                    'url': 'https://example.org/notes', 'doi': '10.1234/notes'}
        metadata['based_on'] = [citation, {'authors': [
            'Another Author'], 'title': 'Another source'}]
        path.write_text(json.dumps(metadata))
        response = self.client.get('/entries/first/')
        self.assertContains(response, 'Based on:')
        self.assertContains(response, 'An Author')
        self.assertContains(response, 'href="https://doi.org/10.1234/notes"')
        self.assertContains(response, '<details class="bibliography-more">')
        for change in ({'url': 'javascript:alert(1)'}, {'authors': []}, {'title': ''}):
            with self.subTest(change=change):
                path.write_text(json.dumps(
                    {**metadata, 'based_on': [{**citation, **change}]}))
                with self.assertRaises(ContentError):
                    self.load()
        path.write_text(json.dumps({**metadata, 'unexpected': 'field'}))
        with self.assertRaises(ContentError):
            self.load()
