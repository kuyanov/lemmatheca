"""Essential source validation and mathematical rendering contracts."""

import json

from django.contrib.staticfiles import finders
from django.test import SimpleTestCase, override_settings
from django.urls import include, path

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
        self.assertIn(
            '<caption><span class="table-label">Table 1</span> Notation</caption>', definition)
        self.assertIn('aria-label="Table 1 Notation"', definition)
        self.assertIn('>Table 1</a>', proof)
        self.assertIn(r'\(a+b\)', definition)
        self.assertIn('<span class="figure-label">Figure 1</span>', definition)
        self.assertIn('>Figure 1</a>', proof)
        self.assertIn('/static/entries/first/diagram.svg', definition)
        self.assertIsNotNone(finders.find('entries/first/diagram.svg'))
        self.assertIsNone(finders.find('entries/first/entry.json'))

    def test_table_numbers_refresh_independently_of_figures_and_other_entries(self):
        original = self.source.read_text().replace(
            '<h2>Sets</h2>', '<h2>Sets</h2><p>See <a href="#notation"></a>.</p>')
        self.source.write_text(original)
        catalog = entries()
        entry = catalog['first']
        definition = render_block(
            entry['blocks_by_id']['sets'], entry, catalog)
        self.assertIn('>Table 1</a>', definition)

        self.source.write_text(original.replace('<table id="notation">', '''
<table><caption>An earlier table</caption><tr><td>Earlier</td></tr></table>
<table id="notation">'''))
        second = self.corpus / 'entries/second/entry.html'
        second.write_text(second.read_text().replace('</section>', '''
<table id="other-table"><caption>Other entry</caption><tr><td>Other</td></tr></table>
</section>'''))
        catalog = entries()
        entry = catalog['first']
        definition = render_block(
            entry['blocks_by_id']['sets'], entry, catalog)
        self.assertIn('>Table 2</a>', definition)
        self.assertIn(
            '<span class="table-label">Table 1</span> An earlier table', definition)
        self.assertIn(
            '<span class="table-label">Table 2</span> Notation', definition)
        self.assertIn('<span class="figure-label">Figure 1</span>', definition)
        self.assertEqual(render_block(
            entry['blocks_by_id']['sets'], entry, catalog), definition)
        other = catalog['second']
        self.assertIn('<span class="table-label">Table 1</span> Other entry',
                      render_block(other['blocks_by_id']['result'], other, catalog))

    def test_reference_text_takes_priority_over_generated_labels(self):
        original = self.source.read_text()
        for href, target in (
            ('#sets', '/entries/first/?from=first&at=reference#sets'),
            ('first#sets', '/entries/first/?from=first&at=reference#sets'),
            ('second#result',
             '/entries/second/?from=first&at=reference#result'),
            ('#diagram', '/entries/first/?from=first&at=reference#diagram'),
            ('#notation', '/entries/first/?from=first&at=reference#notation'),
        ):
            for text in ('binary relation', r'<em>the sets \(A\) &amp; \(B\)</em>'):
                with self.subTest(href=href, text=text):
                    self.source.write_text(original + f'''
<section id="reference" data-kind="lemma"><h2>References</h2>
  <p>See <a href="{href}">{text}</a>.</p>
</section>''')
                    catalog = self.load()
                    entry = catalog['first']
                    block = entry['blocks_by_id']['reference']
                    rendered = render_block(block, entry, catalog)
                    self.assertIn(f'>{text}</a>', rendered)
                    self.assertIn(
                        f'href="{target.replace("&", "&amp;")}"', rendered)
                    # Rendering twice must preserve the cached source and its markup.
                    self.assertEqual(render_block(
                        block, entry, catalog), rendered)

    def test_empty_reference_text_uses_generated_labels(self):
        original = self.source.read_text()
        for href, label in (
            ('#sets', 'Definition 1'),
            ('first#sets', 'Definition 1'),
            ('second#result', 'Another result'),
            ('#diagram', 'Figure 1'),
            ('#notation', 'Table 1'),
        ):
            for text in ('', ' \n\t ', '<span> &nbsp; </span>'):
                with self.subTest(href=href, text=text):
                    self.source.write_text(original + f'''
<section id="reference" data-kind="lemma"><h2>References</h2>
  <p>See <a href="{href}">{text}</a>.</p>
</section>''')
                    catalog = self.load()
                    entry = catalog['first']
                    rendered = render_block(
                        entry['blocks_by_id']['reference'], entry, catalog)
                    self.assertIn(f'>{label}</a>', rendered)

    def test_entry_reference_url_is_resolved_when_rendering(self):
        catalog = self.load()
        entry = catalog['first']
        block = entry['blocks_by_id']['question']

        class MovedRoutes:
            urlpatterns = [path('reader/', include('catalog.urls'))]

        with override_settings(ROOT_URLCONF=MovedRoutes):
            rendered = render_block(block, entry, catalog)
        self.assertIn(
            'href="/reader/entries/second/?from=first&amp;at=question#result"', rendered)
        self.assertIn('>Another result</a>', rendered)

    def test_invalid_references_assets_and_markup_are_rejected(self):
        original = self.source.read_text()
        for before, after, message in (
            ('id="equality"', 'id="sets"', 'duplicate anchor'),
            ('id="notation"', 'id="diagram"', 'duplicate anchor'),
            ('href="#sets"', 'href="#missing"', 'Broken source link'),
            ('second#result',
             'missing#result', 'Broken source link'),
            ('second#result', 'second#missing', 'Broken source link'),
            ('second#result', 'second', 'Broken source link'),
            ('second#result', 'second?area=sets#result', 'Broken source link'),
            ('second#result', 'first#diagram', 'must name a mathematical block'),
            ('second#result', 'first#notation', 'must name a mathematical block'),
            ('second#result', '../second/entry.html#result', 'Use entry-id#block-id'),
            ('second#result', '/entries/second/#result', 'Use entry-id#block-id'),
            ('#sets', 'entry.html#sets', 'Use entry-id#block-id'),
            ('assets/diagram.svg', 'assets/missing.svg', 'Missing or escaped asset'),
            ('assets/diagram.svg', 'assets/../../taxonomy.json', 'entry-local'),
            (r'\eqref{eq:bound}', r'\eqref{missing}',
             'Unknown equation reference'),
            ('</figure>', '</figcaption>', 'Unbalanced closing tag'),
            ('<caption>Notation</caption>', '', 'Each table needs one caption'),
            ('<caption>Notation</caption>',
             '<caption>Notation</caption><caption>Extra</caption>', 'Each table needs one caption'),
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
