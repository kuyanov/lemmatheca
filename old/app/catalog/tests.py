"""Smoke tests for the live corpus and essential reader navigation."""

import json
from unittest.mock import patch

from django.conf import settings
from django.contrib.staticfiles import finders
from django.template.base import Lexer, TokenType
from django.template.loader import get_template
from django.test import SimpleTestCase, override_settings

from .content import area_link, areas, entries
from .testing import CorpusFixtureMixin


class RepositoryTests(SimpleTestCase):
    def test_current_corpus_renders(self):
        catalog = entries()
        home = self.client.get('/')
        first = next(iter(catalog.values()))
        self.assertContains(home, first['title'])
        self.assertContains(home, first['url'])
        for entry in catalog.values():
            with self.subTest(entry=entry['id']):
                self.assertContains(self.client.get(
                    area_link(areas()[entry['primary_area']])['url']), entry['url'])
                article = self.client.get(entry['url'])
                self.assertContains(article, entry['title'])
                self.assertContains(article, 'katex.min.js')
        for asset in ('vendor/katex/katex.min.js', 'vendor/katex/katex.min.css',
                      'vendor/katex/fonts/KaTeX_Main-Regular.woff2'):
            self.assertIsNotNone(finders.find(asset))

    def test_templates_have_no_split_or_invalid_tags(self):
        template_dir = settings.BASE_DIR / 'templates'
        for path in template_dir.rglob('*.html'):
            with self.subTest(template=path.name):
                for token in Lexer(path.read_text()).tokenize():
                    if token.token_type == TokenType.TEXT:
                        self.assertNotRegex(token.contents, r'\{[%{]')
                get_template(str(path.relative_to(template_dir)))


class ReaderTests(CorpusFixtureMixin, SimpleTestCase):
    def test_browsing_and_reading_order(self):
        home = self.client.get('/')
        self.assertContains(home, 'href="/areas/math/"')
        self.assertContains(home, '2 entries')
        area = self.client.get('/areas/math/')
        self.assertContains(area, 'href="/areas/math/sets/"')
        listing = self.client.get('/areas/math/sets/')
        self.assertContains(listing, 'href="/entries/first/"')
        first = self.client.get('/entries/first/')
        self.assertContains(first, 'href="/entries/second/" rel="next"')
        self.assertContains(first, 'Definition 2')
        self.assertNotContains(self.client.get(
            '/entries/second/'), 'rel="next"')
        order = self.corpus / 'reading-order.json'
        order.write_text(json.dumps(
            {'format_version': 1, 'areas': {'sets': ['second', 'first']}}))
        self.assertEqual(self.client.get(
            '/entries/second/').context['next_entry']['id'], 'first')
        self.assertContains(self.client.get('/'), 'href="/entries/second/"')
        with patch('catalog.views.entries', return_value={}):
            self.assertNotContains(self.client.get(
                '/'), 'class="featured-proof"')

    def test_references_return_to_the_citing_answer(self):
        article = self.client.get('/entries/first/')
        self.assertNotContains(article, 'class="question-answer" open')
        for target in ('/entries/second/?from=first&at=question#result',
                       '/entries/first/?from=first&at=question#notation'):
            with self.subTest(target=target):
                self.assertContains(article, target.replace('&', '&amp;'))
                result = self.client.get(target)
                self.assertContains(result, 'class="reading-return"')
                self.assertEqual(
                    result.context['return_url'], '/entries/first/?answer=question#question')
                returned = self.client.get(result.context['return_url'])
                self.assertContains(returned, 'class="question-answer" open')
        # Rendering an open answer must not mutate the cached source.
        self.assertNotContains(self.client.get(
            '/entries/first/'), 'class="question-answer" open')

    def test_entry_references_survive_moving_to_another_subarea(self):
        target = '/entries/second/?from=first&at=question#result'
        self.assertContains(self.client.get('/entries/first/'),
                            target.replace('&', '&amp;'))
        source = self.corpus / 'entries/first/entry.html'
        original_source = source.read_text()
        taxonomy_path = self.corpus / 'taxonomy.json'
        taxonomy = json.loads(taxonomy_path.read_text())
        taxonomy['areas'].append({
            'id': 'orders', 'title': 'Orders', 'parent': 'math',
            'description': 'Ordered sets.',
        })
        taxonomy_path.write_text(json.dumps(taxonomy))
        metadata_path = self.corpus / 'entries/second/entry.json'
        metadata = json.loads(metadata_path.read_text())
        metadata['primary_area'] = 'orders'
        metadata_path.write_text(json.dumps(metadata))
        (self.corpus / 'reading-order.json').write_text(json.dumps({
            'format_version': 1,
            'areas': {'sets': ['first'], 'orders': ['second']},
        }))

        self.assertEqual(source.read_text(), original_source)
        self.assertContains(self.client.get('/entries/first/'),
                            target.replace('&', '&amp;'))
        moved = self.client.get(target)
        self.assertContains(moved, 'href="/areas/math/orders/"')
        self.assertEqual(moved.context['return_url'],
                         '/entries/first/?answer=question#question')
        returned = self.client.get(moved.context['return_url'])
        self.assertContains(returned, 'class="question-answer" open')
        self.assertContains(self.client.get('/areas/math/orders/'),
                            'href="/entries/second/"')
        self.assertNotContains(self.client.get('/areas/math/sets/'),
                               'href="/entries/second/"')

    def test_local_block_figure_and_table_references_offer_a_return(self):
        article = self.client.get('/entries/first/')
        for target, label in (('sets', 'Definition 1'), ('diagram', 'Figure 1'),
                              ('notation', 'Table 1')):
            with self.subTest(target=target):
                url = f'/entries/first/?from=first&at=bound#{target}'
                self.assertContains(article, url.replace('&', '&amp;'))
                self.assertContains(article, f'>{label}</a>')
                response = self.client.get(url)
                self.assertContains(response, 'class="reading-return"')
                self.assertEqual(
                    response.context['return_url'], '/entries/first/#bound')

    def test_invalid_return_context_cannot_link_outside_the_library(self):
        response = self.client.get(
            '/entries/first/', {'from': 'https://example.org/'})
        self.assertNotContains(response, 'class="reading-return"')
        self.assertEqual(response.context['return_url'], '/areas/math/sets/')
        response = self.client.get(
            '/entries/first/', {'from': 'second', 'at': 'missing'})
        self.assertEqual(response.context['return_url'], '/entries/second/')

    def test_custom_404_in_development_and_production(self):
        for debug in (True, False):
            with self.subTest(debug=debug), override_settings(DEBUG=debug):
                self.assertContains(self.client.get(
                    '/missing/'), 'A missing connection.', status_code=404)
