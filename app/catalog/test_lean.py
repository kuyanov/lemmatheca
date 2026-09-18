"""A general Lean file viewer, independent of entry bindings."""

from pathlib import Path
from tempfile import TemporaryDirectory
from unittest.mock import patch

from django.conf import settings
from django.test import SimpleTestCase, override_settings
from django.urls import reverse
from django.utils.html import escape


class LeanFileTests(SimpleTestCase):
    def test_unbound_lean_files_are_viewable_without_loading_the_corpus(self):
        for source in ('formal/Lemmatheca.lean', 'Mathlib/Data/Finset/Card.lean'):
            with self.subTest(source=source), patch('catalog.views.entries') as catalog:
                response = self.client.get(reverse('catalog:lean_file', args=[source]))
                self.assertContains(response, source)
                self.assertContains(response, 'Lean source')
                self.assertNotContains(response, 'Formalization complete')
                self.assertNotContains(response, 'Proof incomplete')
                self.assertNotContains(response, 'katex.min.js')
                self.assertEqual(response.context['return_url'], '/')
                catalog.assert_not_called()

    def test_arbitrary_new_lean_file_is_escaped_and_changes_are_visible(self):
        with TemporaryDirectory() as temporary, override_settings(REPOSITORY_DIR=Path(temporary)):
            directory = Path(temporary) / 'formal/Experiments'
            directory.mkdir(parents=True)
            source = directory / 'New.lean'
            text = '-- <script>alert("hello")</script>\nexample : 1 ≤ 2 := by decide\n'
            source.write_text(text)
            url = reverse('catalog:lean_file', args=['formal/Experiments/New.lean'])
            response = self.client.get(url)
            self.assertContains(response, escape(text))
            self.assertNotContains(response, '<script>alert')
            source.write_text('-- Changed without a server restart\n')
            self.assertContains(self.client.get(url), 'Changed without a server restart')
            self.assertEqual(self.client.head(url).status_code, 200)
            self.assertEqual(self.client.post(url).status_code, 405)

    def test_invalid_paths_and_symlink_escapes_return_404(self):
        for source in ('formal/missing.lean', 'formal/lakefile.toml', '../app/config/settings.py',
                       'formal/../private.lean', 'formal/.lake/private.lean',
                       'Mathlib/../private.lean', '/tmp/private.lean', 'formal/dir\\private.lean',
                       'formal//Lemmatheca.lean', 'formal/Lemmatheca.lean/child.lean'):
            with self.subTest(source=source):
                response = self.client.get(reverse('catalog:lean_file', args=[source]))
                self.assertEqual(response.status_code, 404)
        self.assertEqual(self.client.get('/lean/formal/%2e%2e/private.lean/').status_code, 404)
        with TemporaryDirectory() as temporary, override_settings(REPOSITORY_DIR=Path(temporary)):
            root = Path(temporary)
            (root / 'formal').mkdir()
            (root / 'private.lean').write_text('Do not expose this file')
            (root / 'formal/Escape.lean').symlink_to(root / 'private.lean')
            response = self.client.get('/lean/formal/Escape.lean/')
            self.assertEqual(response.status_code, 404)
            self.assertNotContains(response, 'Do not expose this file', status_code=404)

    def test_invalid_context_cannot_claim_verification_or_change_the_return_destination(self):
        url = reverse('catalog:lean_file', args=['formal/Lemmatheca.lean'])
        for context in (
                {'from': 'https://example.org', 'at': 'sumset', 'status': 'complete'},
                {'from': 'thm-sumset-lower-bound', 'at': 'missing'},
                {'from': 'thm-sumset-lower-bound', 'at': 'sumset-lower-bound',
                 'declaration': 'Lemmatheca.sumset_card_lower_bound'}):
            with self.subTest(context=context):
                response = self.client.get(url, context)
                self.assertEqual(response.status_code, 200)
                self.assertNotContains(response, 'Formalization complete')
                self.assertEqual(response.context['return_url'], '/')
