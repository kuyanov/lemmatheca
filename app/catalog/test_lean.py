"""A general Lean file viewer, independent of entry bindings."""

from io import StringIO
import json
from pathlib import Path
import shutil
from tempfile import TemporaryDirectory
from unittest.mock import patch

from django.conf import settings
from django.core.management import call_command
from django.test import SimpleTestCase, override_settings
from django.urls import reverse
from django.utils.html import escape

from .content import entries, load_catalog
from .metadata import formal_source_path
from .sources import ContentError


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


class WebsiteWithoutMathlibTests(SimpleTestCase):
    """Reproduce a server checkout containing tracked files but no formal/.lake."""

    def setUp(self):
        temporary = TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        shutil.copytree(settings.CORPUS_DIR, self.root / 'corpus')
        shutil.copytree(settings.REPOSITORY_DIR / 'formal', self.root / 'formal',
                        ignore=shutil.ignore_patterns('.lake'))
        configured = override_settings(REPOSITORY_DIR=self.root, CORPUS_DIR=self.root / 'corpus')
        configured.enable()
        self.addCleanup(configured.disable)

    def test_catalog_and_reader_work_without_lake_dependencies(self):
        self.assertFalse((self.root / 'formal/.lake').exists())
        output = StringIO()
        call_command('validate_corpus', stdout=output)
        self.assertIn('Validated 2 entries', output.getvalue())
        for url in ('/', '/areas/combinatorics/additive-combinatorics/sumsets/',
                    '/entries/thm-sumset-lower-bound/', '/entries/thm-triple-sumset-lower-bound/'):
            with self.subTest(url=url):
                self.assertEqual(self.client.get(url).status_code, 200)
        self.assertEqual(entries()['thm-sumset-lower-bound']['formalization']['status'], 'complete')

    def test_missing_mathlib_source_has_pinned_fallback_and_preserves_return_link(self):
        formal = entries()['thm-sumset-lower-bound']['blocks_by_id']['nonempty-sumset']['formalization']
        manifest = json.loads((self.root / 'formal/lake-manifest.json').read_text())
        commit = next(package['rev'] for package in manifest['packages'] if package['name'] == 'mathlib')
        url = formal['source_url']
        response = self.client.get(url)
        self.assertContains(response, 'This mathlib source is not installed on this server.')
        self.assertContains(response, f'https://github.com/leanprover-community/mathlib4/blob/{commit}/{formal["source"]}')
        self.assertEqual(response.context['return_url'], '/entries/thm-sumset-lower-bound/#nonempty-sumset')
        self.assertNotContains(response, '<pre')
        self.assertContains(self.client.get(url.split('?')[0]), 'This mathlib source is not installed')
        self.assertEqual(self.client.get('/lean/Mathlib/Missing.lean/').status_code, 404)
        self.assertEqual(self.client.get('/lean/Mathlib/../private.lean/').status_code, 404)

        # Installing sources later restores the viewer without a catalog edit.
        path = formal_source_path(formal, self.root, require_file=False)
        path.parent.mkdir(parents=True)
        path.write_text('-- Locally installed mathlib source\n')
        self.assertContains(self.client.get(url), 'Locally installed mathlib source')
        self.assertNotContains(self.client.get(url), 'This mathlib source is not installed')

    def test_missing_local_sources_and_unreported_mathlib_paths_still_fail_validation(self):
        with self.assertRaisesRegex(ContentError, 'Missing Lean source:.*Mathlib'):
            formal = entries()['thm-sumset-lower-bound']['blocks_by_id']['sumset']['formalization']
            formal_source_path(formal, self.root)
        report = self.root / 'formal/checks/sumsets.json'
        original = report.read_text()
        data = json.loads(original)
        data['sha256'].pop('formal/.lake/packages/mathlib/' + formal['source'])
        report.write_text(json.dumps(data))
        with self.assertRaisesRegex(ContentError, 'Mathlib source missing from the verification report'):
            load_catalog(self.root / 'corpus', self.root)
        report.write_text(original)
        (self.root / 'formal/Lemmatheca/Combinatorics/Additive/FiniteSumsets.lean').unlink()
        with self.assertRaisesRegex(ContentError, 'Missing Lean source:.*FiniteSumsets.lean'):
            load_catalog(self.root / 'corpus', self.root)
