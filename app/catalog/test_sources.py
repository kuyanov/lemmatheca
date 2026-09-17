"""Exercise the new file contract, independently of the example page templates."""

import json
from pathlib import Path
import shutil
from tempfile import TemporaryDirectory

from django.conf import settings
from django.contrib.staticfiles import finders
from django.test import SimpleTestCase, override_settings
from django.urls import reverse

from .content import entries, load_catalog
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
            ('id="proof-sumset-lower-bound-translation"',
             'id="missing-proof"', "no source anchor"),
        ]
        for before, after, message in changes:
            with self.subTest(change=after):
                self.source.write_text(original.replace(before, after))
                with self.assertRaisesRegex(ContentError, message):
                    self.load()

    def test_missing_bindings_stale_revisions_and_lean_paths_fail_validation(self):
        original = self.metadata.read_text()
        for change in ("binding", "revision", "lean", "references"):
            metadata = json.loads(original)
            if change == "binding":
                metadata["blocks"]["missing"] = {}
            elif change == "revision":
                metadata["blocks"]["sumset-lower-bound"]["references"][0]["revision"] = "old"
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
