from django.template.loader import render_to_string
from django.test import SimpleTestCase

from catalog.progress import block_progress, entry_progress


class ProgressBadgeTests(SimpleTestCase):
    nodes = {
        "done": {"id": "done", "verified": True, "url": "/formal/nodes/done/"},
        "pending": {"id": "pending", "verified": False, "url": "/formal/nodes/pending/"},
    }

    def test_entry_and_block_badges_use_the_same_status_labels_and_icons(self):
        cases = [
            (None, "not_started", "Not started", "–"),
            ([], "not_applicable", "N/A", "–"),
            (["pending"], "partial", "0%", "◷"),
            (["done", "pending"], "partial", "50%", "◷"),
            (["done"], "complete", "100%", "✓"),
        ]
        for ids, status, label, icon in cases:
            with self.subTest(ids=ids):
                block = block_progress(ids, self.nodes)
                entry = entry_progress([{"formal_ids": ids}], self.nodes)
                self.assertEqual(block, entry)
                self.assertEqual(block["status"], status)
                self.assertEqual(block["label"], label)
                html = render_to_string(
                    "catalog/_formalization_badge.html", {"formal": entry})
                self.assertIn(f'formalization-{status}', html)
                self.assertIn(f'aria-hidden="true">{icon}</span>', html)
                self.assertIn(f"Formalization: {label}", html)
                self.assertNotIn("formalization-chevron", html)

    def test_unplanned_blocks_do_not_report_complete_or_a_percentage(self):
        result = entry_progress(
            [{"formal_ids": ["done"]}, {"formal_ids": None}], self.nodes)
        self.assertEqual(result["status"], "partial")
        self.assertEqual(result["label"], "Partial")
        self.assertNotIn("percent", result)
        self.assertEqual(
            result["description"], "1 of 1 nodes verified; 1 block awaiting planning")
        self.assertEqual(entry_progress(
            [{"formal_ids": []}, {"formal_ids": None}], self.nodes)["label"], "Partial")
        result = entry_progress(
            [{"formal_ids": ["done"]}, {"formal_ids": ["done", "pending"]}], self.nodes)
        self.assertEqual(result["label"], "50%")
        self.assertEqual(result["total"], 2)

    def test_block_disclosure_contains_nodes_only_when_available(self):
        for ids in (None, [], ["done", "pending"]):
            with self.subTest(ids=ids):
                block = {"id": "example", "title": "Example", "label": "Lemma 1",
                         "formalization": block_progress(ids, self.nodes),
                         "formal_nodes": [self.nodes[identifier] for identifier in ids or []]}
                html = render_to_string(
                    "catalog/_block_heading.html", {"block": block})
                self.assertEqual(html.count('class="formalization-badge '), 1)
                self.assertIn('href="#example"', html)
                if ids:
                    self.assertIn('<details class="formal-nodes">', html)
                    self.assertIn('formalization-chevron', html)
                    for identifier in ids:
                        self.assertIn(
                            f'href="/formal/nodes/{identifier}/"', html)
                else:
                    self.assertNotIn('<details', html)
                    self.assertNotIn('formalization-chevron', html)
