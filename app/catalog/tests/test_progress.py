from django.template.loader import render_to_string
from django.test import SimpleTestCase

from catalog.progress import block_progress, entry_progress

from .html import HTML


class ProgressBadgeTests(SimpleTestCase):
    nodes = {
        "done": {"id": "done", "verified": True, "url": "/nodes/done/"},
        "pending": {"id": "pending", "verified": False, "url": "/nodes/pending/"},
    }

    def test_entry_and_block_badges_display_the_same_progress(self):
        cases = [
            (None, "not_started", None, 0, 0),
            ([], "not_applicable", None, 0, 0),
            (["pending"], "partial", 0, 0, 1),
            (["done", "pending"], "partial", 50, 1, 2),
            (["done"], "complete", 100, 1, 1),
        ]
        for ids, status, percent, complete, total in cases:
            with self.subTest(ids=ids):
                block = block_progress(ids, self.nodes)
                entry = entry_progress([{"formal_ids": ids}], self.nodes)
                self.assertEqual(block, entry)
                self.assertEqual(block["status"], status)
                self.assertEqual(block.get("percent"), percent)
                self.assertEqual(block["complete"], complete)
                self.assertEqual(block["total"], total)
                self.assertEqual(block["unplanned"], int(ids is None))
                page = HTML(render_to_string(
                    "catalog/_formalization_badge.html", {"formal": entry}))
                self.assertTrue(entry["label"])
                self.assertIn(entry["label"], page.root.text)
                self.assertTrue(entry["description"])
                self.assertTrue(page.find_all(
                    **{"aria-label": entry["description"]}))

    def test_unplanned_blocks_do_not_report_complete_or_a_percentage(self):
        result = entry_progress(
            [{"formal_ids": ["done"]}, {"formal_ids": None}], self.nodes)
        self.assertEqual(result["status"], "partial")
        self.assertNotIn("percent", result)
        self.assertEqual(result["complete"], 1)
        self.assertEqual(result["total"], 1)
        self.assertEqual(result["unplanned"], 1)
        result = entry_progress(
            [{"formal_ids": []}, {"formal_ids": None}], self.nodes)
        self.assertEqual(result["status"], "partial")
        self.assertNotIn("percent", result)

    def test_shared_nodes_are_counted_once(self):
        result = entry_progress(
            [{"formal_ids": ["done"]}, {"formal_ids": ["done", "pending"]}], self.nodes)
        self.assertEqual(result["percent"], 50)
        self.assertEqual(result["complete"], 1)
        self.assertEqual(result["total"], 2)

    def test_block_disclosure_contains_nodes_only_when_available(self):
        for ids in (None, [], ["done", "pending"]):
            with self.subTest(ids=ids):
                block = {"id": "example", "title": "Example", "label": "Lemma 1",
                         "formalization": block_progress(ids, self.nodes),
                         "formal_nodes": [self.nodes[identifier] for identifier in ids or []]}
                page = HTML(render_to_string(
                    "catalog/_block_heading.html", {"block": block}))
                self.assertIn("#example", page.hrefs)
                self.assertIn(block["formalization"]["label"], page.root.text)
                details = page.find_all("details")
                if ids:
                    self.assertEqual(len(details), 1)
                    self.assertNotIn("open", details[0].attrs)
                    self.assertTrue(any(details[0] in summary.ancestors() and summary.text
                                        for summary in page.find_all("summary")))
                    for identifier in ids:
                        links = page.find_all(
                            "a", href=self.nodes[identifier]["url"])
                        self.assertTrue(links)
                        self.assertTrue(
                            all(details[0] in link.ancestors() for link in links))
                else:
                    self.assertFalse(details)
                    self.assertTrue(
                        all(node["url"] not in page.hrefs for node in self.nodes.values()))
