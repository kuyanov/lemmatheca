from pathlib import Path
import shutil
from tempfile import TemporaryDirectory
from unittest.mock import patch

from django.conf import settings
from django.core.management import get_commands
from django.test import SimpleTestCase, override_settings
from django.urls import reverse

from catalog.content import add_progress, load_entry, next_entry
from catalog.entry_files import read_area_entries, read_entry_metadata
from catalog.files import read_json, records, write_json


class ReaderTests(SimpleTestCase):
    def test_area_index_and_next_entry_use_only_listed_metadata(self):
        with TemporaryDirectory() as directory:
            corpus = Path(directory)
            for identifier, area in [("alpha", "first"), ("alpha-tail", "first"),
                                     ("beta", "second"), ("omega", "first"), ("zeta", "first")]:
                entry_dir = corpus / "entries" / identifier
                entry_dir.mkdir(parents=True)
                write_json(entry_dir / "entry.json",
                           {"id": identifier, "primary_area": area})
            write_json(corpus / "area_entries.json", {
                "areas": {"first": ["zeta", "omega"], "second": ["beta"]},
            })

            # No HTML files exist: next-entry navigation needs metadata only.
            with override_settings(CORPUS_DIR=corpus):
                index = read_area_entries()
                self.assertEqual(index["first"], ["zeta", "omega"])
                self.assertEqual(next_entry(
                    read_entry_metadata("zeta"), index)["id"], "omega")
                for identifier in ("omega", "alpha", "alpha-tail", "beta"):
                    self.assertIsNone(next_entry(
                        read_entry_metadata(identifier), index))

    def test_corpus_pages_and_links(self):
        self.assertContains(self.client.get("/"), "Sets and maps")
        self.assertContains(self.client.get(
            "/"), "/areas/logic-and-foundations/")
        self.assertNotContains(self.client.get("/"), 'href="/nodes/"')
        self.assertEqual(self.client.get("/nodes/").status_code, 404)
        area = self.client.get("/areas/logic-and-foundations/set-theory/")
        self.assertContains(area, "Sets and maps")
        self.assertNotContains(area, "Draft")
        for identifier in records(settings.CORPUS_DIR, "entry"):
            entry = load_entry(identifier)
            response = self.client.get(f"/entries/{identifier}/")
            self.assertContains(response, entry["title"])
            self.assertNotRegex(response.content.decode(),
                                r'<a\b[^>]*>\s*</a>')
            self.assertContains(response, f"/static/entries/{identifier}/")
            for block in entry["blocks"]:
                self.assertContains(response, f'id="{block["id"]}"')
                for node in block["formal_ids"] or []:
                    self.assertContains(response, f'/formal/nodes/{node}/')
        response = self.client.get("/entries/ordered-sets/")
        self.assertContains(
            response, '/entries/sets-and-maps/?from=ordered-sets&amp;at=partial-and-total-orders#pairs-and-relations')
        for identifier in records(settings.CORPUS_DIR, "node"):
            self.assertEqual(self.client.get(
                f"/formal/nodes/{identifier}/").status_code, 200)

    def test_missing_records_and_read_only_views(self):
        for url in ["/entries/missing/", "/formal/nodes/missing/", "/api/formal/nodes/missing/",
                    "/areas/set-theory/", "/areas/missing/"]:
            self.assertEqual(self.client.get(url).status_code, 404)
        for url in ["/", "/areas/logic-and-foundations/", "/entries/sets-and-maps/",
                    "/formal/nodes/set/", "/api/formal/nodes/", "/api/formal/nodes/set/"]:
            self.assertEqual(self.client.post(url).status_code, 405)

    def test_contextual_navigation_and_question_return(self):
        response = self.client.get(
            "/entries/sets-and-maps/?from=ordered-sets&at=partial-and-total-orders")
        self.assertEqual(
            response.context["return_url"], "/entries/ordered-sets/#partial-and-total-orders")
        self.assertContains(response, "Back to Ordered sets")
        self.assertEqual(
            response.context["next_entry"]["id"], "equivalence-relations")
        response = self.client.get(
            "/entries/sets-and-maps/?from=sets-and-maps&at=image-intersection-question")
        self.assertEqual(response.context["return_url"],
                         "/entries/sets-and-maps/?answer=image-intersection-question#image-intersection-question")
        self.assertContains(response, "Back to Question 3")
        answer = self.client.get(
            "/entries/sets-and-maps/?answer=image-intersection-question")
        self.assertContains(answer, '<details class="question-answer" open>')
        ordinary = self.client.get("/entries/sets-and-maps/")
        self.assertNotContains(
            ordinary, '<details class="question-answer" open>')
        self.assertEqual(
            ordinary.context["return_url"], "/areas/logic-and-foundations/set-theory/")

    def test_tables_and_formalization_labels(self):
        response = self.client.get("/entries/sets-and-maps/")
        self.assertContains(response, 'class="table-scroll"')
        self.assertContains(
            response, '<span class="table-label">Table 1</span>')
        self.assertNotContains(response, "Draft")
        self.assertContains(response, "Formalization: 100%")
        self.assertNotContains(response, "awaiting maintainer review")
        self.assertContains(self.client.get(
            "/entries/ordered-sets/"), "Formalization: Not started")

    def test_saved_entry_summaries_match_current_block_bindings_and_node_results(self):
        for identifier in records(settings.CORPUS_DIR, "entry"):
            with self.subTest(entry=identifier):
                saved = read_entry_metadata(identifier)["formalization"]
                self.assertEqual(saved, add_progress(
                    load_entry(identifier))["formalization"])

    def test_node_declarations_and_source_links_do_not_run_lean(self):
        nodes = records(settings.CORPUS_DIR, "node")
        identifier = "nat-membership-and-inclusion-example"
        with patch("subprocess.run", side_effect=AssertionError("Page requests must not run Lean")):
            response = self.client.get(f"/formal/nodes/{identifier}/")
        self.assertContains(response, nodes[identifier]["declaration"])
        self.assertContains(response, "Verified")
        self.assertNotContains(response, "View declaration")
        self.assertNotContains(response, "Reviewed")
        self.assertContains(
            response, f'href="#L{nodes[identifier]["declaration_line"]}"')
        self.assertContains(response, 'class="source-line declaration-line"')
        self.assertContains(response, 'class="node-source-browser"')
        library = self.client.get("/formal/nodes/set-subset-transitive/")
        self.assertContains(
            library, f'href="#L{nodes["set-subset-transitive"]["declaration_line"]}"')
        self.assertContains(library, 'class="source-line declaration-line"')
        self.assertNotContains(library, "Pinned")
        api = self.client.get(f"/api/formal/nodes/{identifier}/").json()
        self.assertEqual(api["url"], reverse(
            "catalog:node", args=[identifier]))
        self.assertEqual(reverse("catalog:node_detail", args=[
                         identifier]), f"/api/formal/nodes/{identifier}/")
        self.assertIn(api, self.client.get(
            reverse("catalog:node_list")).json()["nodes"])
        self.assertTrue(api["verified"])
        self.assertNotIn("status", api)
        self.assertNotIn("source_module", api)
        self.assertEqual(api["module"], nodes[identifier]["module"])

    def test_verification_flag_controls_pages_and_entry_progress(self):
        with TemporaryDirectory() as directory:
            corpus = Path(directory) / "corpus"
            shutil.copytree(settings.CORPUS_DIR, corpus)
            path = corpus / "nodes/set.json"
            node = read_json(path)
            with override_settings(CORPUS_DIR=corpus):
                before = add_progress(load_entry(
                    "sets-and-maps"))["formalization"]
                write_json(path, {**node, "verified": False})
                response = self.client.get("/formal/nodes/set/")
                self.assertContains(response, "Not verified")
                self.assertContains(
                    response, f'href="#L{node["declaration_line"]}"')
                self.assertFalse(self.client.get(
                    "/api/formal/nodes/set/").json()["verified"])
                after = add_progress(load_entry(
                    "sets-and-maps"))["formalization"]
                self.assertEqual(after["complete"], before["complete"] - 1)
                self.assertEqual(after["total"], before["total"])
                entry = self.client.get("/entries/sets-and-maps/")
                self.assertContains(entry, "Not verified")
                self.assertNotContains(entry, "Draft")
                write_json(
                    path, {"id": "set", "description": "A set.", "verified": False})
                response = self.client.get("/formal/nodes/set/")
                self.assertContains(response, "Not verified")
                self.assertContains(response, "No Lean declaration")
                self.assertNotContains(response, "View declaration")

    def test_corpus_has_only_verification_status_and_no_review_command(self):
        self.assertNotIn("review", get_commands())
        for kind in ("node", "entry"):
            for record in records(settings.CORPUS_DIR, kind).values():
                self.assertFalse(
                    {"approved", "review", "proven", "sorry", "status"} & record.keys())
                if kind == "node":
                    self.assertIs(type(record["verified"]), bool)
