from pathlib import Path
import shutil
from tempfile import TemporaryDirectory
from unittest.mock import patch
from urllib.parse import parse_qs, urlsplit

from django.conf import settings
from django.core.management import get_commands
from django.test import SimpleTestCase, override_settings
from django.urls import reverse

from catalog.content import add_progress, load_entry, next_entry
from catalog.entry_files import read_area_entries, read_entry_metadata
from catalog.files import read_json, write_json
from catalog.node_files import read_node

from .html import HTML


class ReaderTests(SimpleTestCase):
    def page(self, response):
        self.assertEqual(response.status_code, 200)
        return HTML.from_response(response)

    def assert_source_link(self, response, node):
        page = self.page(response)
        anchor = f"L{node['declaration_line']}"
        self.assertIn(f"#{anchor}", page.hrefs)
        self.assertIn(anchor, page.ids)
        selected = [line["number"]
                    for line in response.context["source_lines"] if line["selected"]]
        self.assertEqual(selected, [node["declaration_line"]])

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

    def test_representative_pages_and_links(self):
        home = self.page(self.client.get("/"))
        self.assertIn("https://github.com/kuyanov/lemmatheca", home.hrefs)
        self.assertIn("/areas/logic-and-foundations/", home.hrefs)
        self.assertNotIn("/nodes/", home.hrefs)
        self.assertEqual(self.client.get("/nodes/").status_code, 404)
        area = self.page(self.client.get(
            "/areas/logic-and-foundations/set-theory/"))
        self.assertIn(reverse("catalog:entry", args=[
                      "sets-and-maps"]), area.hrefs)
        for identifier in ("sets-and-maps", "equivalence-relations", "ordered-sets"):
            entry = load_entry(identifier)
            response = self.client.get(f"/entries/{identifier}/")
            page = self.page(response)
            self.assertIn(entry["title"], page.root.text)
            for link in page.find_all("a"):
                # Link text may contain nested markup, icons, or an accessible label.
                self.assertTrue(link.text or link.attrs.get("aria-label") or
                                any(target in page.ids for target in link.attrs.get("aria-labelledby", "").split()) or
                                any(image.attrs.get("alt") and link in image.ancestors()
                                    for image in page.find_all("img")), link.attrs)
            self.assertTrue(any(element.attrs.get("src", "").startswith(f"/static/entries/{identifier}/")
                                for element in page.elements))
            for block in entry["blocks"]:
                self.assertIn(block["id"], page.ids)
                for node in block["formal_ids"] or []:
                    self.assertIn(
                        reverse("catalog:node", args=[node]), page.hrefs)
        page = self.page(self.client.get("/entries/ordered-sets/"))
        self.assertTrue(any(
            link.path == "/entries/sets-and-maps/" and link.fragment == "pairs-and-relations"
            and parse_qs(link.query) == {"from": ["ordered-sets"], "at": ["partial-and-total-orders"]}
            for link in map(urlsplit, page.hrefs)))
        for identifier in ("set", "set-subset-transitive", "order-equality"):
            self.assertEqual(self.client.get(
                f"/node/{identifier}/").status_code, 200)

    def test_missing_records_and_read_only_views(self):
        for url in ["/entries/missing/", "/node/missing/", "/api/node/missing/",
                    "/areas/set-theory/", "/areas/missing/"]:
            self.assertEqual(self.client.get(url).status_code, 404)
        for url in ["/", "/areas/logic-and-foundations/", "/entries/sets-and-maps/",
                    "/node/set/", "/api/node/", "/api/node/set/"]:
            self.assertEqual(self.client.post(url).status_code, 405)

    def test_contextual_navigation_and_question_return(self):
        response = self.client.get(
            "/entries/sets-and-maps/?from=ordered-sets&at=partial-and-total-orders")
        self.assertEqual(
            response.context["return_url"], "/entries/ordered-sets/#partial-and-total-orders")
        self.assertIn(response.context["return_url"],
                      self.page(response).hrefs)
        self.assertEqual(
            response.context["next_entry"]["id"], "equivalence-relations")
        response = self.client.get(
            "/entries/sets-and-maps/?from=sets-and-maps&at=image-intersection-question")
        self.assertEqual(response.context["return_url"],
                         "/entries/sets-and-maps/?answer=image-intersection-question#image-intersection-question")
        self.assertIn(response.context["return_url"],
                      self.page(response).hrefs)
        answer = self.client.get(
            "/entries/sets-and-maps/?answer=image-intersection-question")
        answer_page = self.page(answer)
        answers = [element for element in answer_page.find_all("details")
                   if any(parent.attrs.get("id") == "image-intersection-question"
                          for parent in element.ancestors()) and "open" in element.attrs]
        self.assertEqual(len(answers), 1)
        self.assertTrue(any(answers[0] in element.ancestors() and element.text
                            for element in answer_page.find_all("summary")))
        ordinary = self.client.get("/entries/sets-and-maps/")
        question_details = [element for element in self.page(ordinary).find_all("details")
                            if any(parent.attrs.get("id") == "image-intersection-question"
                                   for parent in element.ancestors())]
        self.assertTrue(question_details)
        self.assertFalse(
            any("open" in element.attrs for element in question_details))
        self.assertEqual(
            ordinary.context["return_url"], "/areas/logic-and-foundations/set-theory/")

    def test_tables_have_captions_and_keyboard_accessible_scrolling(self):
        page = self.page(self.client.get("/entries/sets-and-maps/"))
        tables = page.find_all("table")
        self.assertTrue(tables)
        for table in tables:
            self.assertTrue(any(table in caption.ancestors() and caption.text
                                for caption in page.find_all("caption")))
            self.assertTrue(any(parent.attrs.get("tabindex") == "0"
                                and parent.attrs.get("role") == "region"
                                and (parent.attrs.get("aria-label") or parent.attrs.get("aria-labelledby"))
                                for parent in table.ancestors()))

    def test_saved_entry_summaries_match_current_block_bindings_and_node_results(self):
        for identifier in ("sets-and-maps", "equivalence-relations", "ordered-sets"):
            with self.subTest(entry=identifier):
                saved = read_entry_metadata(identifier)["formalization"]
                self.assertEqual(saved, add_progress(
                    load_entry(identifier))["formalization"])
                response = self.client.get(
                    reverse("catalog:entry", args=[identifier]))
                page = self.page(response)
                self.assertEqual(
                    response.context["entry"]["formalization"], saved)
                self.assertIn(saved["label"], page.root.text)

    def test_node_declarations_and_source_links_do_not_run_lean(self):
        identifier = "nat-membership-and-inclusion-example"
        node = read_node(identifier)
        for target in (identifier, "set-subset-transitive"):
            record = read_node(target)
            with patch("subprocess.run", side_effect=AssertionError("Page requests must not run Lean")):
                response = self.client.get(
                    reverse("catalog:node", args=[target]))
            page = self.page(response)
            self.assertIn(record["declaration"], page.root.text)
            self.assertEqual(
                response.context["node"]["verified"], record["verified"])
            self.assert_source_link(response, record)
        api = self.client.get(f"/api/node/{identifier}/").json()
        self.assertEqual(api["url"], reverse(
            "catalog:node", args=[identifier]))
        self.assertEqual(reverse("catalog:node_detail", args=[
                         identifier]), f"/api/node/{identifier}/")
        self.assertIn(api, self.client.get(
            reverse("catalog:node_list")).json()["nodes"])
        self.assertEqual(api["verified"], node["verified"])
        self.assertNotIn("status", api)
        self.assertNotIn("source_module", api)
        self.assertEqual(api["module"], node["module"])

    def test_verification_flag_controls_pages_and_entry_progress(self):
        with TemporaryDirectory() as directory:
            corpus = Path(directory) / "corpus"
            shutil.copytree(settings.CORPUS_DIR, corpus)
            path = corpus / "nodes/set.json"
            node = read_json(path)
            with override_settings(CORPUS_DIR=corpus):
                write_json(path, {**node, "verified": True})
                verified_page = self.page(self.client.get("/node/set/"))
                before = add_progress(load_entry(
                    "sets-and-maps"))["formalization"]
                write_json(path, {**node, "verified": False})
                response = self.client.get("/node/set/")
                self.assert_source_link(response, node)
                self.assertFalse(response.context["node"]["verified"])
                self.assertNotEqual(verified_page.root.text,
                                    self.page(response).root.text)
                self.assertFalse(self.client.get(
                    "/api/node/set/").json()["verified"])
                after = add_progress(load_entry(
                    "sets-and-maps"))["formalization"]
                self.assertEqual(after["complete"], before["complete"] - 1)
                self.assertEqual(after["total"], before["total"])
                entry = self.client.get("/entries/sets-and-maps/")
                self.assertEqual(entry.status_code, 200)
                self.assertEqual(
                    entry.context["entry"]["formalization"], after)
                self.assertTrue(any(record["id"] == "set" and not record["verified"]
                                    for block in entry.context["entry"]["blocks"]
                                    for record in block["formal_nodes"]))
                write_json(
                    path, {"id": "set", "description": "A set.", "verified": False})
                response = self.client.get("/node/set/")
                self.assertEqual(response.status_code, 200)
                self.assertFalse(response.context["node"]["verified"])
                self.assertIsNone(response.context["node"].get("declaration"))
                self.assertIsNone(response.context["node"]["source"])

    def test_corpus_has_only_verification_status_and_no_review_command(self):
        self.assertNotIn("review", get_commands())
        self.assertIs(type(read_node("set")["verified"]), bool)

    def test_reader_does_not_repeat_offline_content_or_asset_checks(self):
        with patch("catalog.validation.checked_source", side_effect=AssertionError("Offline check")), \
                patch("catalog.entry_files.is_local_asset", side_effect=AssertionError("Asset stat")):
            response = self.client.get("/entries/sets-and-maps/")
            self.assertEqual(response.status_code, 200)
            self.assertEqual(response.context["entry"]["id"], "sets-and-maps")
