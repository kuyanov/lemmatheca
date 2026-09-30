"""A page must not scan or depend on unrelated corpus records."""

from collections import Counter
from contextlib import contextmanager
from pathlib import Path
from tempfile import TemporaryDirectory
from unittest.mock import patch

from django.test import SimpleTestCase, override_settings

from catalog.entry_files import read_entry, read_entry_metadata
from catalog.files import write_json
from catalog.node_files import read_node
from catalog.progress import entry_progress

from .html import HTML


class LocalReadTests(SimpleTestCase):
    def setUp(self):
        temporary = TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.corpus = Path(temporary.name)
        settings = override_settings(CORPUS_DIR=self.corpus)
        settings.enable()
        self.addCleanup(settings.disable)
        (self.corpus / "nodes").mkdir()
        self.statistics = {
            "entries": 3, "verified_entries": 1, "nodes": 23,
            "verified_nodes": 17, "contributors": 19,
        }
        write_json(self.corpus / "statistics.json", self.statistics)
        write_json(self.corpus / "taxonomy.json", {"areas": [
            {"id": "root", "title": "Root", "parent": None},
            {"id": "first", "title": "First", "parent": "root"},
            {"id": "second", "title": "Second", "parent": "root"},
        ]})
        write_json(self.corpus / "area_entries.json", {"areas": {
            "first": ["alpha", "next"], "second": ["remote"],
        }})
        for identifier, area, formal, body in [
            ("alpha", "first", "proof",
             '<a href="remote#fact"></a><a href="remote#fact">Again</a>'),
            ("next", "first", "proof", "Next."),
            ("remote", "second", "unrelated",
             '<a href="unrelated#fact">Not followed transitively</a>'),
        ]:
            directory = self.corpus / "entries" / identifier
            directory.mkdir(parents=True)
            write_json(directory / "entry.json", {
                "id": identifier, "title": identifier.title(), "primary_area": area,
                "summary": identifier, "reading_time": 5,
                "formalization": entry_progress(
                    [{"formal_ids": [formal]}], {formal: {"verified": True}}),
            })
            (directory / "entry.html").write_text(
                f'<section id="fact" data-kind="lemma" data-formal="{formal}">'
                f'<h2>{identifier.title()} fact</h2><p>{body}</p></section>')
        for identifier, dependencies in [("proof", ["hint"]), ("hint", ["unrelated"])]:
            write_json(self.corpus / "nodes" / f"{identifier}.json", {
                "id": identifier, "description": identifier, "verified": True,
                "dependencies": dependencies,
            })
        # Broken, unlisted files must not break otherwise valid pages.
        (self.corpus / "nodes/unrelated.json").write_text("not JSON")
        directory = self.corpus / "entries/unrelated"
        directory.mkdir()
        (directory / "entry.json").write_text("not JSON")
        (directory / "entry.html").write_text("not an entry")

    @contextmanager
    def only_reads(self, *allowed):
        reads = Counter()
        original_open = Path.open

        def opened(path, *args, **kwargs):
            if path.is_relative_to(self.corpus):
                relative = path.relative_to(self.corpus).as_posix()
                self.assertIn(relative, allowed,
                              f"Unrelated corpus read: {relative}")
                reads[relative] += 1
            return original_open(path, *args, **kwargs)

        with patch.object(Path, "open", opened), \
                patch.object(Path, "glob", side_effect=AssertionError("A detail page must not scan the corpus")):
            yield reads

    def test_metadata_and_record_reads_are_direct(self):
        with self.only_reads("entries/alpha/entry.json") as reads:
            self.assertEqual(read_entry_metadata("alpha")["title"], "Alpha")
        self.assertEqual(reads.total(), 1)
        with self.only_reads("entries/alpha/entry.json", "entries/alpha/entry.html"):
            self.assertIn("Alpha fact", read_entry("alpha")["source"])
        with self.only_reads("nodes/proof.json"):
            self.assertTrue(read_node("proof")["verified"])

    def test_home_and_parent_area_read_only_navigation_and_statistics(self):
        with self.only_reads("taxonomy.json", "area_entries.json", "statistics.json") as reads, \
                patch("subprocess.run", side_effect=AssertionError("No Git or Lean in requests")):
            home = self.client.get("/")
            self.assertEqual(home.status_code, 200)
            self.assertEqual(home.context["statistics"], self.statistics)
            page = HTML.from_response(home)
            for count in self.statistics.values():
                self.assertRegex(page.root.text, rf"\b{count}\b")
            self.assertEqual(home.context["areas"][0]["entry_count"], 3)
            self.assertEqual(home.context["area_count"], 3)
        self.assertEqual(reads.total(), 3)
        with self.only_reads("taxonomy.json", "area_entries.json"):
            area = self.client.get("/areas/root/")
            self.assertEqual(area.status_code, 200)
            self.assertEqual([item["entry_count"]
                             for item in area.context["areas"]], [2, 1])

    def test_home_handles_an_unbuilt_or_empty_corpus_snapshot(self):
        (self.corpus / "statistics.json").unlink()
        response = self.client.get("/")
        self.assertEqual(response.status_code, 200)
        self.assertEqual(
            response.context["statistics"], dict.fromkeys(self.statistics))
        empty = dict.fromkeys(self.statistics, 0)
        write_json(self.corpus / "statistics.json", empty)
        response = self.client.get("/")
        self.assertEqual(response.status_code, 200)
        self.assertEqual(response.context["statistics"], empty)

    def test_area_reads_only_indexed_metadata_without_html_or_nodes(self):
        with self.only_reads("taxonomy.json", "area_entries.json",
                             "entries/alpha/entry.json", "entries/next/entry.json") as reads:
            response = self.client.get("/areas/root/first/")
            self.assertEqual(response.status_code, 200)
            self.assertEqual([item["id"] for item in response.context["entries"]], [
                             "alpha", "next"])
            self.assertTrue(all(entry["formalization"]["status"] == "complete"
                                for entry in response.context["entries"]))
        self.assertTrue(all(count == 1 for count in reads.values()))

    def test_entry_reads_references_once_without_their_nodes_or_transitive_links(self):
        with self.only_reads("taxonomy.json", "area_entries.json", "nodes/proof.json",
                             "entries/alpha/entry.json", "entries/alpha/entry.html",
                             "entries/remote/entry.json", "entries/remote/entry.html",
                             "entries/next/entry.json") as reads:
            response = self.client.get("/entries/alpha/?from=remote&at=fact")
            self.assertEqual(response.status_code, 200)
            self.assertEqual(response.context["return_entry"]["id"], "remote")
            self.assertEqual(
                response.context["return_url"], "/entries/remote/#fact")
            self.assertEqual(response.context["next_entry"]["id"], "next")
            self.assertEqual(
                response.context["entry"]["formalization"]["percent"], 100)
        self.assertTrue(all(count == 1 for count in reads.values()))

    def test_node_page_reads_only_node_and_direct_hints_and_api_only_node(self):
        with self.only_reads("nodes/proof.json", "nodes/hint.json") as reads:
            response = self.client.get("/node/proof/")
            self.assertEqual(response.status_code, 200)
            self.assertTrue(response.context["node"]["verified"])
            self.assertEqual(
                [node["id"] for node in response.context["dependencies"]], ["hint"])
        self.assertEqual(reads, {"nodes/proof.json": 1, "nodes/hint.json": 1})
        with self.only_reads("nodes/proof.json") as reads:
            self.assertTrue(self.client.get(
                "/api/node/proof/").json()["verified"])
        self.assertEqual(reads.total(), 1)
        write_json(self.corpus / "nodes/proof.json",
                   {"id": "proof", "verified": False})
        self.assertFalse(self.client.get(
            "/api/node/proof/").json()["verified"])

    def test_invalid_identifiers_never_open_files(self):
        with patch.object(Path, "open", side_effect=AssertionError("Invalid ID reached the filesystem")):
            for identifier in ("..", "../outside", "/tmp/outside", "a/b", "a\\b", "", None):
                for read in (read_entry, read_entry_metadata, read_node):
                    with self.subTest(identifier=identifier, read=read.__name__):
                        with self.assertRaises(FileNotFoundError):
                            read(identifier)

    def test_missing_and_invalid_queries_still_fall_back_to_area(self):
        for source in ("missing", "../../outside"):
            response = self.client.get("/entries/alpha/", {"from": source})
            self.assertEqual(
                response.context["return_url"], "/areas/root/first/")
        for url in ("/entries/missing/", "/node/missing/", "/api/node/../"):
            self.assertEqual(self.client.get(url).status_code, 404)
