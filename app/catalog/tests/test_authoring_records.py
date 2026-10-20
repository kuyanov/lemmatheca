"""Authoring-register navigation reads only narrowed records, without Lean/index."""

from contextlib import contextmanager
from io import StringIO
from pathlib import Path
from tempfile import TemporaryDirectory
from unittest.mock import patch

from django.core.management import call_command
from django.test import SimpleTestCase, override_settings

from catalog.authoring_records import (
    build_planning_index, build_source_index, planning_catalog, source_catalog,
    write_authoring_indexes,
)
from catalog.files import read_json, write_json


class AuthoringRecordTests(SimpleTestCase):
    def setUp(self):
        temporary = TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.corpus = Path(temporary.name)
        for directory in ("source-errors/sources", "source-errors/findings", "reference-planning/records"):
            (self.corpus / directory).mkdir(parents=True)
        self.sources = {
            "alpha": {"id": "alpha", "publication": "Alpha's arithmetic notes (2025)",
                      "urls": ["https://example.com/alpha#chapter"], "entry_refs": ["arithmetic#start"],
                      "finding_ids": ["ERR-1"], "reviews": [{"checked_passages": "Chapter 1.",
                          "consumers": "Arithmetic.", "outcome": "Repaired.", "checked_on": "2026-10-20"}]},
            "beta": {"id": "beta", "publication": "Beta's tree notes (2024)",
                     "urls": ["https://example.com/beta"], "entry_refs": ["trees"],
                     "finding_ids": ["ERR-2"], "reviews": [{"checked_passages": "Chapter 2.",
                         "consumers": "Trees.", "outcome": "Local typo.", "checked_on": "2026-10-20"}]},
        }
        self.findings = {
            "ERR-1": {"id": "ERR-1", "title": "A serious arithmetic error", "source_ids": ["alpha"],
                      "severity": "serious", "details": "An incorrect bound.",
                      "entry_refs": ["proofs#bound"], "related_findings": []},
            "ERR-2": {"id": "ERR-2", "title": "A local typo", "source_ids": ["beta"],
                      "severity": "local", "details": "A reversed symbol.", "entry_refs": ["trees"],
                      "related_findings": []},
        }
        self.plans = {
            "arithmetic-proof": {"id": "arithmetic-proof", "kind": "upcoming-reference",
                                 "title": "Arithmetic proof reference", "areas": ["mathematical-logic"],
                                 "entry_refs": ["arithmetic#start"], "urls": ["https://example.com/alpha"],
                                 "planned_entry_ids": ["future-arithmetic"],
                                 "details": "Use induction in a future proof."},
            "trees-plan": {"id": "trees-plan", "kind": "area-plan", "title": "Trees plan",
                           "areas": ["set-theory"], "entry_refs": ["trees"], "urls": [],
                           "details": "More on trees."},
        }
        for kind, records, directory in (("source", self.sources, "source-errors/sources"),
                                         ("finding", self.findings, "source-errors/findings"),
                                         ("plan", self.plans, "reference-planning/records")):
            for key, record in records.items():
                write_json(self.corpus / directory / f"{key}.json", record)
        write_authoring_indexes(self.corpus)
        override = override_settings(CORPUS_DIR=self.corpus, CORPUS_INDEX_PATH=self.corpus / "missing-main-index.json")
        override.enable()
        self.addCleanup(override.disable)

    def get(self, path, parameters=None, status=200):
        response = self.client.get(path, parameters or {})
        self.assertEqual(response.status_code, status, response.content)
        return response.json()

    @contextmanager
    def reads(self):
        opened = []
        original = Path.open

        def tracked(path, *args, **kwargs):
            opened.append(path)
            return original(path, *args, **kwargs)

        with patch.object(Path, "open", tracked), patch("subprocess.run", side_effect=AssertionError("No subprocess")):
            yield opened

    def test_catalogs_are_reproducible_and_command_replaces_stale_catalogs(self):
        self.assertEqual(source_catalog(self.sources, self.findings), build_source_index(self.corpus))
        self.assertEqual(planning_catalog(self.plans), build_planning_index(self.corpus))
        sources = read_json(self.corpus / "source-errors/index.json")
        self.assertEqual(sources["by_entry"]["proofs"], ["alpha"])
        self.assertEqual(sources["by_url"]["https://example.com/alpha"], ["alpha"])
        (self.corpus / "source-errors/index.json").write_text("broken")
        output = StringIO()
        call_command("index_authoring_records", stdout=output)
        self.assertIn("2 sources, 2 findings, and 2 planning records", output.getvalue())
        self.assertEqual(read_json(self.corpus / "source-errors/index.json"), sources)

    def test_rebuild_leaves_unchanged_catalogs_untouched(self):
        with patch("catalog.authoring_records.write_json", wraps=write_json) as writes:
            write_authoring_indexes(self.corpus)
        writes.assert_not_called()
        source = self.sources["alpha"]
        source["urls"].append("https://example.com/alias")
        write_json(self.corpus / "source-errors/sources/alpha.json", source)
        with patch("catalog.authoring_records.write_json", wraps=write_json) as writes:
            write_authoring_indexes(self.corpus)
        self.assertEqual(writes.call_count, 1)
        self.assertEqual(writes.call_args.args[0], self.corpus / "source-errors/index.json")

    def test_filters_intersect_catalog_keys_before_opening_records(self):
        with self.reads() as reads:
            result = self.get("/api/source-errors/sources/", {
                "entry_id": "proofs", "url": "https://example.com/alpha#different", "q": "ALPHA arithmetic",
            })
        self.assertEqual([record["id"] for record in result["results"]], ["alpha"])
        self.assertNotIn(self.corpus / "source-errors/sources/beta.json", reads)
        self.assertNotIn("reviews", result["results"][0])
        with self.reads() as reads:
            plans = self.get("/api/reference-planning/", {"area": "mathematical-logic",
                             "kind": "upcoming-reference", "entry_id": "arithmetic", "q": "future induction"})
        self.assertEqual([record["id"] for record in plans["results"]], ["arithmetic-proof"])
        self.assertNotIn(self.corpus / "reference-planning/records/trees-plan.json", reads)
        self.assertNotIn("details", plans["results"][0])
        self.assertEqual(self.get("/api/reference-planning/", {"entry_id": "future-arithmetic"})["count"], 1)
        self.assertEqual(self.get("/api/reference-planning/", {"q": "future missing"})["count"], 0)

    def test_planned_entry_lookup_accepts_core_corpus_id_lengths(self):
        entry_id = "future-" + "a" * 140
        record = {**self.plans["trees-plan"], "planned_entry_ids": [entry_id]}
        write_json(self.corpus / "reference-planning/records/trees-plan.json", record)
        write_authoring_indexes(self.corpus)
        result = self.get("/api/reference-planning/", {"entry_id": entry_id})
        self.assertEqual([item["id"] for item in result["results"]], ["trees-plan"])

    def test_findings_filter_by_affected_entry_severity_and_source(self):
        result = self.get("/api/source-errors/findings/", {
            "entry_id": "proofs", "severity": "serious", "source_id": "alpha", "q": "incorrect bound",
        })
        self.assertEqual([record["id"] for record in result["results"]], ["ERR-1"])
        # A source's coverage does not imply every finding affects that entry.
        self.assertEqual(self.get("/api/source-errors/findings/", {"entry_id": "arithmetic"})["count"], 0)
        self.assertEqual(self.get("/api/source-errors/findings/", {"source_id": "missing"})["count"], 0)
        self.assertNotIn("details", result["results"][0])

    def test_pagination_reads_only_the_requested_page_without_text_filters(self):
        with self.reads() as reads:
            result = self.get("/api/source-errors/sources/", {"limit": 1, "offset": 1})
        self.assertEqual((result["count"], result["limit"], result["offset"]), (2, 1, 1))
        self.assertEqual([record["id"] for record in result["results"]], ["beta"])
        self.assertNotIn(self.corpus / "source-errors/sources/alpha.json", reads)
        self.assertEqual(self.get("/api/source-errors/sources/", {"offset": 9})["results"], [])

    def test_exact_record_lookup_is_index_free_and_reads_one_file(self):
        (self.corpus / "source-errors/index.json").unlink()
        (self.corpus / "reference-planning/index.json").unlink()
        for path, expected in (("/api/source-errors/sources/alpha/", self.sources["alpha"]),
                               ("/api/source-errors/findings/ERR-1/", self.findings["ERR-1"]),
                               ("/api/reference-planning/arithmetic-proof/", self.plans["arithmetic-proof"])):
            with self.subTest(path=path), self.reads() as reads:
                self.assertEqual(self.get(path), expected)
                self.assertEqual(len(reads), 1)
        self.get("/api/source-errors/sources/", status=503)
        self.get("/api/source-errors/sources/missing/", status=404)

    def test_invalid_queries_ids_and_methods_are_rejected(self):
        for path, params in (("/api/source-errors/sources/", {"entry_id": "../outside"}),
                             ("/api/source-errors/sources/", {"q": " "}),
                             ("/api/source-errors/sources/", {"q": "x" * 201}),
                             ("/api/source-errors/sources/", {"url": "not-a-url"}),
                             ("/api/source-errors/sources/", {"limit": 0}),
                             ("/api/source-errors/sources/", {"offset": -1}),
                             ("/api/reference-planning/", {"kind": ""}),
                             ("/api/source-errors/findings/", {"severity": "minor"}),
                             ("/api/source-errors/sources/alpha/", {"q": "alpha"}),
                             ("/api/source-errors/sources/bad..id/", {}),
                             ("/api/reference-planning/", {"unknown": "x"})):
            with self.subTest(path=path, params=params):
                self.get(path, params, status=400)
        self.get("/api/source-errors/sources/?entry_id=alpha&entry_id=beta", status=400)
        self.assertEqual(self.client.post("/api/reference-planning/").status_code, 405)
        self.assertEqual(self.client.head("/api/reference-planning/").status_code, 200)

    def test_malformed_records_and_catalogs_are_service_errors(self):
        path = self.corpus / "source-errors/sources/alpha.json"
        for contents in ("[]", '{"id":"wrong"}', "invalid JSON"):
            path.write_text(contents)
            self.get("/api/source-errors/sources/alpha/", status=503)
            self.get("/api/source-errors/sources/", {"entry_id": "arithmetic"}, status=503)
        write_json(path, self.sources["alpha"])
        for index in ({}, {"schema_version": 1, "sources": ["../outside"]}):
            write_json(self.corpus / "source-errors/index.json", index)
            self.get("/api/source-errors/sources/", status=503)

    def test_requests_are_read_only(self):
        before = {path: path.read_bytes() for path in self.corpus.rglob("*") if path.is_file()}
        for path in ("/api/source-errors/sources/", "/api/source-errors/findings/", "/api/reference-planning/"):
            self.get(path)
        after = {path: path.read_bytes() for path in self.corpus.rglob("*") if path.is_file()}
        self.assertEqual(before, after)
