"""Indexed authoring requests stay read-only and read metadata from the corpus."""

from collections import Counter
from contextlib import contextmanager
import json
from pathlib import Path
from tempfile import TemporaryDirectory
from unittest.mock import patch
from weakref import WeakValueDictionary

from django.test import SimpleTestCase, override_settings

from catalog.corpus_index import write_index
from catalog.entry_text import clear_text_cache, text_cache_info
from catalog.files import read_json, write_json
from catalog.index_reader import clear_index_cache
from catalog.node_files import read_node
from catalog.queries import CorpusQuery


class IndexedAPITests(SimpleTestCase):
    def setUp(self):
        temporary = TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.repository = Path(temporary.name)
        self.corpus = self.repository / "corpus"
        self.cache = self.corpus / "index.json"
        (self.corpus / "nodes").mkdir(parents=True)
        write_json(self.corpus / "taxonomy.json", {"areas": [
            {"id": "root", "title": "Root", "parent": None, "description": "Root."},
            {"id": "first", "title": "First", "parent": "root", "description": "First."},
            {"id": "second", "title": "Second", "parent": "root", "description": "Second."},
        ]})
        write_json(self.corpus / "area_entries.json", {"areas": {
            "first": ["beta", "alpha"], "second": ["remote"],
        }})
        for identifier, verified, module, declaration in [
            ("proof", True, "Lemmatheca.Shared", "Example.proof"),
            ("other", False, "Lemmatheca.Other", "Example.other"),
            ("unused", True, "Lemmatheca.Unused", "Example.unused"),
            ("unbound", False, None, None),
        ]:
            record = {"id": identifier, "description": f"Description of {identifier}.",
                      "verified": verified, "dependencies": []}
            if module:
                record.update(module=module, declaration=declaration)
            write_json(self.corpus / "nodes" / f"{identifier}.json", record)
        self.add_entry("alpha", "first", '''
            <section id="question" data-kind="question" data-formal="proof other">
              <h2>Diagonal question</h2><p>A diagonal argument.</p>
              <a href="beta#fact">Earlier fact</a>
              <a href="#local">Nearby anchor</a>
              <a href="#question">Same question</a>
              <span id="local">Nested target.</span>
              <a href="https://example.com/">External source</a>
              <details class="question-answer"><summary>Show answer</summary>
                <p>A hidden witness.</p><a href="beta#fact">Earlier fact again</a>
              </details>
            </section>
            <section id="repeat" data-kind="lemma" data-formal="proof">
              <h2>Repeated binding</h2><p>A consequence.</p>
            </section>
            <section id="empty" data-kind="lemma" data-formal="">
              <h2>Empty mapping</h2><p>No formal content.</p>
            </section>
            <section id="planned" data-kind="lemma">
              <h2>Unplanned mapping</h2><p>A future argument.</p>
            </section>''')
        self.add_entry("beta", "first", '''
            <section id="fact" data-kind="lemma" data-formal="proof">
              <h2>A fact</h2><p>An elementary fact.</p>
            </section>''')
        self.add_entry("remote", "second", '''
            <section id="fact" data-kind="lemma" data-formal="other">
              <h2>Remote fact</h2><p>A remote argument.</p>
            </section>''')
        self.revision = write_index(self.corpus, self.cache)["revision"]
        configuration = override_settings(CORPUS_DIR=self.corpus, CORPUS_INDEX_PATH=self.cache)
        configuration.enable()
        self.addCleanup(configuration.disable)
        clear_index_cache()
        self.addCleanup(clear_index_cache)
        clear_text_cache()
        self.addCleanup(clear_text_cache)

    def add_entry(self, identifier, area, source):
        directory = self.corpus / "entries" / identifier
        directory.mkdir(parents=True)
        write_json(directory / "entry.json", {
            "id": identifier, "title": identifier.title(), "primary_area": area,
            "additional_areas": [], "based_on": [], "reading_time": 5,
            "summary": "Summary.", "abstract": f"Abstract for {identifier}.",
        })
        (directory / "entry.html").write_text(source, encoding="utf-8")

    def get(self, path, params=None):
        response = self.client.get(path, params or {})
        self.assertEqual(response.status_code, 200, response.content)
        payload = response.json()
        self.assertEqual(payload["index_revision"], self.revision)
        self.assertEqual(payload["metadata_source"], "live_corpus")
        return payload

    def assert_error(self, path, params, status, code=None):
        response = self.client.get(path, params)
        self.assertEqual(response.status_code, status, response.content)
        error = response.json()["error"]
        self.assertIsInstance(error["message"], str)
        self.assertTrue(error["message"])
        if code:
            self.assertEqual(error["code"], code)
        return response

    @contextmanager
    def track_reads(self, *, allow_html=False):
        reads = Counter()
        original_open = Path.open

        def opened(path, *args, **kwargs):
            mode = args[0] if args else kwargs.get("mode", "r")
            if "r" in mode:
                reads[path] += 1
                if not allow_html:
                    self.assertNotEqual(path.suffix, ".html", "This query must not read HTML")
            return original_open(path, *args, **kwargs)

        with patch.object(Path, "open", opened), \
                patch("subprocess.run", side_effect=AssertionError("No Lean or Git in requests")):
            yield reads

    def test_context_selects_blocks_answers_and_reading_neighbors(self):
        with self.track_reads(allow_html=True) as reads:
            result = self.get("/api/entries/alpha/context/", {"limit": 2, "offset": 1})
        self.assertEqual({path.parent.name for path in reads if path.suffix == ".html"}, {"alpha"})
        self.assertEqual(result["entry"]["title"], "Alpha")
        self.assertEqual(result["blocks"]["count"], 4)
        self.assertEqual([block["key"] for block in result["blocks"]["results"]],
                         ["alpha#repeat", "alpha#empty"])
        self.assertEqual(result["navigation"]["previous"]["id"], "beta")
        self.assertIsNone(result["navigation"]["next"])
        self.assertNotIn("nodes", result)
        self.assertNotIn("references", result)
        full = self.get("/api/entries/alpha/context/")
        self.assertIn("hidden witness", full["blocks"]["results"][0]["answer_text"])
        without = self.get("/api/entries/alpha/context/", {"include_answers": "false"})
        self.assertNotIn("hidden witness", str(without))

    def test_context_block_selection_uses_entry_order_before_pagination(self):
        result = self.get("/api/entries/alpha/context/", {
            "block_ids": "planned,question,repeat,question", "limit": 1, "offset": 1,
        })
        self.assertEqual(result["block_ids"], ["question", "repeat", "planned"])
        self.assertEqual(result["blocks"]["count"], 3)
        self.assertEqual([block["key"] for block in result["blocks"]["results"]],
                         ["alpha#repeat"])
        self.assertEqual(result["blocks"]["offset"], 1)
        self.assertEqual(result["entry"]["abstract"], "Abstract for alpha.")
        self.assertEqual(result["navigation"]["previous"]["id"], "beta")
        self.assertIsNone(result["navigation"]["next"])
        answer = self.get("/api/entries/alpha/context/", {"block_ids": "question"})
        self.assertIn("hidden witness", answer["blocks"]["results"][0]["answer_text"])
        self.assertNotIn("block_ids", self.get("/api/entries/alpha/context/"))

    def test_context_selection_scopes_nodes_and_coverage_without_returning_blocks(self):
        result = self.get("/api/entries/alpha/context/", {
            "block_ids": "repeat,question", "include": "nodes,coverage", "limit": 1, "offset": 1,
        })
        self.assertNotIn("blocks", result)
        self.assertEqual(result["nodes"]["count"], 2)
        self.assertEqual([node["id"] for node in result["nodes"]["results"]], ["other"])
        coverage = result["coverage"]
        self.assertEqual(set(coverage["nodes"]), {"proof", "other"})
        entry = coverage["entries"][0]
        self.assertEqual([block["id"] for block in entry["blocks"]], ["question", "repeat"])
        self.assertEqual(entry["formalization"]["total"], 2)
        self.assertEqual(entry["formalization"]["complete"], 1)
        self.assertEqual(entry["formalization"]["unplanned"], 0)
        with self.track_reads(allow_html=True) as reads:
            states = self.get("/api/entries/alpha/context/", {
                "block_ids": "planned,empty", "include": "nodes,coverage",
            })
        self.assertFalse(any(path.parent == self.corpus / "nodes" for path in reads))
        self.assertEqual(states["nodes"]["count"], 0)
        self.assertEqual(states["coverage"]["nodes"], {})
        self.assertEqual([(block["id"], block["formal_ids"], block["formalization"]["status"])
                          for block in states["coverage"]["entries"][0]["blocks"]], [
            ("empty", [], "not_applicable"), ("planned", None, "not_started"),
        ])

    def test_context_selected_references_union_owned_anchors_and_deduplicate_self_edges(self):
        alpha = self.corpus / "entries/alpha/entry.html"
        alpha.write_text(alpha.read_text().replace(
            '<h2>Repeated binding</h2>', '<h2>Repeated binding</h2>'
            '<a href="#question">Back to question</a><a href="beta#fact">Another fact</a>').replace(
            '<h2>Empty mapping</h2>',
            '<h2>Empty mapping</h2><a href="#local">Nested question anchor</a>'))
        beta = self.corpus / "entries/beta/entry.html"
        beta.write_text(beta.read_text().replace(
            '</section>', '<a href="alpha#repeat">Repeated block</a></section>'))
        self.revision = write_index(self.corpus, self.cache)["revision"]
        params = {"block_ids": "repeat,question", "include": "references"}
        result = self.get("/api/entries/alpha/context/", params)
        self.assertNotIn("blocks", result)
        references = result["references"]
        self.assertEqual(references["count"], 8)
        self.assertEqual(len({edge["id"] for edge in references["results"]}), 8)
        self.assertEqual(Counter((edge["source"], edge["target"])
                                 for edge in references["results"]), Counter({
            ("alpha#question", "beta#fact"): 2,
            ("alpha#question", "alpha#local"): 1,
            ("alpha#question", "alpha#question"): 1,
            ("alpha#repeat", "alpha#question"): 1,
            ("alpha#repeat", "beta#fact"): 1,
            ("alpha#empty", "alpha#local"): 1,
            ("beta#fact", "alpha#repeat"): 1,
        }))
        page = self.get("/api/entries/alpha/context/", {**params, "limit": 2, "offset": 1})
        self.assertEqual(page["references"]["count"], 8)
        self.assertEqual(page["references"]["results"], references["results"][1:3])
        visible = self.get("/api/entries/alpha/context/", {**params, "include_answers": "false"})
        self.assertEqual(visible["references"]["count"], 7)
        self.assertFalse(any(edge["in_answer"] for edge in visible["references"]["results"]))

    def test_context_block_selectors_reject_invalid_and_non_block_targets(self):
        path = "/api/entries/alpha/context/"
        for value in ["", " ", ",", "question,", "question,,repeat", "alpha#question",
                      "../question", ",".join(["question"] * 101)]:
            with self.subTest(value=value):
                self.assert_error(path, {"block_ids": value}, 400)
        for value in ["missing", "local", "fact"]:
            with self.subTest(value=value):
                self.assert_error(path, {"block_ids": value}, 404)
        for include in ["", "navigation"]:
            with self.subTest(include=include):
                self.assert_error(path, {"block_ids": "question", "include": include}, 400)
        self.assert_error(path + "?block_ids=question&block_ids=repeat", {}, 400)
        maximum = self.get(path, {"block_ids": ",".join(["question"] * 100)})
        self.assertEqual(maximum["block_ids"], ["question"])
        query = CorpusQuery(read_json(self.cache), self.corpus)
        for value in [[], "question", [None], [1], ["question", ""]]:
            with self.subTest(value=value), self.assertRaises(ValueError):
                query.get_entry_context("alpha", block_ids=value)

    def test_context_selection_still_detects_stale_excluded_blocks(self):
        source = self.corpus / "entries/alpha/entry.html"
        source.write_text(source.read_text().replace('id="planned"', 'id="renamed"'))
        for include in ["blocks", "nodes", "references", "coverage"]:
            with self.subTest(include=include):
                self.assert_error("/api/entries/alpha/context/", {
                    "block_ids": "question", "include": include,
                }, 409, "index_outdated")

    def test_context_resolves_internal_links_inline_without_mutating_cached_text(self):
        source = self.corpus / "entries/alpha/entry.html"
        source.write_text(source.read_text().replace(
            '<p>A diagonal argument.</p>',
            '<p>By <a href="#repeat"></a>, this follows from '
            '<a href="beta#fact"></a>.</p>').replace(
            '<p>A hidden witness.</p>',
            '<p>A hidden witness uses <a href="#empty"></a>.</p>'
            '<a href="https://answer.example/">Secret source</a>'))
        beta = self.corpus / "entries/beta/entry.html"
        beta.write_text(beta.read_text().replace(
            '<p>An elementary fact.</p>', '<p>See <a href="alpha#question"></a>.</p>'))
        self.revision = write_index(self.corpus, self.cache)["revision"]
        full = self.get("/api/entries/alpha/context/", {"include": "blocks,references"})
        block = full["blocks"]["results"][0]
        self.assertIn("By Lemma 1, this follows from A fact.", block["text"])
        self.assertIn("A hidden witness uses Lemma 2.", block["answer_text"])
        internal = [link for link in block["links"] if link["kind"] == "internal"]
        self.assertIn({"target": "alpha#repeat", "text": "Lemma 1",
                       "url": "/entries/alpha/#repeat"},
                      [{key: link[key] for key in ("target", "text", "url")}
                       for link in internal])
        self.assertIn("Earlier fact", [link["text"] for link in internal])
        # Cross-entry label resolution reads headings, so cyclic links do not
        # recurse and resolved labels must never overwrite the cached source.
        target = self.get("/api/entries/beta/context/")["blocks"]["results"][0]
        self.assertIn("See Diagonal question.", target["text"])
        beta.write_text(beta.read_text().replace("A fact", "A freshly revised target"))
        refreshed = self.get("/api/entries/alpha/context/")["blocks"]["results"][0]
        self.assertIn("this follows from A freshly revised target.", refreshed["text"])
        self.assertEqual(next(link["text"] for link in refreshed["links"]
                              if link["href"] == "beta#fact"), "A freshly revised target")
        hidden = self.get("/api/entries/alpha/context/", {
            "include": "blocks,references", "include_answers": "false",
        })
        self.assertNotIn("Secret source", str(hidden))
        self.assertNotIn("https://answer.example/", str(hidden))
        self.assertNotIn("answer_text", hidden["blocks"]["results"][0])
        self.assertFalse(any(link["in_answer"]
                             for link in hidden["blocks"]["results"][0]["links"]))
        self.assertFalse(any(edge["in_answer"] for edge in hidden["references"]["results"]))

    def test_context_labels_explicit_figure_table_and_equation_anchor_links(self):
        source = self.corpus / "entries/beta/entry.html"
        source.write_text(r'''<section id="fact" data-kind="lemma" data-formal="proof">
            <h2>A fact</h2>
            <figure id="picture"><figcaption>A diagram.</figcaption></figure>
            <table id="values"><caption>Some values.</caption><tr><td>1</td></tr></table>
            <div class="math-display">\[x=x\label{eq:one}\]</div>
            <p>Use <a href="#picture"></a>, <a href="#values"></a>, and
            <a href="#eq:one"></a>.</p></section>''')
        self.revision = write_index(self.corpus, self.cache)["revision"]
        block = self.get("/api/entries/beta/context/")["blocks"]["results"][0]
        self.assertIn("Use Figure 1, Table 1, and (1).", block["text"])
        self.assertEqual([(link["target"], link["text"]) for link in block["links"]], [
            ("beta#picture", "Figure 1"), ("beta#values", "Table 1"), ("beta#eq:one", "(1)"),
        ])

    def test_block_search_filters_and_answer_opt_in(self):
        self.assertEqual(self.get("/api/search/blocks/", {"q": "hidden witness"})["count"], 0)
        answer = self.get("/api/search/blocks/", {
            "q": "HIDDEN WITNESS", "include_answers": "true", "kind": "question", "area": "first",
        })
        self.assertEqual([block["key"] for block in answer["results"]], ["alpha#question"])
        self.assertEqual(self.get("/api/search/blocks/", {
            "q": "argument", "area": "second",
        })["count"], 1)
        all_results = self.get("/api/search/blocks/", {"area": "root", "limit": 1, "offset": 1})
        self.assertEqual(all_results["count"], 6)
        self.assertEqual(len(all_results["results"]), 1)
        self.assertEqual(all_results["limit"], 1)
        self.assertEqual(all_results["offset"], 1)

    def test_node_search_finds_unused_and_unbound_records(self):
        result = self.get("/api/search/nodes/", {"q": "description"})
        self.assertEqual({node["id"] for node in result["results"]},
                         {"proof", "other", "unused", "unbound"})
        result = self.get("/api/search/nodes/", {"verified": "false"})
        self.assertEqual({node["id"] for node in result["results"]}, {"other", "unbound"})
        result = self.get("/api/search/nodes/", {"declaration": "Example.proof"})
        self.assertEqual([node["id"] for node in result["results"]], ["proof"])
        self.assertEqual(self.get("/api/search/nodes/", {"declaration": "Example"})["count"], 0)

    def test_area_node_collections_deduplicate_consumers_and_filter_usage(self):
        with self.track_reads() as reads:
            result = self.get("/api/search/nodes/", {
                "area": "first", "limit": 1, "offset": 1,
            })
        self.assertEqual(result["count"], 2)
        self.assertEqual([node["id"] for node in result["results"]], ["proof"])
        self.assertEqual({path.name for path in reads if path.parent == self.corpus / "nodes"},
                         {"proof.json"})
        # The root includes both child areas, with shared node `other` only once.
        root = self.get("/api/search/nodes/", {"area": "root"})
        self.assertEqual([node["id"] for node in root["results"]], ["other", "proof"])
        self.assertEqual(self.get("/api/search/nodes/", {
            "area": "root", "include_descendants": "false",
        })["count"], 0)
        for params, expected in [
            ({"usage": "mapped"}, ["other", "proof"]),
            ({"usage": "unmapped"}, ["unbound", "unused"]),
            ({"usage": "unmapped", "verified": "false"}, ["unbound"]),
            ({"area": "first", "usage": "unmapped"}, []),
            ({"area": "first", "module": "Lemmatheca.Shared",
              "declaration": "Example.proof", "verified": "true"}, ["proof"]),
            ({"area": "second", "module": "Lemmatheca.Shared"}, []),
        ]:
            with self.subTest(params=params), self.track_reads():
                result = self.get("/api/search/nodes/", params)
                self.assertEqual([node["id"] for node in result["results"]], expected)

    def test_additional_area_metadata_updates_node_and_entry_collections_live(self):
        before = self.get("/api/search/nodes/", {"area": "second"})
        self.assertEqual([node["id"] for node in before["results"]], ["other"])
        metadata = self.corpus / "entries/beta/entry.json"
        write_json(metadata, {**read_json(metadata), "additional_areas": ["second"]})
        with self.track_reads():
            after = self.get("/api/search/nodes/", {"area": "second"})
            entries = self.get("/api/entries/", {"area": "second"})
        self.assertEqual([node["id"] for node in after["results"]], ["other", "proof"])
        self.assertEqual([entry["id"] for entry in entries["results"]], ["beta", "remote"])
        self.assertEqual(entries["results"][0]["additional_areas"], ["second"])

    def test_entry_listing_is_compact_ordered_and_reads_no_html_or_nodes(self):
        with self.track_reads() as reads:
            result = self.get("/api/entries/")
        self.assertEqual(result["count"], 3)
        self.assertEqual([entry["id"] for entry in result["results"]], ["beta", "alpha", "remote"])
        defaults = {"id", "title", "primary_area", "additional_areas", "reading_position",
                    "block_count", "url"}
        self.assertTrue(all(set(entry) == defaults for entry in result["results"]))
        self.assertEqual([entry["reading_position"] for entry in result["results"]], [1, 2, 1])
        self.assertEqual([entry["block_count"] for entry in result["results"]], [1, 4, 1])
        self.assertEqual(result["results"][0]["url"], "/entries/beta/")
        self.assertFalse(any(path.parent == self.corpus / "nodes" for path in reads))
        page = self.get("/api/entries/", {"area": "root", "limit": 1, "offset": 1})
        self.assertEqual(page["count"], 3)
        self.assertEqual([entry["id"] for entry in page["results"]], ["alpha"])
        self.assertEqual(self.get("/api/entries/", {
            "area": "root", "include_descendants": "false",
        })["count"], 0)

    def test_field_projection_returns_selected_live_fields_and_keeps_ids(self):
        with self.track_reads():
            nodes = self.get("/api/search/nodes/", {
                "declaration": "Example.proof", "fields": "description",
            })
        self.assertEqual(nodes["results"], [{"id": "proof", "description": "Description of proof."}])
        metadata = self.corpus / "entries/alpha/entry.json"
        saved_summary = {"status": "partial", "complete": 1, "total": 2, "unplanned": 1,
                         "label": "Partial", "description": "Saved summary."}
        write_json(metadata, {**read_json(metadata), "abstract": "A revised abstract.",
                              "formalization": saved_summary})
        with self.track_reads():
            entries = self.get("/api/entries/", {
                "area": "first", "limit": 1, "offset": 1,
                "fields": "abstract,summary,reading_time,based_on,formalization",
            })
        self.assertEqual(entries["results"], [{
            "id": "alpha", "abstract": "A revised abstract.", "summary": "Summary.",
            "reading_time": 5, "based_on": [], "formalization": saved_summary,
        }])
        self.assertEqual(self.get("/api/entries/", {"fields": "id", "limit": 1})["results"],
                         [{"id": "beta"}])

    def test_repeated_node_queries_union_matches_and_report_clause_provenance(self):
        clauses = ["description proof", "unused", "DESCRIPTION proof", "unused nonexistent"]
        with self.track_reads():
            result = self.get("/api/search/nodes/", {"q": clauses})
        self.assertEqual(result["count"], 2)
        self.assertEqual([(node["id"], node["matched_queries"]) for node in result["results"]],
                         [("proof", [0, 2]), ("unused", [1])])
        page = self.get("/api/search/nodes/", {"q": clauses, "limit": 1, "offset": 1})
        self.assertEqual(page["count"], 2)
        self.assertEqual([(node["id"], node["matched_queries"]) for node in page["results"]],
                         [("unused", [1])])
        filtered = self.get("/api/search/nodes/", {"q": clauses, "usage": "mapped", "area": "first"})
        self.assertEqual([node["id"] for node in filtered["results"]], ["proof"])
        projected = self.get("/api/search/nodes/", {"q": clauses, "fields": "description"})
        self.assertTrue(all(set(node) == {"id", "description"} for node in projected["results"]))
        single = self.get("/api/search/nodes/", {"q": "proof"})
        self.assertNotIn("matched_queries", single["results"][0])
        explicit = self.get("/api/search/nodes/", {"q": "proof", "fields": "matched_queries"})
        self.assertEqual(explicit["results"], [{"id": "proof", "matched_queries": [0]}])
        maximum = self.get("/api/search/nodes/", {"q": ["proof"] * 10})
        self.assertEqual(maximum["results"][0]["matched_queries"], list(range(10)))

    def test_exact_node_filters_and_context_avoid_unrelated_records(self):
        with self.track_reads() as reads:
            result = self.get("/api/search/nodes/", {"module": "Lemmatheca.Shared"})
        self.assertEqual([node["id"] for node in result["results"]], ["proof"])
        node_reads = {path.name for path in reads if path.parent == self.corpus / "nodes"}
        self.assertEqual(node_reads, {"proof.json"})
        with self.track_reads(allow_html=True) as reads:
            result = self.get("/api/entries/alpha/context/", {"include": "nodes"})
        self.assertEqual({node["id"] for node in result["nodes"]["results"]}, {"proof", "other"})
        self.assertEqual({path.name for path in reads if path.parent == self.corpus / "nodes"},
                         {"proof.json", "other.json"})

    def test_node_search_retains_only_requested_page_while_counting_all_matches(self):
        class TrackedNode(dict):
            pass

        for number in range(80):
            identifier = f"bulk-{number:03}"
            write_json(self.corpus / "nodes" / f"{identifier}.json", {
                "id": identifier, "description": f"Description of {identifier}.",
                "verified": number % 2 == 0, "module": "Lemmatheca.Shared",
                "declaration": "Example.proof", "dependencies": [],
            })
        index = write_index(self.corpus, self.cache)
        for filters, count, expected in [
            ({}, 84, ["bulk-003", "bulk-004"]),
            ({"module": "Lemmatheca.Shared", "declaration": "Example.proof", "verified": True},
             41, ["bulk-006", "bulk-008"]),
            ({"queries": ["description", "bulk"]}, 84, ["bulk-003", "bulk-004"]),
        ]:
            with self.subTest(filters=filters):
                retained = WeakValueDictionary()
                peak = 0

                def tracked_read(identifier, corpus):
                    nonlocal peak
                    record = TrackedNode(read_node(identifier, corpus))
                    retained[identifier] = record
                    peak = max(peak, len(retained))
                    return record

                query = CorpusQuery(index, self.corpus)
                with patch("catalog.queries.read_node", side_effect=tracked_read):
                    result = query.find_nodes("description", limit=2, offset=3, **filters)
                self.assertEqual(result["count"], count)
                self.assertEqual([node["id"] for node in result["results"]], expected)
                self.assertLessEqual(set(retained), set(expected))
                # The result page plus the current/previous candidate are the
                # only live records, even when every node must be inspected.
                self.assertLessEqual(peak, 4)

    def test_references_preserve_repeated_links_and_answer_locations(self):
        result = self.get("/api/references/", {"target": "beta#fact", "direction": "incoming"})
        self.assertEqual(result["count"], 2)
        self.assertEqual(len({edge["id"] for edge in result["results"]}), 2)
        self.assertEqual([edge["in_answer"] for edge in result["results"]], [False, True])
        for edge in result["results"]:
            self.assertEqual(edge["source"], "alpha#question")
            self.assertEqual(edge["source_url"], "/entries/alpha/#question")
            self.assertEqual(edge["target_url"], "/entries/beta/#fact")
        outgoing = self.get("/api/references/", {"target": "alpha", "direction": "outgoing"})
        self.assertEqual(outgoing["count"], 4)
        self.assertNotIn("https://example.com/", str(outgoing))

    def test_block_references_include_owned_anchors_and_self_edges_once(self):
        result = self.get("/api/references/", {"target": "alpha#question", "direction": "incoming"})
        self.assertEqual({edge["target"] for edge in result["results"]},
                         {"alpha#local", "alpha#question"})
        both = self.get("/api/references/", {"target": "alpha#question", "direction": "both"})
        self.assertEqual(both["count"], 4)
        self.assertEqual(len({edge["id"] for edge in both["results"]}), 4)
        anchor = self.get("/api/references/", {"target": "alpha#local", "direction": "incoming"})
        self.assertEqual(anchor["count"], 1)
        self.assertEqual(anchor["results"][0]["target"], "alpha#local")

    def test_coverage_preserves_mapping_states_and_counts_shared_nodes_once(self):
        with self.track_reads(allow_html=True):
            result = self.get("/api/coverage/", {"entry_ids": "alpha,beta"})
        self.assertEqual(result["verification_source"], "saved")
        alpha, beta = result["entries"]
        self.assertEqual(alpha["id"], "alpha")
        self.assertEqual(alpha["formalization"]["total"], 2)
        self.assertEqual(alpha["formalization"]["complete"], 1)
        self.assertEqual(alpha["formalization"]["unplanned"], 1)
        self.assertEqual(beta["formalization"]["percent"], 100)
        blocks = {block["key"]: block for block in alpha["blocks"]}
        self.assertEqual(blocks["alpha#empty"]["formalization"]["status"], "not_applicable")
        self.assertEqual(blocks["alpha#planned"]["formalization"]["status"], "not_started")
        self.assertEqual(set(result["nodes"]), {"proof", "other"})
        self.assertTrue(result["nodes"]["proof"]["verified"])
        context = self.get("/api/entries/alpha/context/", {"include": "coverage"})
        self.assertEqual(context["coverage"]["entries"][0]["formalization"], alpha["formalization"])

    def test_node_consumers_are_paged_without_duplicate_shared_bindings(self):
        result = self.get("/api/nodes/proof/consumers/", {"limit": 2, "offset": 1})
        self.assertEqual(result["count"], 3)
        self.assertEqual([block["key"] for block in result["results"]],
                         ["alpha#repeat", "beta#fact"])
        unused = self.get("/api/nodes/unused/consumers/")
        self.assertEqual(unused["count"], 0)
        self.assertEqual(unused["results"], [])

    def test_metadata_edits_are_visible_without_rebuilding_index(self):
        metadata = self.corpus / "entries/alpha/entry.json"
        write_json(metadata, {**read_json(metadata), "title": "Revised title"})
        proof = self.corpus / "nodes/proof.json"
        write_json(proof, {**read_json(proof), "description": "Revised description", "verified": False})
        with self.track_reads(allow_html=True):
            result = self.get("/api/entries/alpha/context/", {"include": "nodes,coverage"})
        self.assertEqual(result["entry"]["title"], "Revised title")
        nodes = {node["id"]: node for node in result["nodes"]["results"]}
        self.assertEqual(nodes["proof"]["description"], "Revised description")
        self.assertFalse(nodes["proof"]["verified"])
        self.assertEqual(result["coverage"]["entries"][0]["formalization"]["complete"], 0)
        search = self.get("/api/search/nodes/", {"q": "revised description"})
        self.assertEqual([node["id"] for node in search["results"]], ["proof"])

    def test_warm_cache_avoids_reloading_index_and_atomic_replacement_refreshes_it(self):
        self.get("/api/search/blocks/", {"q": "diagonal"})
        with self.track_reads() as reads:
            self.get("/api/search/blocks/", {"q": "diagonal"})
            self.get("/api/entries/alpha/context/")
        self.assertNotIn(self.cache, reads)
        source = self.corpus / "entries/alpha/entry.html"
        source.write_text(source.read_text().replace("A diagonal argument.", "A replaced argument."))
        self.revision = write_index(self.corpus, self.cache)["revision"]
        with self.track_reads(allow_html=True):
            result = self.get("/api/search/blocks/", {"q": "replaced argument"})
        self.assertEqual(result["count"], 1)

    def test_live_entry_text_refreshes_without_rebuilding_structural_index(self):
        self.get("/api/search/blocks/", {"q": "diagonal"})
        source = self.corpus / "entries/alpha/entry.html"
        source.write_text(source.read_text()
                          .replace("Diagonal question", "Fresh question heading")
                          .replace("A diagonal argument.", "A newly edited argument.")
                          .replace("A hidden witness.", "A revised hidden answer."))
        with self.track_reads(allow_html=True):
            context = self.get("/api/entries/alpha/context/")
        block = context["blocks"]["results"][0]
        self.assertEqual(block["title"], "Fresh question heading")
        self.assertIn("newly edited argument", block["text"])
        self.assertIn("revised hidden answer", block["answer_text"])
        with self.track_reads():
            search = self.get("/api/search/blocks/", {"q": "fresh newly"})
        self.assertEqual([block["key"] for block in search["results"]], ["alpha#question"])
        self.assertEqual(self.get("/api/search/blocks/", {"q": "diagonal"})["count"], 0)

    def test_search_only_constructs_requested_page_summaries(self):
        with patch.object(CorpusQuery, "_block_summary", autospec=True,
                          side_effect=CorpusQuery._block_summary) as summaries:
            result = self.get("/api/search/blocks/", {"limit": 1, "offset": 2})
        self.assertEqual(result["count"], 6)
        self.assertEqual([block["key"] for block in result["results"]], ["alpha#empty"])
        self.assertEqual(summaries.call_count, 1)

    def test_references_read_only_page_sources_and_refresh_link_labels(self):
        with self.track_reads(allow_html=True) as reads:
            result = self.get("/api/references/", {
                "target": "beta#fact", "direction": "incoming", "limit": 1,
            })
        self.assertEqual({path.parent.name for path in reads if path.suffix == ".html"}, {"alpha"})
        self.assertEqual(result["results"][0]["text"], "Earlier fact")
        source = self.corpus / "entries/alpha/entry.html"
        source.write_text(source.read_text().replace(
            '>Earlier fact</a>', '>A freshly written label</a>'))
        refreshed = self.get("/api/references/", {
            "target": "beta#fact", "direction": "incoming", "limit": 1,
        })
        self.assertEqual(refreshed["results"][0]["text"], "A freshly written label")
        # The answer reference follows an external link in the source. Its
        # index ordinal must count that external link as well.
        answer = self.get("/api/references/", {
            "target": "beta#fact", "direction": "incoming", "limit": 1, "offset": 1,
        })
        self.assertEqual(answer["results"][0]["text"], "Earlier fact again")

    def test_changed_entry_structure_or_reference_targets_report_conflicts(self):
        source = self.corpus / "entries/alpha/entry.html"
        original = source.read_text()
        for changed in [original.replace('id="planned"', 'id="renamed"'),
                        original.replace('data-kind="question"', 'data-kind="theorem"'),
                        original.replace('data-formal="proof other"', 'data-formal="proof"')]:
            with self.subTest(changed=changed):
                source.write_text(changed)
                self.assert_error("/api/entries/alpha/context/", {}, 409, "index_outdated")
        source.write_text(original.replace('href="beta#fact"', 'href="remote#fact"'))
        self.assert_error("/api/references/", {
            "target": "beta#fact", "direction": "incoming",
        }, 409, "index_outdated")

    def test_reference_pages_validate_the_complete_known_source_link_sequence(self):
        source = self.corpus / "entries/alpha/entry.html"
        original = source.read_text()
        changes = [
            original.replace('<a href="beta#fact">Earlier fact again</a>',
                             '<a href="remote#fact">Earlier fact again</a>'),
            original.replace('<a href="#local">Nearby anchor</a>', ''),
            original.replace('<a href="#local">Nearby anchor</a>\n'
                             '              <a href="#question">Same question</a>',
                             '<a href="#question">Same question</a>\n'
                             '              <a href="#local">Nearby anchor</a>'),
            original.replace('</section>',
                             '<a href="remote#fact">Added reference</a></section>', 1),
        ]
        for changed in changes:
            with self.subTest(changed=changed):
                self.assertNotEqual(changed, original)
                source.write_text(changed)
                clear_text_cache()
                # This page loads alpha but not its changed edge. Comparing
                # only the returned edge would miss the stale source structure.
                self.assert_error("/api/references/", {
                    "target": "beta#fact", "direction": "incoming", "limit": 1,
                }, 409, "index_outdated")
                # An empty incoming page visits no sources; its count remains
                # explicitly scoped to the saved reference snapshot.
                with self.track_reads():
                    empty = self.get("/api/references/", {
                        "target": "beta#fact", "direction": "incoming", "offset": 50,
                    })
                self.assertEqual(empty["results"], [])
                self.assertEqual(empty["count"], 2)

    def test_outgoing_references_detect_new_links_in_previously_empty_sources(self):
        source = self.corpus / "entries/beta/entry.html"
        source.write_text(source.read_text().replace(
            '</section>', '<a href="alpha#question">New reference</a></section>'))
        for params in [
            {"target": "beta", "direction": "outgoing"},
            {"target": "beta#fact", "direction": "outgoing", "offset": 50},
        ]:
            with self.subTest(params=params):
                self.assert_error("/api/references/", params, 409, "index_outdated")

    def test_incoming_references_retain_snapshot_scope_for_unknown_new_sources(self):
        source = self.corpus / "entries/remote/entry.html"
        source.write_text(source.read_text().replace(
            '</section>', '<a href="beta#fact">Previously unindexed source</a></section>'))
        with self.track_reads(allow_html=True) as reads:
            incoming = self.get("/api/references/", {
                "target": "beta#fact", "direction": "incoming",
            })
        self.assertEqual(incoming["count"], 2)
        self.assertNotIn("remote", {path.parent.name for path in reads if path.suffix == ".html"})
        self.revision = write_index(self.corpus, self.cache)["revision"]
        refreshed = self.get("/api/references/", {
            "target": "beta#fact", "direction": "incoming",
        })
        self.assertEqual(refreshed["count"], 3)
        self.assertIn("remote#fact", {edge["source"] for edge in refreshed["results"]})

    def test_mapping_queries_require_current_source_but_node_search_does_not(self):
        (self.corpus / "entries/alpha/entry.html").unlink()
        with self.track_reads():
            self.get("/api/search/nodes/", {"module": "Lemmatheca.Shared"})
        for path, params in [
            ("/api/coverage/", {"entry_ids": "alpha"}),
            ("/api/entries/alpha/context/", {"include": "nodes"}),
            ("/api/entries/alpha/context/", {"include": "coverage"}),
            ("/api/entries/alpha/context/", {}),
        ]:
            with self.subTest(path=path, params=params):
                self.assert_error(path, params, 409, "index_outdated")

    def test_mapping_edits_conflict_until_the_index_is_rebuilt(self):
        source = self.corpus / "entries/alpha/entry.html"
        source.write_text(source.read_text().replace('data-formal="proof other"',
                                                     'data-formal="unused"'))
        for path, params in [
            ("/api/coverage/", {"entry_ids": "alpha"}),
            ("/api/entries/alpha/context/", {"include": "nodes"}),
        ]:
            with self.subTest(path=path):
                response = self.assert_error(path, params, 409, "index_outdated")
                self.assertNotIn('"results"', response.content.decode())
        self.revision = write_index(self.corpus, self.cache)["revision"]
        context = self.get("/api/entries/alpha/context/", {"include": "nodes,coverage"})
        self.assertEqual({node["id"] for node in context["nodes"]["results"]},
                         {"proof", "unused"})
        blocks = context["coverage"]["entries"][0]["blocks"]
        self.assertEqual(blocks[0]["formal_ids"], ["unused"])
        self.assertNotIn("other", context["coverage"]["nodes"])

    @override_settings(CORPUS_TEXT_CACHE_ENTRIES=2)
    def test_coverage_validates_twenty_selected_entries_with_bounded_text_cache(self):
        additions = [f"bulk-{number:02}" for number in range(18)]
        order_path = self.corpus / "area_entries.json"
        order = read_json(order_path)
        order["areas"]["first"].extend(additions)
        write_json(order_path, order)
        for identifier in additions:
            self.add_entry(identifier, "first",
                           '<section id="fact" data-kind="lemma" data-formal="proof">'
                           '<h2>A fact</h2><p>An argument.</p></section>')
        self.revision = write_index(self.corpus, self.cache)["revision"]
        selected = ["alpha", "beta", *additions]
        with self.track_reads(allow_html=True) as reads:
            result = self.get("/api/coverage/", {"entry_ids": ",".join(selected)})
        self.assertEqual([entry["id"] for entry in result["entries"]], selected)
        self.assertEqual({path.parent.name for path in reads if path.suffix == ".html"},
                         set(selected))
        self.assertLessEqual(text_cache_info()["entries"], 2)
        self.assertLessEqual(text_cache_info()["bytes"], text_cache_info()["max_bytes"])

    def test_requests_do_not_change_corpus_or_index(self):
        before = {path: path.read_bytes() for path in self.repository.rglob("*") if path.is_file()}
        with patch("subprocess.run", side_effect=AssertionError("No Lean or Git in requests")):
            for path, params in [
                ("/api/entries/", {}),
                ("/api/entries/alpha/context/", {"include": "blocks,nodes,references,coverage,navigation"}),
                ("/api/search/blocks/", {"q": "argument"}),
                ("/api/search/nodes/", {}),
                ("/api/references/", {"target": "alpha"}),
                ("/api/coverage/", {"entry_ids": "alpha,beta"}),
                ("/api/nodes/proof/consumers/", {}),
            ]:
                with self.subTest(path=path):
                    self.get(path, params)
        self.assertEqual(before, {path: path.read_bytes()
                                  for path in self.repository.rglob("*") if path.is_file()})

    def test_expected_revision_and_missing_mapped_node_report_conflicts(self):
        self.assert_error("/api/search/blocks/", {"revision": "0" * 64}, 409)
        self.assert_error("/api/entries/", {"revision": "0" * 64}, 409)
        (self.corpus / "nodes/proof.json").unlink()
        self.assert_error("/api/coverage/", {"entry_ids": "alpha"}, 409, "index_outdated")

    def test_missing_corrupt_and_incompatible_index_are_service_errors(self):
        legacy = {**read_json(self.cache), "schema_version": 4}
        for contents in [None, "not JSON", "{}", json.dumps(legacy)]:
            with self.subTest(contents=contents):
                if contents is None:
                    self.cache.unlink(missing_ok=True)
                else:
                    self.cache.write_text(contents)
                clear_index_cache()
                self.assert_error("/api/search/blocks/", {}, 503)
                self.assert_error("/api/entries/", {}, 503)
                if contents is None:
                    self.assertFalse(self.cache.exists(), "Requests must not generate an index")

    def test_unknown_targets_return_json_not_found(self):
        for path, params in [
            ("/api/entries/missing/context/", {}),
            ("/api/nodes/missing/consumers/", {}),
            ("/api/references/", {"target": "alpha#missing"}),
            ("/api/references/", {"target": "missing"}),
            ("/api/coverage/", {"entry_ids": "missing"}),
            ("/api/search/blocks/", {"area": "missing"}),
            ("/api/search/nodes/", {"area": "missing"}),
            ("/api/entries/", {"area": "missing"}),
        ]:
            with self.subTest(path=path, params=params):
                self.assert_error(path, params, 404)

    def test_invalid_parameters_and_repeated_keys_are_rejected(self):
        for path, params in [
            ("/api/search/blocks/", {"unknown": "value"}),
            ("/api/search/blocks/", {"limit": "0"}),
            ("/api/search/blocks/", {"limit": "101"}),
            ("/api/search/blocks/", {"offset": "-1"}),
            ("/api/search/blocks/", {"limit": "1.5"}),
            ("/api/search/blocks/", {"include_answers": "yes"}),
            ("/api/search/blocks/", {"kind": "unsupported"}),
            ("/api/search/nodes/", {"verified": "yes"}),
            ("/api/search/nodes/", {"usage": "verified"}),
            ("/api/search/nodes/", {"include_descendants": "yes"}),
            ("/api/search/nodes/", {"fields": ""}),
            ("/api/search/nodes/", {"fields": "description,unknown"}),
            ("/api/search/nodes/", {"fields": "id,"}),
            ("/api/search/nodes/", {"q": ["proof", " "]}),
            ("/api/search/nodes/", {"q": ["proof"] * 11}),
            ("/api/search/nodes/", {"q": ["proof", "x" * 201]}),
            ("/api/entries/", {"fields": ""}),
            ("/api/entries/", {"fields": "description"}),
            ("/api/entries/", {"include_descendants": "yes"}),
            ("/api/entries/alpha/context/", {"include": "not-supported"}),
            ("/api/references/", {}),
            ("/api/references/", {"target": "alpha", "direction": "sideways"}),
            ("/api/coverage/", {}),
            ("/api/coverage/", {"entry_ids": ",".join(f"entry{i}" for i in range(21))}),
        ]:
            with self.subTest(path=path, params=params):
                self.assert_error(path, params, 400)
        self.assert_error("/api/search/blocks/?q=first&q=second", {}, 400)
        self.assert_error("/api/entries/?area=first&area=second", {}, 400)
        self.assert_error("/api/search/nodes/?usage=mapped&usage=unmapped", {}, 400)

    def test_duplicate_csv_values_are_deduplicated_but_invalid_ids_are_safe(self):
        context = self.get("/api/entries/alpha/context/", {"include": "blocks,blocks"})
        self.assertEqual(context["blocks"]["count"], 4)
        coverage = self.get("/api/coverage/", {"entry_ids": "alpha,alpha"})
        self.assertEqual([entry["id"] for entry in coverage["entries"]], ["alpha"])
        # A warm cache lets us verify that a traversal-shaped ID never reaches
        # even a live metadata read.
        self.get("/api/search/blocks/")
        with patch.object(Path, "open", side_effect=AssertionError("Invalid target reached files")):
            self.assert_error("/api/references/", {"target": "../outside#fact"}, 404)

    def test_malformed_live_metadata_reports_outdated_index(self):
        for relative in ["entries/alpha/entry.json", "nodes/proof.json"]:
            path = self.corpus / relative
            original = path.read_bytes()
            for record in [[], {"id": "wrong-id"}]:
                with self.subTest(relative=relative, record=record):
                    write_json(path, record)
                    endpoint, parameters = (("/api/entries/alpha/context/", {})
                                            if relative.startswith("entries/") else
                                            ("/api/coverage/", {"entry_ids": "alpha"}))
                    self.assert_error(endpoint, parameters, 409, "index_outdated")
            path.write_bytes(original)

    def test_malformed_nested_index_is_a_service_error(self):
        document = read_json(self.cache)
        document["blocks"]["alpha#question"]["kind"] = 3
        write_json(self.cache, document)
        clear_index_cache()
        self.assert_error("/api/entries/alpha/context/", {}, 503)

    def test_legacy_node_apis_do_not_require_the_index(self):
        self.cache.unlink()
        detail = self.client.get("/api/nodes/proof/")
        self.assertEqual(detail.status_code, 200)
        self.assertEqual(detail.json()["description"], "Description of proof.")
        listing = self.client.get("/api/nodes/")
        self.assertEqual(listing.status_code, 200)
        self.assertEqual({record["id"] for record in listing.json()["nodes"]},
                         {"proof", "other", "unused", "unbound"})
        self.assertNotIn("index_revision", detail.json())

    def test_head_is_read_only_and_other_methods_are_not_allowed(self):
        for path, params in [
            ("/api/entries/", {}),
            ("/api/entries/alpha/context/", {}),
            ("/api/search/blocks/", {}),
            ("/api/search/nodes/", {}),
            ("/api/references/", {"target": "alpha"}),
            ("/api/coverage/", {"entry_ids": "alpha"}),
            ("/api/nodes/proof/consumers/", {}),
        ]:
            with self.subTest(path=path):
                head = self.client.head(path, params)
                self.assertEqual(head.status_code, 200, head.content)
                self.assertEqual(head.content, b"")
                self.assertEqual(self.client.post(path, params).status_code, 405)
