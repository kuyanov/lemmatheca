"""The authoring index is deterministic, derived and published only if valid."""

from collections import Counter
from copy import deepcopy
import json
from pathlib import Path
from tempfile import TemporaryDirectory
from unittest.mock import patch

from django.test import SimpleTestCase

from catalog.corpus_index import CorpusIndex, default_index_path, write_index
from catalog.files import read_json, write_json
from catalog.validation import CorpusError, checked_source


class CorpusIndexTests(SimpleTestCase):
    def setUp(self):
        temporary = TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.repository = Path(temporary.name).resolve()
        self.corpus = self.repository / "corpus"
        (self.corpus / "nodes").mkdir(parents=True)
        write_json(self.corpus / "taxonomy.json", {"areas": [
            {"id": "area", "title": "Area", "parent": None,
             "description": "An area."},
        ]})
        write_json(self.corpus / "area_entries.json", {
            "areas": {"area": ["beta", "alpha"]},
        })
        for node_id, dependencies in [("proof", []), ("other", ["proof"])]:
            write_json(self.corpus / f"nodes/{node_id}.json", {
                "id": node_id, "description": rf"A proof of \(x=x\): {node_id}.",
                "verified": True, "module": "Lemmatheca.Example",
                "declaration": "Example.shared", "dependencies": dependencies,
                "signature": "Example.shared : True", "declaration_line": 3,
            })
        self.alpha = self.add_entry("alpha", r'''
            <section id="question" data-kind="question" data-formal="proof other">
              <h2>A question</h2><p>First paragraph with
              \(x=x\).</p><p>Second <em>paragraph</em>.</p>
              <ul><li>First item</li><li>Second item</li></ul>
              <a href="beta#fact"></a><a href="#local">Nearby</a>
              <a href="https://example.com/">Source</a>
              <span id="local">An anchor.</span>
              <details class="question-answer"><summary>Show answer</summary>
                <p>The hidden answer.</p><a href="beta#fact">Earlier fact</a>
              </details>
            </section>
            <section id="empty" data-kind="lemma" data-formal="">
              <h2>Empty mapping</h2><p>No formal content.</p>
            </section>
            <section id="planned" data-kind="lemma">
              <h2>Unplanned</h2><p>Not yet mapped.</p>
            </section>''')
        self.beta = self.add_entry("beta", '''
            <section id="fact" data-kind="lemma" data-formal="proof">
              <h2>A fact</h2><p>True.</p>
            </section>''')
        self.destination = default_index_path(self.repository)

    def add_entry(self, identifier, source):
        directory = self.corpus / "entries" / identifier
        directory.mkdir(parents=True)
        write_json(directory / "entry.json", {
            "id": identifier, "title": identifier.capitalize(),
            "primary_area": "area", "additional_areas": [], "based_on": [],
            "reading_time": 5, "summary": "Summary.", "abstract": "Abstract.",
        })
        path = directory / "entry.html"
        path.write_text(source, encoding="utf-8")
        return path

    def test_index_reuses_validated_inputs_and_exports_relationships(self):
        before = {path: path.read_bytes()
                  for path in self.corpus.rglob("*") if path.is_file()}
        reads = Counter()
        original_open = Path.open

        def tracked_open(path, *args, **kwargs):
            mode = args[0] if args else kwargs.get("mode", "r")
            if "r" in mode and path in before:
                reads[path] += 1
            return original_open(path, *args, **kwargs)

        with patch.object(Path, "open", tracked_open), \
                patch("subprocess.run", side_effect=AssertionError("No Lean")), \
                patch("catalog.sources.render_block", side_effect=AssertionError("No rendering")):
            result = write_index(self.corpus, self.destination)
        self.assertEqual(reads, Counter({path: 1 for path in before}))
        self.assertEqual(read_json(self.destination), result)
        self.assertEqual(before, {path: path.read_bytes()
                                 for path in self.corpus.rglob("*") if path.is_file()})
        self.assertEqual(result["schema_version"], 4)
        self.assertEqual(result["counts"], {
            "areas": 1, "entries": 2, "blocks": 4, "nodes": 2,
            "references": 3, "bindings": 3,
        })
        self.assertEqual(result["entries"]["alpha"]["reading_position"], 2)
        self.assertEqual(result["entries"]["beta"]["reading_position"], 1)
        self.assertEqual(result["entries"]["alpha"]["blocks"],
                         ["question", "empty", "planned"])
        self.assertEqual(set(result["entries"]["alpha"]), {"blocks", "reading_position"})
        self.assertEqual(result["nodes_by_declaration"]["Example.shared"], ["other", "proof"])
        self.assertEqual(result["module_nodes"]["Lemmatheca.Example"], ["other", "proof"])
        self.assertEqual(result["node_consumers"]["proof"], ["alpha#question", "beta#fact"])
        self.assertEqual(result["hint_dependents"]["proof"], ["other"])
        self.assertNotIn("other", result["hint_dependents"])
        self.assertNotIn("lean_dependencies", result)
        self.assertEqual(result["blocks"]["alpha#empty"]["formal_ids"], [])
        self.assertIsNone(result["blocks"]["alpha#planned"]["formal_ids"])
        question = result["blocks"]["alpha#question"]
        self.assertEqual(question["number"], 1)
        self.assertEqual(result["blocks"]["alpha#empty"]["number"], 1)
        self.assertEqual(result["blocks"]["alpha#planned"]["number"], 2)
        self.assertEqual(result["blocks"]["alpha#planned"]["order"], 3)
        self.assertEqual(result["references"][1]["target"], "alpha#local")
        self.assertEqual([edge["link_index"] for edge in result["references"]], [0, 1, 3])
        self.assertFalse(result["references"][0]["in_answer"])
        self.assertTrue(result["references"][2]["in_answer"])
        self.assertEqual(result["outgoing"]["alpha#question"], [0, 1, 2])
        self.assertEqual(result["incoming"]["beta#fact"], [0, 2])
        self.assertEqual(result["anchors"]["alpha#local"], "alpha#question")
        self.assertNotIn("alpha#question", result["anchors"])
        self.assertNotIn("alpha#empty", result["outgoing"])
        self.assertNotIn("alpha#empty", result["incoming"])
        self.assertNotIn("https://example.com/", result["incoming"])

    def test_collector_does_not_mutate_trees_and_link_ordinals_count_assets(self):
        source = r'''<section id="fact" data-kind="lemma"><h2>A fact</h2>
            <p>Visible <span>words</span>.</p><script>ignored script</script>
            <style>ignored style</style>
            <script id="script-anchor">also ignored</script>
            <div class="math-display">\[x=x\label{eq:one}\]</div>
            <a href="#eq:one">Equation</a><a href="assets/data.txt">Data</a>
            <a href="#script-anchor">An unusual local anchor</a>
            </section>'''
        root, *_ = checked_source(source)
        before = deepcopy(root)
        collector = CorpusIndex(self.corpus)
        collector.add_reading_order({"areas": {"area": ["beta"]}})
        collector.add_entry(read_json(self.beta.parent / "entry.json"), root)
        result = collector.finish()
        self.assertEqual(root, before)
        self.assertEqual(result["references"][0]["target"], "beta#eq:one")
        self.assertEqual(result["anchors"]["beta#eq:one"], "beta#fact")
        self.assertEqual(result["incoming"]["beta#eq:one"], [0])
        self.assertEqual(result["incoming"]["beta#script-anchor"], [1])
        self.assertEqual([edge["link_index"] for edge in result["references"]], [0, 2])
        self.assertNotIn("assets/data.txt", json.dumps(result))

    def test_authored_prose_is_not_retained_or_exported_but_still_changes_revision(self):
        markers = {
            "A question": "PRIVATE_HEADING_MARKER",
            "First paragraph with": "PRIVATE_BODY_MARKER",
            "The hidden answer.": "PRIVATE_ANSWER_MARKER",
            "Nearby": "PRIVATE_INTERNAL_LINK_LABEL",
            "Source": "PRIVATE_EXTERNAL_LINK_LABEL",
            "https://example.com/": "https://private-external-url.example/",
        }
        source = self.alpha.read_text()
        for text, marker in markers.items():
            source = source.replace(text, marker)
        self.alpha.write_text(source)
        root, *_ = checked_source(source)
        collector = CorpusIndex(self.corpus)
        collector.add_reading_order(read_json(self.corpus / "area_entries.json"))
        collector.add_entry(read_json(self.alpha.parent / "entry.json"), root)
        for marker in markers.values():
            self.assertNotIn(marker, str(vars(collector)))

        result = write_index(self.corpus, self.destination)
        serialized = json.dumps(result)
        for marker in markers.values():
            self.assertNotIn(marker, serialized)
        for block in result["blocks"].values():
            self.assertEqual(set(block), {"kind", "number", "order", "formal_ids"})
        for edge in result["references"]:
            self.assertEqual(set(edge), {"source", "target", "in_answer", "link_index"})

        self.alpha.write_text(source.replace("PRIVATE_BODY_MARKER", "UPDATED_PRIVATE_BODY_MARKER"))
        updated = write_index(self.corpus, self.destination)
        self.assertNotEqual(updated["revision"], result["revision"])
        self.assertEqual({key: value for key, value in updated.items() if key != "revision"},
                         {key: value for key, value in result.items() if key != "revision"})

    def test_deterministic_across_collection_order_and_locations(self):
        def collect(reverse=False):
            collector = CorpusIndex(self.corpus)
            collector.add_taxonomy(read_json(self.corpus / "taxonomy.json"))
            collector.add_reading_order(read_json(self.corpus / "area_entries.json"))
            for path in sorted(self.corpus.rglob("*"), reverse=reverse):
                if not path.is_file():
                    continue
                collector.add_file(path, path.read_bytes())
                if path.parent.name == "nodes":
                    collector.add_node(read_json(path))
                elif path.name == "entry.html":
                    root, *_ = checked_source(path.read_text())
                    collector.add_entry(read_json(path.parent / "entry.json"), root)
            return collector.finish()

        first, second = collect(), collect(reverse=True)
        self.assertEqual(first, second)
        copied = CorpusIndex(self.repository / "another-checkout/corpus")
        for path in self.corpus.rglob("*"):
            if path.is_file():
                copied.add_file(copied.corpus / path.relative_to(self.corpus), path.read_bytes())
        self.assertEqual(first["revision"], copied.finish()["revision"])
        self.assertNotIn(str(self.repository), str(first))

    def test_invalid_corpus_and_publication_error_preserve_previous_cache(self):
        write_index(self.corpus, self.destination)
        previous = self.destination.read_bytes()
        source = self.alpha.read_bytes()
        self.alpha.write_text("<section>")
        with self.assertRaises(CorpusError):
            write_index(self.corpus, self.destination)
        self.assertEqual(self.destination.read_bytes(), previous)
        self.alpha.write_bytes(source)
        previous_artifacts = set(self.destination.parent.iterdir())
        with patch.object(Path, "replace", side_effect=OSError("Cannot publish")):
            with self.assertRaisesRegex(OSError, "Cannot publish"):
                write_index(self.corpus, self.destination)
        self.assertEqual(self.destination.read_bytes(), previous)
        self.assertEqual(set(self.destination.parent.iterdir()), previous_artifacts)

    def test_revision_hashes_exact_bytes_including_crlf(self):
        paths = [self.alpha, self.alpha.parent / "entry.json"]
        initial_revision = write_index(self.corpus, self.destination)["revision"]
        for path in paths:
            original = path.read_bytes()
            path.write_bytes(original.replace(b"\n", b"\r\n"))
            content = path.read_bytes()
            self.assertIn(b"\r\n", content)
            result = write_index(self.corpus, self.destination)
            self.assertNotEqual(result["revision"], initial_revision)
            path.write_bytes(original)
            self.assertEqual(write_index(self.corpus, self.destination)["revision"], initial_revision)

    def test_metadata_is_not_duplicated_but_still_changes_revision(self):
        node_path = self.corpus / "nodes/proof.json"
        metadata_path = self.alpha.parent / "entry.json"
        taxonomy_path = self.corpus / "taxonomy.json"
        write_json(node_path, {
            **read_json(node_path), "description": "NODE_DESCRIPTION_PRIVATE",
            "signature": "Example.shared : NODE_SIGNATURE_PRIVATE",
        })
        write_json(metadata_path, {
            **read_json(metadata_path), "abstract": "ENTRY_ABSTRACT_PRIVATE",
            "based_on": [{"authors": ["CITATION_AUTHOR_PRIVATE"], "title": "CITATION_TITLE_PRIVATE"}],
        })
        taxonomy = read_json(taxonomy_path)
        taxonomy["areas"][0]["description"] = "TAXONOMY_DESCRIPTION_PRIVATE"
        write_json(taxonomy_path, taxonomy)
        result = write_index(self.corpus, self.destination)
        self.assertTrue({"nodes", "areas", "reading_order", "verification", "files"}.isdisjoint(result))
        serialized = json.dumps(result)
        for text in ["NODE_DESCRIPTION_PRIVATE", "NODE_SIGNATURE_PRIVATE", "ENTRY_ABSTRACT_PRIVATE",
                     "CITATION_AUTHOR_PRIVATE", "CITATION_TITLE_PRIVATE", "TAXONOMY_DESCRIPTION_PRIVATE"]:
            self.assertNotIn(text, serialized)
        self.assertNotIn('"verified"', serialized)
        original_derived_data = {key: value for key, value in result.items()
                                 if key != "revision"}

        # Fields omitted from the export still change its revision. The derived
        # relationships themselves need not change when only metadata changes.
        updates = [
            (node_path, {"description": "UPDATED_NODE_DESCRIPTION", "verified": False}),
            (metadata_path, {"abstract": "UPDATED_ABSTRACT"}),
            (taxonomy_path, {"areas": [{**taxonomy["areas"][0], "title": "UPDATED_AREA_TITLE"}]}),
        ]
        previous_revision = result["revision"]
        for path, update in updates:
            write_json(path, {**read_json(path), **update})
            result = write_index(self.corpus, self.destination)
            self.assertNotEqual(result["revision"], previous_revision)
            self.assertEqual({key: value for key, value in result.items()
                              if key != "revision"}, original_derived_data)
            previous_revision = result["revision"]

    def test_rejects_destinations_in_corpus_before_validation(self):
        for path in [self.corpus / "index.json", self.alpha.parent / "../index.json"]:
            with self.subTest(path=path), \
                    patch("catalog.validation.validate_corpus", side_effect=AssertionError("No scan")):
                with self.assertRaisesRegex(ValueError, "outside the corpus"):
                    write_index(self.corpus, path)
        alias = self.repository / "alias"
        alias.symlink_to(self.corpus, target_is_directory=True)
        with self.assertRaisesRegex(ValueError, "outside the corpus"):
            write_index(self.corpus, alias / "index.json")
