"""Build publication orchestration and one real Lean kernel-checker batch."""

from io import StringIO
import json
from pathlib import Path
import shutil
import subprocess
from tempfile import TemporaryDirectory
from unittest.mock import patch

from django.conf import settings
from django.core.management import call_command, CommandError
from django.test import SimpleTestCase, override_settings

from catalog.corpus_index import write_index
from catalog.files import read_json, write_json
from catalog.proofs import build


class ProofResultsTests(SimpleTestCase):
    def setUp(self):
        temporary = TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        (self.root / "nodes").mkdir()
        self.path = self.root / "nodes/example.json"
        write_json(self.path, {"id": "example", "module": "Lemmatheca", "declaration": "example",
                               "verified": True, "signature": "example : True", "declaration_line": 5})
        directory = self.root / "entries/example"
        directory.mkdir(parents=True)
        self.metadata = directory / "entry.json"
        self.source = directory / "entry.html"
        write_json(self.metadata, {"id": "example", "title": "Example", "reading_time": 5,
                                   "formalization": {"label": "Previous summary"}})
        self.source.write_text(
            '<section id="fact" data-kind="lemma" data-formal="example">'
            '<h2>Example</h2><p>True.</p></section>')
        self.statistics = self.root / "statistics.json"
        write_json(self.statistics, {
            "entries": 1, "verified_entries": 1, "nodes": 1,
            "verified_nodes": 1, "contributors": 2,
        })

    def test_build_or_check_error_and_interruption_write_nothing(self):
        previous = self.path.read_bytes()
        modified = self.path.stat().st_mtime_ns
        entry_before = self.metadata.read_bytes()
        entry_modified = self.metadata.stat().st_mtime_ns
        statistics_before = self.statistics.read_bytes()
        for error in (subprocess.CalledProcessError(1, "lake"), KeyboardInterrupt()):
            for first_result in ([], [subprocess.CompletedProcess([], 0)]):
                with self.subTest(error=type(error), check=bool(first_result)):
                    with patch("catalog.proofs.subprocess.run", side_effect=[*first_result, error]), \
                            patch("catalog.proofs.save_results") as save:
                        with self.assertRaises(type(error)):
                            build(self.root, self.root)
                        save.assert_not_called()
                    self.assertEqual(self.path.read_bytes(), previous)
                    self.assertEqual(self.path.stat().st_mtime_ns, modified)
                    self.assertEqual(self.metadata.read_bytes(), entry_before)
                    self.assertEqual(
                        self.metadata.stat().st_mtime_ns, entry_modified)
                    self.assertEqual(
                        self.statistics.read_bytes(), statistics_before)

    def test_missing_or_malformed_result_writes_nothing(self):
        previous = self.path.read_bytes()
        entry_before = self.metadata.read_bytes()
        for output in ("", 'NODE_STATUS {"declaration":"example","verified":"true"}',
                       'NODE_STATUS []', 'NODE_STATUS {"verified":true}',
                       'NODE_STATUS {"declaration":[],"verified":true}',
                       'NODE_STATUS {"declaration":"example","verified":true,"typo":"value"}',
                       'NODE_STATUS {', 'NODE_STATUS {"declaration":"other","verified":true}',
                       'NODE_STATUS {"declaration":"example","verified":true}\n' * 2):
            with self.subTest(output=output):
                with patch("catalog.proofs.subprocess.run", return_value=subprocess.CompletedProcess([], 0, output)), \
                        patch("catalog.proofs.save_results") as save:
                    with self.assertRaises(ValueError):
                        build(self.root, self.root)
                    save.assert_not_called()
                self.assertEqual(self.path.read_bytes(), previous)
                self.assertEqual(self.metadata.read_bytes(), entry_before)

    def test_build_does_not_read_or_write_statistics(self):
        self.statistics.write_text(
            "A malformed snapshot must not affect a proof build.")
        before = self.statistics.read_bytes()
        output = 'NODE_STATUS {"declaration":"example","verified":false}'
        with patch("catalog.proofs.subprocess.run", return_value=subprocess.CompletedProcess([], 0, output)):
            self.assertEqual(build(self.root, self.root), (0, 1))
        self.assertEqual(self.statistics.read_bytes(), before)

    def test_summaries_use_new_proof_results_and_preserve_metadata(self):
        statistics_before = self.statistics.read_bytes()
        for verified, label in [(False, "0%"), (True, "100%")]:
            with self.subTest(verified=verified):
                output = 'NODE_STATUS {"declaration":"example","verified":' + \
                    str(verified).lower() + '}'
                with patch("catalog.proofs.subprocess.run", return_value=subprocess.CompletedProcess([], 0, output)):
                    build(self.root, self.root)
                entry = read_json(self.metadata)
                self.assertEqual(entry["formalization"]["label"], label)
                self.assertEqual(entry["formalization"]
                                 ["complete"], int(verified))
                self.assertEqual(entry["formalization"]["total"], 1)
                self.assertEqual(entry["title"], "Example")
                self.assertEqual(entry["reading_time"], 5)
                self.assertNotIn("source", entry)
                self.assertNotIn("directory", entry)
                self.assertEqual(self.statistics.read_bytes(),
                                 statistics_before)

    def test_invalid_entry_source_or_binding_prevents_all_writes(self):
        node_before, entry_before = self.path.read_bytes(), self.metadata.read_bytes()
        valid_source = self.source.read_text()
        for source in (valid_source.replace('data-formal="example"', 'data-formal="missing"'),
                       valid_source.replace("</section>", "")):
            with self.subTest(source=source):
                self.source.write_text(source)
                output = 'NODE_STATUS {"declaration":"example","verified":false}'
                with patch("catalog.proofs.subprocess.run", return_value=subprocess.CompletedProcess([], 0, output)), \
                        patch("catalog.proofs.save_results") as save_nodes, \
                        patch("catalog.proofs.save_entries") as save_entries:
                    with self.assertRaises(ValueError):
                        build(self.root, self.root)
                    save_nodes.assert_not_called()
                    save_entries.assert_not_called()
                self.assertEqual(self.path.read_bytes(), node_before)
                self.assertEqual(self.metadata.read_bytes(), entry_before)

    def test_metadata_changes_during_build_are_preserved(self):
        def run(command, **kwargs):
            node = read_json(self.path)
            node["description"] = "Updated description."
            write_json(self.path, node)
            entry = read_json(self.metadata)
            entry["reading_time"] = 10
            write_json(self.metadata, entry)
            return subprocess.CompletedProcess(command, 0,
                                               'NODE_STATUS {"declaration":"example","verified":false,"module":"Lemmatheca.Examples"}\n')
        with patch("catalog.proofs.subprocess.run", side_effect=run):
            self.assertEqual(build(self.root, self.root), (0, 1))
        self.assertEqual(read_json(self.path), {"id": "example", "module": "Lemmatheca.Examples", "declaration": "example",
                                                "description": "Updated description.", "verified": False})
        self.assertEqual(read_json(self.metadata)["reading_time"], 10)
        self.assertEqual(read_json(self.metadata)[
                         "formalization"]["label"], "0%")

    def test_binding_changes_during_build_discard_stale_result(self):
        def run(command, **kwargs):
            node = read_json(self.path)
            node["declaration"] = "other"
            write_json(self.path, node)
            return subprocess.CompletedProcess(command, 0,
                                               'NODE_STATUS {"declaration":"example","verified":true}\n')
        with patch("catalog.proofs.subprocess.run", side_effect=run):
            self.assertEqual(build(self.root, self.root), (0, 1))
        node = read_json(self.path)
        self.assertEqual(node["declaration"], "other")
        self.assertFalse(node["verified"])
        self.assertNotIn("signature", node)
        self.assertEqual(read_json(self.metadata)[
                         "formalization"]["label"], "0%")

    def test_missing_hint_dependency_still_prevents_all_writes(self):
        node = read_json(self.path)
        node["dependencies"] = ["missing"]
        write_json(self.path, node)
        before = self.path.read_bytes(), self.metadata.read_bytes()
        output = 'NODE_STATUS {"declaration":"example","verified":true}'
        with patch("catalog.proofs.subprocess.run", return_value=subprocess.CompletedProcess([], 0, output)):
            with self.assertRaisesRegex(ValueError, "example: missing dependency missing"):
                build(self.root, self.root)
        self.assertEqual(before, (self.path.read_bytes(),
                         self.metadata.read_bytes()))


class BuildPublicationTests(SimpleTestCase):
    def test_proof_refresh_reversal_and_failures_preserve_published_snapshot(self):
        # External-process fixtures isolate publication behavior. The actual
        # checker is exercised separately in one Lean batch below.
        with TemporaryDirectory() as directory:
            root = Path(directory)
            corpus, formal = root / "corpus", root / "formal"
            (corpus / "nodes").mkdir(parents=True)
            formal.mkdir()
            names = ["complete", "unfinished", "indirect",
                     "unfinishedDefinition", "unsupported", "unbound"]
            for name in names:
                write_json(corpus / "nodes" / f"{name}.json", {
                    "id": name, "module": "Lemmatheca" if name != "unbound" else None,
                    "declaration": name if name != "unbound" else None, "verified": False,
                    "description": f"The {name} example.", "dependencies": [],
                })
            write_json(corpus / "taxonomy.json", {"areas": [{
                "id": "area", "title": "Area", "parent": None,
                "description": "An example area.",
            }]})
            write_json(corpus / "area_entries.json", {
                "areas": {"area": ["example"]}})
            entry_file = corpus / "entries/example/entry.json"
            entry_file.parent.mkdir(parents=True)
            write_json(entry_file, {
                "id": "example", "title": "Example", "primary_area": "area",
                "additional_areas": [], "based_on": [], "reading_time": 5,
                "summary": "Example proofs.", "abstract": "Examples of proof status.",
            })
            (entry_file.parent / "entry.html").write_text(
                '<section id="fact" data-kind="lemma" data-formal="complete unfinished indirect unbound">'
                '<h2>Example</h2><p>Proofs.</p></section>')

            def node(name):
                return read_json(corpus / "nodes" / f"{name}.json")

            def run_build(verified, *, fail_at=None):
                declarations = {node(name)["declaration"] for name in names
                                if node(name)["declaration"]}

                def run(command, **kwargs):
                    self.assertEqual(kwargs["cwd"], formal)
                    self.assertTrue(kwargs["check"])
                    if command[:2] == ["lake", "build"]:
                        if fail_at == "compile":
                            raise subprocess.CalledProcessError(1, command)
                        return subprocess.CompletedProcess(command, 0)
                    self.assertEqual(command[:3], ["lake", "env", "lean"])
                    inspection = (formal / command[-1]).read_text()
                    self.assertIn("import Lemmatheca.ProofStatus", inspection)
                    for declaration in declarations:
                        self.assertEqual(inspection.count(
                            "#node_status " + json.dumps(declaration)), 1)
                    if fail_at == "inspect":
                        raise subprocess.CalledProcessError(1, command)
                    output = "\n".join("NODE_STATUS " + json.dumps({
                        "declaration": declaration, "verified": declaration in verified,
                        "signature": f"{declaration} : True", "module": "Lemmatheca.Examples",
                        "declaration_line": 3,
                    }) for declaration in declarations)
                    return subprocess.CompletedProcess(command, 0, output)

                with override_settings(CORPUS_DIR=corpus, REPOSITORY_DIR=root), \
                        patch("catalog.proofs.subprocess.run", side_effect=run) as external:
                    result = call_command("build", stdout=StringIO())
                    self.assertEqual(external.call_count, 2)
                    return result

            index_path = root / "artifacts/corpus-index.json"

            def assert_index(verified, label):
                index = read_json(index_path)
                self.assertEqual(index["entries"]["example"], {
                    "blocks": ["fact"], "reading_position": 1,
                })
                current = write_index(corpus, root / "expected-index.json")
                self.assertEqual(index["revision"], current["revision"])
                self.assertEqual(read_json(entry_file)["formalization"]["label"], label)
                for name in names:
                    self.assertEqual(node(name)["verified"], name in verified)

            self.assertEqual(run_build({"complete"}),
                             "Updated 6 nodes: 1 verified, 5 not verified.")
            assert_index({"complete"}, "25%")
            self.assertFalse((corpus / "statistics.json").exists())
            self.assertIn("complete", node("complete")["signature"])
            self.assertEqual(node("complete")["module"], "Lemmatheca.Examples")
            self.assertEqual(node("complete")["declaration_line"], 3)
            for name in names:
                self.assertFalse(
                    {"proven", "sorry", "approved", "source_module"} & node(name).keys())

            repaired = {"complete", "unfinished", "indirect"}
            self.assertEqual(run_build(repaired),
                             "Updated 6 nodes: 3 verified, 3 not verified.")
            assert_index(repaired, "75%")
            self.assertEqual(run_build({"complete"}),
                             "Updated 6 nodes: 1 verified, 5 not verified.")
            assert_index({"complete"}, "25%")

            record = node("complete")
            record["declaration"] = "doesNotExist"
            write_json(corpus / "nodes/complete.json", record)
            previous = {
                name: (corpus / "nodes" / f"{name}.json").read_bytes() for name in names}
            entry_before, index_before = entry_file.read_bytes(), index_path.read_bytes()
            for fail_at in ("inspect", "compile"):
                with self.subTest(fail_at=fail_at), self.assertRaises(CommandError):
                    run_build(set(), fail_at=fail_at)
                self.assertEqual(entry_file.read_bytes(), entry_before)
                self.assertEqual(index_path.read_bytes(), index_before)
                self.assertFalse((corpus / "statistics.json").exists())
                for name in names:
                    self.assertEqual(
                        (corpus / "nodes" / f"{name}.json").read_bytes(), previous[name])


class BuildCommandIndexTests(SimpleTestCase):
    def setUp(self):
        temporary = TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.corpus = self.root / "corpus"
        self.corpus.mkdir()

    def test_index_is_refreshed_after_proof_metadata_is_saved(self):
        events = []
        output = StringIO()

        def save_proofs(corpus, formal):
            self.assertEqual((corpus, formal),
                             (self.corpus, self.root / "formal"))
            write_json(corpus / "result.json", {"verified": True})
            events.append("proofs")
            return 1, 2

        def save_index(corpus, destination):
            self.assertEqual(destination,
                             self.root / "artifacts/corpus-index.json")
            self.assertEqual(read_json(corpus / "result.json"), {"verified": True})
            events.append("index")

        with override_settings(CORPUS_DIR=self.corpus, REPOSITORY_DIR=self.root), \
                patch("catalog.management.commands.build.build", side_effect=save_proofs), \
                patch("catalog.management.commands.build.write_index", side_effect=save_index):
            result = call_command("build", stdout=output)
        self.assertEqual(events, ["proofs", "index"])
        self.assertEqual(result, "Updated 2 nodes: 1 verified, 1 not verified.")
        self.assertIn("Corpus index written:", output.getvalue())

    def test_failed_proof_build_never_starts_index_generation(self):
        with override_settings(CORPUS_DIR=self.corpus, REPOSITORY_DIR=self.root), \
                patch("catalog.management.commands.build.build", side_effect=ValueError("Lean inspection failed")), \
                patch("catalog.management.commands.build.write_index") as write:
            with self.assertRaisesRegex(CommandError, "Lean inspection failed"):
                call_command("build", stdout=StringIO())
            write.assert_not_called()

    def test_index_failure_reports_error_and_preserves_previous_cache(self):
        index = self.root / "artifacts/corpus-index.json"
        index.parent.mkdir()
        write_json(index, {"previous": "index"})
        previous = index.read_bytes()
        output = StringIO()
        with override_settings(CORPUS_DIR=self.corpus, REPOSITORY_DIR=self.root), \
                patch("catalog.management.commands.build.build", return_value=(1, 1)):
            with self.assertRaisesRegex(CommandError, "taxonomy.json"):
                call_command("build", stdout=output)
        self.assertEqual(index.read_bytes(), previous)
        self.assertNotIn("Updated", output.getvalue())


class ProofStatusLeanTests(SimpleTestCase):
    def test_real_checker_batches_transitive_axioms_and_rejects_missing_declarations(self):
        # Inline the current checker, rather than reusing a potentially stale
        # olean. One direct Lean invocation needs no Lake project or C build.
        checker = (settings.REPOSITORY_DIR / "formal/Lemmatheca/ProofStatus.lean").read_text()
        examples = """
-- The word sorry in a comment is not an unfinished proof.
theorem complete : True := True.intro
theorem unfinished : True := sorry
theorem indirect : True := unfinished
def unfinishedDefinition : Nat := sorry
axiom assumption : False
theorem unsupported : False := assumption
noncomputable def selector {α : Sort u} (h : Nonempty α) : α := Classical.choice h
noncomputable def indirectSelector {α : Sort u} (h : Nonempty α) : α := selector h
noncomputable def chosenType : Type := Classical.choice (show Nonempty Type from ⟨Nat⟩)
theorem typeOnly (x : chosenType) : x = x := Eq.refl _
"""
        cases = {"complete": True, "unfinished": False, "indirect": False,
                 "unfinishedDefinition": False, "unsupported": False,
                 "selector": True, "indirectSelector": True, "typeOnly": True,
                 "Nat.succ_ne_zero": True, "propext": True, "Quot.sound": True}
        with TemporaryDirectory() as directory:
            formal = Path(directory)
            shutil.copyfile(settings.REPOSITORY_DIR / "formal/lean-toolchain",
                            formal / "lean-toolchain")
            source = checker + examples
            commands = "\n".join("#node_status " + json.dumps(name) for name in cases)
            (formal / "Check.lean").write_text(
                source + commands + '\n#node_status "doesNotExist"\n', encoding="utf-8")
            result = subprocess.run(["lean", "Check.lean"], cwd=formal, text=True,
                                    stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        self.assertEqual(result.returncode, 1, result.stdout)
        self.assertIn("doesNotExist", result.stdout)
        self.assertIn("error", result.stdout)
        records = [json.loads(line.removeprefix("NODE_STATUS "))
                   for line in result.stdout.splitlines() if line.startswith("NODE_STATUS ")]
        self.assertEqual([record["declaration"] for record in records], list(cases))
        by_name = {record["declaration"]: record for record in records}
        for name, expected in cases.items():
            with self.subTest(declaration=name):
                record = by_name[name]
                self.assertEqual(record["verified"], expected)
                self.assertIn(name, record["signature"])
                self.assertGreater(record["declaration_line"], 0)
        self.assertEqual(by_name["Nat.succ_ne_zero"]["module"], "Init.Data.Nat.Basic")
        complete_line = next(number for number, line in enumerate(source.splitlines(), 1)
                             if line.startswith("theorem complete :"))
        self.assertEqual(by_name["complete"]["declaration_line"], complete_line)
