"""Proof result persistence and the build command against an isolated Lean project."""

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
                               "axioms": [], "verified": True, "signature": "example : True", "declaration_line": 5})
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
                       'NODE_STATUS []', 'NODE_STATUS {"verified":true,"lean_axioms":[]}',
                       'NODE_STATUS {"declaration":[],"verified":true,"lean_axioms":[]}',
                       'NODE_STATUS {"declaration":"example","verified":true,"lean_axioms":[],"axioms":["choice"]}',
                       'NODE_STATUS {', 'NODE_STATUS {"declaration":"other","verified":true,"lean_axioms":[]}',
                       'NODE_STATUS {"declaration":"example","verified":true,"lean_axioms":[]}\n' * 2):
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
        output = 'NODE_STATUS {"declaration":"example","verified":false,"lean_axioms":[]}'
        with patch("catalog.proofs.subprocess.run", return_value=subprocess.CompletedProcess([], 0, output)):
            self.assertEqual(build(self.root, self.root), (0, 1))
        self.assertEqual(self.statistics.read_bytes(), before)

    def test_summaries_use_new_proof_results_and_preserve_metadata(self):
        statistics_before = self.statistics.read_bytes()
        for verified, label in [(False, "0%"), (True, "100%")]:
            with self.subTest(verified=verified):
                output = 'NODE_STATUS {"declaration":"example","verified":' + \
                    str(verified).lower() + ',"lean_axioms":[]}'
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
                output = 'NODE_STATUS {"declaration":"example","verified":false,"lean_axioms":[]}'
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
                                               'NODE_STATUS {"declaration":"example","verified":false,"lean_axioms":[],"module":"Lemmatheca.Examples"}\n')
        with patch("catalog.proofs.subprocess.run", side_effect=run):
            self.assertEqual(build(self.root, self.root), (0, 1))
        self.assertEqual(read_json(self.path), {"id": "example", "module": "Lemmatheca.Examples", "declaration": "example",
                                                "description": "Updated description.", "axioms": [], "verified": False})
        self.assertEqual(read_json(self.metadata)["reading_time"], 10)
        self.assertEqual(read_json(self.metadata)[
                         "formalization"]["label"], "0%")

    def test_binding_changes_during_build_discard_stale_result(self):
        def run(command, **kwargs):
            node = read_json(self.path)
            node["declaration"] = "other"
            write_json(self.path, node)
            return subprocess.CompletedProcess(command, 0,
                                               'NODE_STATUS {"declaration":"example","verified":true,"lean_axioms":[]}\n')
        with patch("catalog.proofs.subprocess.run", side_effect=run):
            self.assertEqual(build(self.root, self.root), (0, 1))
        node = read_json(self.path)
        self.assertEqual(node["declaration"], "other")
        self.assertFalse(node["verified"])
        self.assertNotIn("signature", node)
        self.assertEqual(read_json(self.metadata)[
                         "formalization"]["label"], "0%")

    def test_current_axiom_allowance_is_used_and_preserved_during_build(self):
        for declared, verified in [(["choice"], True), ([], False)]:
            with self.subTest(declared=declared):
                def run(command, **kwargs):
                    node = read_json(self.path)
                    node["axioms"] = declared
                    write_json(self.path, node)
                    return subprocess.CompletedProcess(command, 0, "NODE_STATUS " + json.dumps({
                        "declaration": "example", "verified": True,
                        "lean_axioms": ["Classical.choice"],
                    }))
                with patch("catalog.proofs.subprocess.run", side_effect=run):
                    self.assertEqual(
                        build(self.root, self.root), (int(verified), 1))
                node = read_json(self.path)
                self.assertEqual(node["axioms"], declared)
                self.assertEqual(node["verified"], verified)
                self.assertNotIn("lean_axioms", node)

    def test_invalid_axiom_reports_or_metadata_write_nothing(self):
        before = self.path.read_bytes(), self.metadata.read_bytes()
        for actual in (None, "Classical.choice", [None], [""], ["Quot.sound", "Quot.sound"]):
            with self.subTest(actual=actual):
                output = "NODE_STATUS " + json.dumps({"declaration": "example", "verified": True,
                                                      "lean_axioms": actual})
                with patch("catalog.proofs.subprocess.run", return_value=subprocess.CompletedProcess([], 0, output)):
                    with self.assertRaisesRegex(ValueError, "axiom result"):
                        build(self.root, self.root)
                self.assertEqual(
                    before, (self.path.read_bytes(), self.metadata.read_bytes()))
        node = read_json(self.path)
        del node["axioms"]
        write_json(self.path, node)
        with patch("catalog.proofs.subprocess.run") as run:
            with self.assertRaisesRegex(ValueError, "axioms must be a list"):
                build(self.root, self.root)
            run.assert_not_called()

    def test_hint_axiom_mismatch_prevents_all_build_writes(self):
        node = read_json(self.path)
        node["dependencies"] = ["prerequisite"]
        write_json(self.path, node)
        other = self.root / "nodes/prerequisite.json"
        write_json(other, {"id": "prerequisite", "axioms": [
                   "choice"], "verified": False})
        before = self.path.read_bytes(), other.read_bytes(), self.metadata.read_bytes()
        for actual in ([], ["Classical.choice"]):
            with self.subTest(actual=actual):
                output = 'NODE_STATUS ' + json.dumps({"declaration": "example", "verified": True,
                                                     "lean_axioms": actual})
                with patch("catalog.proofs.subprocess.run", return_value=subprocess.CompletedProcess([], 0, output)):
                    with self.assertRaisesRegex(ValueError, "example: dependencies require undeclared axioms: choice"):
                        build(self.root, self.root)
                self.assertEqual(before, (self.path.read_bytes(), other.read_bytes(),
                                         self.metadata.read_bytes()))
        node["axioms"] = ["choice"]
        write_json(self.path, node)
        with patch("catalog.proofs.subprocess.run", return_value=subprocess.CompletedProcess([], 0, output)):
            self.assertEqual(build(self.root, self.root), (1, 2))
        self.assertTrue(read_json(self.path)["verified"])
        self.assertEqual(read_json(self.path)["axioms"], ["choice"])

    def test_missing_hint_dependency_still_prevents_all_writes(self):
        node = read_json(self.path)
        node["dependencies"] = ["missing"]
        write_json(self.path, node)
        before = self.path.read_bytes(), self.metadata.read_bytes()
        output = 'NODE_STATUS {"declaration":"example","verified":true,"lean_axioms":[]}'
        with patch("catalog.proofs.subprocess.run", return_value=subprocess.CompletedProcess([], 0, output)):
            with self.assertRaisesRegex(ValueError, "example: missing dependency missing"):
                build(self.root, self.root)
        self.assertEqual(before, (self.path.read_bytes(), self.metadata.read_bytes()))


class LeanBuildTests(SimpleTestCase):
    def test_complete_sorry_indirect_axiom_missing_and_failed_build(self):
        with TemporaryDirectory() as directory:
            root = Path(directory)
            corpus, formal = root / "corpus", root / "formal"
            (corpus / "nodes").mkdir(parents=True)
            (formal / "Lemmatheca").mkdir(parents=True)
            shutil.copyfile(settings.REPOSITORY_DIR /
                            "formal/lean-toolchain", formal / "lean-toolchain")
            shutil.copyfile(settings.REPOSITORY_DIR / "formal/Lemmatheca/ProofStatus.lean",
                            formal / "Lemmatheca/ProofStatus.lean")
            (formal / "lakefile.toml").write_text(
                'name = "proof_test"\n[[lean_lib]]\nname = "Lemmatheca"\n')
            source = '''import Lemmatheca.ProofStatus
-- The word sorry in a comment is not an unfinished proof.
theorem complete : True := by trivial
theorem unfinished : True := by sorry
theorem indirect : True := unfinished
def unfinishedDefinition : Nat := sorry
axiom assumption : False
theorem unsupported : False := assumption
'''
            (formal / "Lemmatheca.lean").write_text("import Lemmatheca.Examples\n")
            module = formal / "Lemmatheca/Examples.lean"
            module.write_text(source)
            names = ["complete", "unfinished", "indirect",
                     "unfinishedDefinition", "unsupported", "unbound"]
            for name in names:
                write_json(corpus / "nodes" / f"{name}.json", {
                    "id": name, "module": "Lemmatheca" if name != "unbound" else None,
                    "declaration": name if name != "unbound" else None, "axioms": [], "verified": False,
                })
            entry_file = corpus / "entries/example/entry.json"
            entry_file.parent.mkdir(parents=True)
            write_json(entry_file, {"id": "example", "title": "Example"})
            (entry_file.parent / "entry.html").write_text(
                '<section id="fact" data-kind="lemma" data-formal="complete unfinished indirect unbound">'
                '<h2>Example</h2><p>Proofs.</p></section>')

            def run_build():
                with override_settings(CORPUS_DIR=corpus, REPOSITORY_DIR=root):
                    return call_command("build", stdout=StringIO())

            def node(name):
                return read_json(corpus / "nodes" / f"{name}.json")

            self.assertEqual(
                run_build(), "Updated 6 nodes: 1 verified, 5 not verified.")
            self.assertFalse((corpus / "statistics.json").exists())
            self.assertEqual(read_json(entry_file)[
                             "formalization"]["label"], "25%")
            self.assertTrue(node("complete")["verified"])
            self.assertIn("complete", node("complete")["signature"])
            self.assertEqual(node("complete")["module"], "Lemmatheca.Examples")
            self.assertEqual(node("complete")["declaration_line"], 3)
            for name in ["unfinished", "indirect", "unfinishedDefinition"]:
                self.assertFalse(node(name)["verified"])
            self.assertFalse(node("unsupported")["verified"])
            self.assertFalse(node("unbound")["verified"])
            for name in names:
                self.assertFalse(
                    {"proven", "sorry", "approved", "source_module"} & node(name).keys())

            module.write_text(source.replace("by sorry", "by trivial", 1))
            self.assertEqual(
                run_build(), "Updated 6 nodes: 3 verified, 3 not verified.")
            self.assertEqual(read_json(entry_file)[
                             "formalization"]["label"], "75%")
            self.assertTrue(node("indirect")["verified"])

            # A proof can become unfinished again without failing the build.
            module.write_text(source)
            self.assertEqual(
                run_build(), "Updated 6 nodes: 1 verified, 5 not verified.")
            self.assertFalse(node("unfinished")["verified"])
            self.assertFalse(node("indirect")["verified"])
            self.assertEqual(read_json(entry_file)[
                             "formalization"]["label"], "25%")

            # A missing declaration is an error, not a vacuously sorry-free proof.
            record = node("complete")
            record["declaration"] = "doesNotExist"
            write_json(corpus / "nodes/complete.json", record)
            previous = {
                name: (corpus / "nodes" / f"{name}.json").read_bytes() for name in names}
            entry_before = entry_file.read_bytes()
            with self.assertRaises(CommandError):
                run_build()
            self.assertEqual(entry_file.read_bytes(), entry_before)
            self.assertFalse((corpus / "statistics.json").exists())
            for name in names:
                self.assertEqual(
                    (corpus / "nodes" / f"{name}.json").read_bytes(), previous[name])

            module.write_text(source + "\nthis is not Lean\n")
            with self.assertRaises(CommandError):
                run_build()
            self.assertEqual(entry_file.read_bytes(), entry_before)
            self.assertFalse((corpus / "statistics.json").exists())
            for name in names:
                self.assertEqual(
                    (corpus / "nodes" / f"{name}.json").read_bytes(), previous[name])


class AxiomVerificationTests(SimpleTestCase):
    def test_direct_inherited_and_type_axioms_against_node_allowances(self):
        with TemporaryDirectory() as directory:
            formal = Path(directory)
            (formal / "Lemmatheca").mkdir()
            shutil.copyfile(settings.REPOSITORY_DIR / "formal/lean-toolchain",
                            formal / "lean-toolchain")
            shutil.copyfile(settings.REPOSITORY_DIR / "formal/Lemmatheca/ProofStatus.lean",
                            formal / "Lemmatheca/ProofStatus.lean")
            (formal / "lakefile.toml").write_text(
                'name = "axiom_test"\n[[lean_lib]]\nname = "Lemmatheca"\n')
            (formal / "Lemmatheca/Examples.lean").write_text('''import Lemmatheca.ProofStatus
theorem complete : True := by trivial
noncomputable def selector {α : Sort u} (h : Nonempty α) : α := Classical.choice h
noncomputable def indirectSelector {α : Sort u} (h : Nonempty α) : α := selector h
theorem unfinished : True := by sorry
axiom assumption : False
theorem unsupported : False := assumption
noncomputable def chosenType : Type := Classical.choice (show Nonempty Type from ⟨Nat⟩)
theorem typeOnly (x : chosenType) : x = x := rfl
''')
            (formal / "Lemmatheca.lean").write_text("import Lemmatheca.Examples\n")
            corpus = formal / "corpus"
            (corpus / "nodes").mkdir(parents=True)
            # A shared declaration is checked against each node's own allowance.
            cases = [("complete", "complete", [], True),
                     ("selector", "selector", [], False),
                     ("selector-allowed", "selector", ["choice"], True),
                     ("indirect", "indirectSelector", [], False),
                     ("indirect-allowed",
                      "indirectSelector", ["choice"], True),
                     ("type-only", "typeOnly", [], False),
                     ("type-only-allowed", "typeOnly", ["choice"], True),
                     ("unfinished", "unfinished", ["choice"], False),
                     ("unsupported", "unsupported", ["choice"], False),
                     ("nat", "Nat.succ_ne_zero", [], True),
                     ("propext", "propext", [], True),
                     ("quotient", "Quot.sound", [], True)]
            for identifier, declaration, axioms, verified in cases:
                write_json(corpus / "nodes" / f"{identifier}.json", {
                    "id": identifier, "module": "Lemmatheca.Examples",
                    "declaration": declaration, "axioms": axioms, "verified": False})
            self.assertEqual(build(corpus, formal), (7, 12))
            for identifier, _, axioms, verified in cases:
                node = read_json(corpus / "nodes" / f"{identifier}.json")
                self.assertEqual(node["axioms"], axioms)
                self.assertEqual(node["verified"], verified)
                self.assertNotIn("lean_axioms", node)

            # Diagnostic reports still expose the full transitive kernel axioms.
            path = formal / "Report.lean"
            declarations = sorted(
                {declaration for _, declaration, _, _ in cases})
            path.write_text("import Lemmatheca.Examples\n" + "\n".join(
                f"#node_status {json.dumps(name)}" for name in declarations) + "\n")
            report = subprocess.run(["lake", "env", "lean", str(path)],
                                    cwd=formal, capture_output=True, text=True)
            self.assertEqual(report.returncode, 0,
                             report.stdout + report.stderr)
            results = {result["declaration"]: result for line in report.stdout.splitlines()
                       if line.startswith("NODE_STATUS ")
                       for result in [json.loads(line.removeprefix("NODE_STATUS "))]}
            self.assertEqual(results.keys(), set(declarations))
            for name in ("selector", "indirectSelector", "typeOnly"):
                self.assertIn("Classical.choice", results[name]["lean_axioms"])
            for name, axiom in (("unfinished", "sorryAx"), ("unsupported", "assumption")):
                self.assertFalse(results[name]["verified"])
                self.assertIn(axiom, results[name]["lean_axioms"])
            self.assertEqual(results["propext"]["lean_axioms"], ["propext"])
            self.assertEqual(results["Quot.sound"]
                             ["lean_axioms"], ["Quot.sound"])
