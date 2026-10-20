"""The single build command prepares a coherent snapshot before publishing it."""

from io import StringIO
import json
from pathlib import Path
import shutil
import subprocess
from tempfile import TemporaryDirectory
from unittest.mock import patch

from django.conf import settings
from django.core.management import call_command, CommandError, get_commands
from django.test import SimpleTestCase, override_settings

from catalog.files import read_json, write_json
from catalog.proofs import prepare_proof_results


class ProofPreparationTests(SimpleTestCase):
    def setUp(self):
        temporary = TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        (self.root / "nodes").mkdir()
        self.path = self.root / "nodes/example.json"
        write_json(self.path, {
            "id": "example", "module": "Lemmatheca", "declaration": "example",
            "verified": True, "signature": "example : True", "declaration_line": 5,
        })

    def test_preparation_returns_results_without_publishing_and_ignores_unrelated_files(self):
        before = self.path.read_bytes(), self.path.stat().st_mtime_ns
        (self.root / "statistics.json").write_text("not a statistics snapshot")
        output = 'NODE_STATUS {"declaration":"example","verified":false,"module":"Lemmatheca.Origin"}'
        with patch("catalog.proofs.subprocess.run",
                   return_value=subprocess.CompletedProcess([], 0, output)):
            prepared = prepare_proof_results(self.root, self.root)
        self.assertFalse(prepared["example"]["verified"])
        self.assertEqual(prepared["example"]["module"], "Lemmatheca.Origin")
        self.assertNotIn("signature", prepared["example"])
        self.assertNotIn("declaration_line", prepared["example"])
        self.assertEqual(before, (self.path.read_bytes(), self.path.stat().st_mtime_ns))
        self.assertEqual((self.root / "statistics.json").read_text(), "not a statistics snapshot")

    def test_compile_inspection_and_interruption_failures_preserve_saved_results(self):
        before = self.path.read_bytes(), self.path.stat().st_mtime_ns
        for error in (subprocess.CalledProcessError(1, "lake"), KeyboardInterrupt()):
            for first_result in ([], [subprocess.CompletedProcess([], 0)]):
                with self.subTest(error=type(error), inspecting=bool(first_result)), \
                        patch("catalog.proofs.subprocess.run", side_effect=[*first_result, error]):
                    with self.assertRaises(type(error)):
                        prepare_proof_results(self.root, self.root)
                    self.assertEqual(before, (self.path.read_bytes(), self.path.stat().st_mtime_ns))

    def test_missing_malformed_unknown_and_duplicate_results_are_rejected(self):
        before = self.path.read_bytes()
        outputs = ("", 'NODE_STATUS {"declaration":"example","verified":"true"}',
                   'NODE_STATUS []', 'NODE_STATUS {"verified":true}',
                   'NODE_STATUS {"declaration":[],"verified":true}',
                   'NODE_STATUS {"declaration":"example","verified":true,"typo":"value"}',
                   'NODE_STATUS {', 'NODE_STATUS {"declaration":"other","verified":true}',
                   'NODE_STATUS {"declaration":"example","verified":true}\n' * 2)
        for output in outputs:
            with self.subTest(output=output), patch("catalog.proofs.subprocess.run",
                    return_value=subprocess.CompletedProcess([], 0, output)):
                with self.assertRaises(ValueError):
                    prepare_proof_results(self.root, self.root)
                self.assertEqual(before, self.path.read_bytes())

    def test_unicode_modules_are_checked_and_concurrent_authored_metadata_is_preserved(self):
        module = "Lemmatheca.Δ"
        write_json(self.path, {**read_json(self.path), "module": module})

        def run(command, **kwargs):
            if command[:2] == ["lake", "build"]:
                self.assertIn(module, command)
                write_json(self.path, {**read_json(self.path), "description": "Edited during compilation."})
                return subprocess.CompletedProcess(command, 0)
            self.assertIn(f"import {module}\n", (self.root / command[-1]).read_text())
            output = 'NODE_STATUS ' + json.dumps({
                "declaration": "example", "verified": True, "module": module,
            })
            return subprocess.CompletedProcess(command, 0, output)

        with patch("catalog.proofs.subprocess.run", side_effect=run):
            result = prepare_proof_results(self.root, self.root)
        self.assertTrue(result["example"]["verified"])
        self.assertEqual(result["example"]["description"], "Edited during compilation.")
        # Preparation does not persist the generated removal of old fields.
        self.assertIn("signature", read_json(self.path))

    def test_changed_binding_discards_the_old_lean_result_without_saving(self):
        def run(command, **kwargs):
            write_json(self.path, {**read_json(self.path), "declaration": "other"})
            return subprocess.CompletedProcess(command, 0,
                'NODE_STATUS {"declaration":"example","verified":true}')

        with patch("catalog.proofs.subprocess.run", side_effect=run):
            result = prepare_proof_results(self.root, self.root)
        self.assertEqual(result["example"]["declaration"], "other")
        self.assertFalse(result["example"]["verified"])
        self.assertNotIn("signature", result["example"])
        self.assertTrue(read_json(self.path)["verified"])


class BuildCommandTests(SimpleTestCase):
    def setUp(self):
        temporary = TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name).resolve()
        self.corpus, self.formal = self.root / "corpus", self.root / "formal"
        (self.corpus / "nodes").mkdir(parents=True)
        self.formal.mkdir()
        write_json(self.corpus / "taxonomy.json", {"areas": [{
            "id": "area", "title": "Area", "parent": None, "description": "An area.",
        }]})
        write_json(self.corpus / "area_entries.json", {"areas": {"area": ["example"]}})
        self.node = self.corpus / "nodes/proof.json"
        self.planned = self.corpus / "nodes/planned.json"
        write_json(self.node, {
            "id": "proof", "description": "A bound proof.", "dependencies": [],
            "module": "Lemmatheca.Example", "declaration": "Example.fact",
            "verified": True, "signature": "Example.fact : True", "declaration_line": 3,
        })
        write_json(self.planned, {
            "id": "planned", "description": "A planned proof.", "dependencies": [],
            "module": None, "declaration": None,
        })
        self.entry = self.corpus / "entries/example/entry.json"
        self.entry.parent.mkdir(parents=True)
        write_json(self.entry, {
            "id": "example", "title": "Example", "primary_area": "area", "additional_areas": [],
            "based_on": [], "reading_time": 5, "summary": "A summary.", "abstract": "An abstract.",
        })
        self.html = self.entry.with_name("entry.html")
        self.html.write_text('<section id="fact" data-kind="lemma" data-formal="proof planned">'
                             '<h2>A fact</h2><p>A fact.</p></section>')
        self.source = self.corpus / "source-errors/sources/book.json"
        self.finding = self.corpus / "source-errors/findings/BOOK-01.json"
        self.plan = self.corpus / "reference-planning/records/future.json"
        for path in (self.source, self.finding, self.plan):
            path.parent.mkdir(parents=True)
        write_json(self.source, {
            "id": "book", "publication": "A book, edition 1.", "urls": ["https://example.com/book"],
            "entry_refs": ["example#fact"], "finding_ids": ["BOOK-01"],
            "reviews": [{"checked_passages": "Chapter 1.", "consumers": "Example.",
                         "outcome": "Repaired.", "checked_on": "2026-10-20"}],
        })
        write_json(self.finding, {
            "id": "BOOK-01", "title": "An incorrect bound", "source_ids": ["book"],
            "severity": "serious", "details": "A repair.", "entry_refs": ["example#fact"],
            "related_findings": [],
        })
        write_json(self.plan, {
            "id": "future", "kind": "planned-entry", "title": "Future entry", "areas": ["area"],
            "entry_refs": ["example#fact"], "urls": [], "details": "Pending scope.",
            "planned_entry_ids": ["future-entry"],
        })
        for directory in ("source-errors", "reference-planning"):
            write_json(self.corpus / directory / "policy.json", {"scope": "Scoped records."})
        self.index = self.corpus / "index.json"
        self.catalogs = [self.corpus / "source-errors/index.json",
                         self.corpus / "reference-planning/index.json"]
        override = override_settings(CORPUS_DIR=self.corpus, REPOSITORY_DIR=self.root,
                                     CORPUS_INDEX_PATH=None)
        override.enable()
        self.addCleanup(override.disable)

    def snapshot(self):
        return {path.relative_to(self.root): (path.read_bytes(), path.stat().st_mtime_ns)
                for path in self.root.rglob("*") if path.is_file()}

    def command(self, *args):
        output = StringIO()
        call_command("build", *args, stdout=output)
        return output.getvalue()

    def lean(self, verified=True, *, fail_at=None):
        def run(command, **kwargs):
            self.assertEqual(kwargs["cwd"], self.formal)
            self.assertTrue(kwargs["check"])
            compiling = command[:2] == ["lake", "build"]
            if fail_at == ("compile" if compiling else "inspect"):
                raise subprocess.CalledProcessError(1, command, output="Lean failed")
            if compiling:
                return subprocess.CompletedProcess(command, 0)
            self.assertEqual(command[:3], ["lake", "env", "lean"])
            self.assertIn('#node_status "Example.fact"', (self.formal / command[-1]).read_text())
            output = "NODE_STATUS " + json.dumps({
                "declaration": "Example.fact", "verified": verified,
                "module": "Lemmatheca.Example", "signature": "Example.fact : True",
                "declaration_line": 3,
            })
            return subprocess.CompletedProcess(command, 0, output)
        return patch("catalog.proofs.subprocess.run", side_effect=run)

    def test_no_lean_refresh_preserves_proofs_defaults_missing_status_and_builds_all_outputs(self):
        proof_before = read_json(self.node)
        with patch("subprocess.run", side_effect=AssertionError("No Lean")):
            output = self.command("--no-lean")
        self.assertIn("Corpus valid: 1 entries, 2 nodes, 1 areas.", output)
        self.assertIn("1 of 2 nodes verified.", output)
        self.assertNotIn("counts", read_json(self.index))
        self.assertEqual(read_json(self.node), proof_before)
        self.assertFalse(read_json(self.planned)["verified"])
        summary = read_json(self.entry)["formalization"]
        self.assertEqual((summary["complete"], summary["total"], summary["label"]), (1, 2, "50%"))
        self.assertEqual(read_json(self.entry)["title"], "Example")
        self.assertEqual(read_json(self.index)["node_consumers"]["proof"], ["example#fact"])
        self.assertEqual(read_json(self.catalogs[0])["by_entry"]["example"], ["book"])
        self.assertIn("future", read_json(self.catalogs[1])["records"])
        self.assertFalse((self.corpus / "statistics.json").exists())

    def test_read_only_no_lean_check_accepts_missing_generated_outputs_and_lean_installation(self):
        record = read_json(self.node)
        record.pop("verified")
        write_json(self.node, record)
        self.formal.rmdir()
        before = self.snapshot()
        with patch("subprocess.run", side_effect=AssertionError("No Lean")), \
                patch("catalog.node_files.read_nodes", side_effect=AssertionError("No whole node catalog")), \
                patch("catalog.sources.render_block", side_effect=AssertionError("No rendering")):
            self.command("--no-lean", "--check")
        self.assertEqual(self.snapshot(), before)
        self.assertFalse(self.index.exists())
        self.assertTrue(all(not path.exists() for path in self.catalogs))
        self.assertNotIn("formalization", read_json(self.entry))
        self.assertNotIn("verified", read_json(self.node))

    def test_no_lean_check_ignores_stale_derived_catalogs_but_still_checks_authored_refs(self):
        for path in self.catalogs:
            path.write_text("obsolete generated cache")
        self.index.write_text("obsolete index")
        before = self.snapshot()
        with patch("subprocess.run", side_effect=AssertionError("No Lean")):
            self.command("--no-lean", "--check")
        self.assertEqual(self.snapshot(), before)
        write_json(self.source, {**read_json(self.source), "entry_refs": ["example#missing"]})
        invalid_before = self.snapshot()
        with self.assertRaisesRegex(CommandError, "Unknown referenced block"), self.lean() as external:
            self.command()
        external.assert_not_called()
        self.assertEqual(self.snapshot(), invalid_before)

    def test_removed_binding_is_structurally_checkable_and_no_lean_refresh_clears_old_results(self):
        with self.lean():
            self.command()
        stale = {**read_json(self.node), "module": None, "declaration": None}
        write_json(self.node, stale)
        before = self.snapshot()
        with patch("subprocess.run", side_effect=AssertionError("No Lean")):
            self.command("--no-lean", "--check")
            self.assertEqual(self.snapshot(), before)
            self.command("--no-lean")
        current = read_json(self.node)
        self.assertFalse(current["verified"])
        self.assertNotIn("signature", current)
        self.assertNotIn("declaration_line", current)
        self.assertEqual(read_json(self.entry)["formalization"]["label"], "0%")

    def test_reserved_index_is_not_an_input_and_authored_edits_change_revision(self):
        with patch("subprocess.run", side_effect=AssertionError("No Lean")):
            self.command("--no-lean")
            first = read_json(self.index)
            self.command("--no-lean")
            self.assertEqual(read_json(self.index)["revision"], first["revision"])
            self.index.write_text("not even JSON")
            self.command("--no-lean")
            self.assertEqual(read_json(self.index)["revision"], first["revision"])
            write_json(self.node, {**read_json(self.node), "description": "Updated authored description."})
            self.command("--no-lean")
        current = read_json(self.index)
        self.assertNotEqual(current["revision"], first["revision"])
        self.assertNotIn("counts", current)
        self.assertEqual({key: value for key, value in current.items() if key != "revision"},
                         {key: value for key, value in first.items() if key != "revision"})
        self.assertTrue(read_json(self.node)["verified"])

    def test_index_override_and_configured_external_destination(self):
        configured, explicit = self.root / "cache/configured.json", self.root / "cache/explicit.json"
        with override_settings(CORPUS_INDEX_PATH=configured), \
                patch("subprocess.run", side_effect=AssertionError("No Lean")):
            self.command("--no-lean", "--index", str(explicit))
            self.assertTrue(explicit.exists())
            self.assertFalse(configured.exists())
            self.command("--no-lean")
        self.assertTrue(configured.exists())
        self.assertFalse(self.index.exists())
        self.assertEqual(read_json(explicit)["revision"], read_json(configured)["revision"])

    def test_symlink_corpus_build_matches_physical_root_and_checks_remain_read_only(self):
        alias = self.root / "corpus-alias"
        alias.symlink_to(self.corpus, target_is_directory=True)
        before = self.snapshot()
        with override_settings(CORPUS_DIR=alias, CORPUS_INDEX_PATH=alias / "index.json"), \
                patch("subprocess.run", side_effect=AssertionError("No Lean")):
            self.command("--no-lean")
        from_alias = read_json(self.index)
        after = self.snapshot()
        self.assertEqual(set(after) - set(before), {
            path.relative_to(self.root) for path in (self.index, *self.catalogs)
        })
        self.assertEqual({path for path in before if before[path] != after[path]}, {
            self.entry.relative_to(self.root), self.planned.relative_to(self.root),
        })
        with patch("subprocess.run", side_effect=AssertionError("No Lean")):
            self.command("--no-lean")
        self.assertEqual(read_json(self.index), from_alias)
        before_checks = self.snapshot()
        with override_settings(CORPUS_DIR=alias, CORPUS_INDEX_PATH=alias / "index.json"):
            with patch("subprocess.run", side_effect=AssertionError("No Lean")):
                self.command("--no-lean", "--check")
            self.assertEqual(self.snapshot(), before_checks)
            with self.lean() as external:
                self.command("--check")
            self.assertEqual(external.call_count, 2)
        self.assertEqual(self.snapshot(), before_checks)

    def test_index_collision_and_symlink_cannot_overwrite_authored_inputs(self):
        alias = self.root / "corpus-alias"
        alias.symlink_to(self.corpus, target_is_directory=True)
        destinations = (self.node, self.entry, self.catalogs[0], self.corpus / "cache.json",
                        alias / "entries/example/entry.json")
        before = self.snapshot()
        for destination in destinations:
            with self.subTest(destination=destination), self.lean() as external:
                with self.assertRaises(CommandError):
                    self.command("--index", str(destination))
                external.assert_not_called()
                self.assertEqual(self.snapshot(), before)

    def test_source_file_checks_are_opt_in_and_do_not_need_a_lean_process(self):
        before = self.snapshot()
        with patch("subprocess.run", side_effect=AssertionError("No Lean")):
            self.command("--no-lean", "--check")
            with self.assertRaisesRegex(CommandError, "Missing Lean source"):
                self.command("--no-lean", "--check", "--check-sources")
        self.assertEqual(self.snapshot(), before)
        source = self.formal / "Lemmatheca/Example.lean"
        source.parent.mkdir()
        source.write_text("theorem Example.fact : True := True.intro\n")
        before = self.snapshot()
        with patch("subprocess.run", side_effect=AssertionError("No Lean")):
            self.command("--no-lean", "--check", "--check-sources")
        self.assertEqual(self.snapshot(), before)

    def test_full_refresh_and_lean_failure_preserve_the_last_published_snapshot(self):
        with self.lean(False) as external:
            self.command()
        self.assertEqual(external.call_count, 2)
        self.assertFalse(read_json(self.node)["verified"])
        self.assertEqual(read_json(self.entry)["formalization"]["label"], "0%")
        with self.lean(True):
            self.command()
        self.assertTrue(read_json(self.node)["verified"])
        self.assertEqual(read_json(self.entry)["formalization"]["label"], "50%")
        before = self.snapshot()
        for fail_at in ("compile", "inspect"):
            with self.subTest(fail_at=fail_at), self.lean(fail_at=fail_at):
                with self.assertRaisesRegex(CommandError, "Lean failed"):
                    self.command()
                self.assertEqual(self.snapshot(), before)

    def test_invalid_authored_links_and_dependencies_fail_before_lean(self):
        changes = ((self.html, lambda: self.html.write_text(
            self.html.read_text().replace("A fact.</p>", '<a href="example#missing">Bad</a></p>'))),
            (self.node, lambda: write_json(self.node, {**read_json(self.node), "dependencies": ["missing"]})))
        for path, change in changes:
            original = path.read_bytes()
            try:
                change()
                before = self.snapshot()
                with self.lean() as external, self.assertRaises(CommandError):
                    self.command()
                external.assert_not_called()
                self.assertEqual(self.snapshot(), before)
            finally:
                path.write_bytes(original)

    def test_invalid_prepared_node_prevents_every_metadata_and_catalog_write(self):
        with patch("subprocess.run", side_effect=AssertionError("No Lean")):
            self.command("--no-lean")
        from catalog.node_files import read_nodes
        prepared = read_nodes(self.corpus)
        prepared["proof"] = {**prepared["proof"], "verified": False, "signature": 17}
        before = self.snapshot()
        with patch("catalog.build.prepare_proof_results", return_value=prepared), \
                self.assertRaises(CommandError):
            self.command()
        self.assertEqual(self.snapshot(), before)

    def test_index_preparation_failure_leaves_the_published_metadata_unchanged(self):
        with patch("subprocess.run", side_effect=AssertionError("No Lean")):
            self.command("--no-lean")
        before = self.snapshot()
        with self.lean(False), \
                patch("catalog.build.CorpusIndex.finish", side_effect=ValueError("Cannot prepare index")), \
                self.assertRaisesRegex(CommandError, "Cannot prepare index"):
            self.command()
        self.assertEqual(self.snapshot(), before)

    def test_authored_metadata_edits_during_lean_survive_proof_and_summary_refresh(self):
        with self.lean(False) as external:
            inspect = external.side_effect

            def edit_during_compile(command, **kwargs):
                result = inspect(command, **kwargs)
                if command[:2] == ["lake", "build"]:
                    write_json(self.node, {**read_json(self.node), "description": "Concurrent edit."})
                    write_json(self.entry, {**read_json(self.entry), "reading_time": 15})
                return result

            external.side_effect = edit_during_compile
            self.command()
        self.assertEqual(read_json(self.node)["description"], "Concurrent edit.")
        self.assertFalse(read_json(self.node)["verified"])
        self.assertEqual(read_json(self.entry)["reading_time"], 15)
        self.assertEqual(read_json(self.entry)["formalization"]["label"], "0%")

    def test_references_edited_during_lean_are_rechecked_before_publication(self):
        with patch("subprocess.run", side_effect=AssertionError("No Lean")):
            self.command("--no-lean")
        valid_html = self.html.read_text()
        expected = None
        with self.lean(False) as external:
            inspect = external.side_effect

            def edit_during_compile(command, **kwargs):
                nonlocal expected
                result = inspect(command, **kwargs)
                if command[:2] == ["lake", "build"]:
                    self.html.write_text(valid_html.replace("A fact.</p>",
                        '<a href="example#missing">Edited reference</a></p>'))
                    expected = self.snapshot()
                return result

            external.side_effect = edit_during_compile
            with self.assertRaisesRegex(CommandError, "mathematical block"):
                self.command()
        self.assertIsNotNone(expected)
        self.assertEqual(self.snapshot(), expected)

    def test_full_check_detects_stale_proof_fields_summaries_and_catalogs_without_saving(self):
        with self.lean():
            self.command()
        for path, field, value in (
                (self.node, "verified", False), (self.node, "signature", "Old signature"),
                (self.node, "declaration_line", 99), (self.node, "module", "Lemmatheca.Old"),
                (self.entry, "formalization", {**read_json(self.entry)["formalization"], "label": "Old label"}),
                (self.catalogs[0], "by_entry", {})):
            with self.subTest(path=path, field=field):
                original = path.read_bytes()
                write_json(path, {**read_json(path), field: value})
                before = self.snapshot()
                with self.lean(), self.assertRaisesRegex(CommandError, "[Ss]tale|[Oo]utdated|[Dd]iffer"):
                    self.command("--check")
                self.assertEqual(self.snapshot(), before)
                path.write_bytes(original)

    def test_full_check_accepts_current_saved_index_and_writes_nothing(self):
        with self.lean():
            self.command()
        # Snapshot equality is semantic; formatting alone need not trigger a rebuild.
        self.index.write_text(json.dumps(read_json(self.index), sort_keys=True))
        before = self.snapshot()
        with self.lean() as external:
            output = self.command("--check")
        self.assertIn("Corpus valid: 1 entries, 2 nodes, 1 areas.", output)
        self.assertEqual(external.call_count, 2)
        self.assertEqual(self.snapshot(), before)

    def test_full_check_rejects_missing_malformed_and_modified_saved_index_without_writes(self):
        with self.lean():
            self.command()
        original = self.index.read_bytes()
        current = read_json(self.index)
        cases = (
            ("missing", None), ("malformed", "not JSON"), ("not an object", "[]"),
            ("changed revision", json.dumps({**current, "revision": "0" * 64})),
            ("changed relationships", json.dumps({**current, "node_consumers": {}})),
            ("unexpected counts", json.dumps({**current, "counts": {"nodes": 2}})),
        )
        for order in (True, 1.0):
            wrong_type = {**current, "blocks": {**current["blocks"], "example#fact": {
                **current["blocks"]["example#fact"], "order": order,
            }}}
            cases += ((f"block order has type {type(order).__name__}", json.dumps(wrong_type)),)
        for name, contents in cases:
            with self.subTest(index=name):
                if contents is None:
                    self.index.unlink()
                else:
                    self.index.write_text(contents)
                before = self.snapshot()
                try:
                    with self.lean(), self.assertRaisesRegex(CommandError, r"index\.json"):
                        self.command("--check")
                    self.assertEqual(self.snapshot(), before)
                finally:
                    self.index.write_bytes(original)

    def test_full_check_accepts_valid_statistics_changes_but_rejects_invalid_statistics(self):
        with self.lean():
            self.command()
        index_before = self.index.read_bytes()
        statistics = self.corpus / "statistics.json"
        snapshot = {"entries": 1, "verified_entries": 0, "nodes": 2,
                    "verified_nodes": 1, "contributors": 3}
        for data in (snapshot, {**snapshot, "verified_nodes": 2, "contributors": 4}):
            with self.subTest(statistics=data):
                write_json(statistics, data)
                before = self.snapshot()
                with self.lean():
                    self.command("--check")
                self.assertEqual(self.snapshot(), before)
                self.assertEqual(self.index.read_bytes(), index_before)
        write_json(statistics, {**snapshot, "nodes": "two"})
        before = self.snapshot()
        with self.lean() as external, self.assertRaisesRegex(CommandError, r"statistics\.json"):
            self.command("--check")
        external.assert_not_called()
        self.assertEqual(self.snapshot(), before)

    def test_full_check_detects_index_revision_staleness_after_authored_prose_changes(self):
        with self.lean():
            self.command()
        current = read_json(self.index)
        self.html.write_text(self.html.read_text().replace("A fact.</p>", "A revised fact.</p>"))
        before = self.snapshot()
        with self.lean(), self.assertRaisesRegex(CommandError, r"index\.json"):
            self.command("--check")
        self.assertEqual(self.snapshot(), before)
        self.assertEqual(read_json(self.index), current)

    def test_full_check_checks_the_selected_index_without_falling_back_to_default(self):
        with self.lean():
            self.command()
        selected, explicit = self.root / "selected.json", self.root / "explicit.json"
        current = read_json(self.index)
        before = self.snapshot()
        with self.lean(), self.assertRaisesRegex(CommandError, r"selected\.json"):
            self.command("--check", "--index", str(selected))
        self.assertEqual(self.snapshot(), before)
        write_json(selected, current)
        # A broken default cannot invalidate a current, explicitly selected index.
        self.index.write_text("obsolete default")
        before = self.snapshot()
        with self.lean():
            self.command("--check", "--index", str(selected))
        self.assertEqual(self.snapshot(), before)
        with override_settings(CORPUS_INDEX_PATH=selected):
            with self.lean():
                self.command("--check")
            self.assertEqual(self.snapshot(), before)
            # An explicit override wins over a current configured destination.
            with self.lean(), self.assertRaisesRegex(CommandError, r"explicit\.json"):
                self.command("--check", "--index", str(explicit))
            self.assertEqual(self.snapshot(), before)

    def test_no_lean_check_does_not_require_a_current_selected_index(self):
        selected = self.root / "selected.json"
        for contents in (None, "not JSON", '{"revision":"obsolete"}'):
            with self.subTest(contents=contents):
                if contents is not None:
                    selected.write_text(contents)
                before = self.snapshot()
                with patch("subprocess.run", side_effect=AssertionError("No Lean")):
                    self.command("--no-lean", "--check", "--index", str(selected))
                self.assertEqual(self.snapshot(), before)

    def test_legacy_commands_are_removed(self):
        get_commands.cache_clear()
        commands = get_commands()
        self.assertNotIn("validate_corpus", commands)
        self.assertNotIn("index_authoring_records", commands)


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
