"""Statistics history is built once from Git, then records only changed counts."""

from copy import deepcopy
from io import StringIO
import os
from pathlib import Path
import subprocess
from tempfile import TemporaryDirectory
from unittest.mock import patch

from django.core.management import call_command, CommandError
from django.test import SimpleTestCase, override_settings

from catalog.files import read_json, write_json
from catalog.statistics import append_counts, contributor_count, history_from_git, prepare_statistics
from catalog.validation import validate_statistics


class ContributorTests(SimpleTestCase):
    def test_author_names_and_mailmap_avoid_counting_email_aliases_twice(self):
        with TemporaryDirectory() as directory:
            root = Path(directory)

            def git(*args):
                return subprocess.run(
                    ["git", "-c", "commit.gpgsign=false", "-c",
                        "core.hooksPath=/dev/null", *args],
                    cwd=root, check=True, capture_output=True, text=True)

            git("init", "--quiet")
            for name, email in [("Alice", "alice@example.test"),
                                ("Alice", "alias@example.test"),
                                ("A. Example", "third@example.test"),
                                ("Bob", "bob@example.test"),
                                ("github-actions[bot]",
                                 "actions@example.test"),
                                ("dependabot[bot]", "dependabot@example.test")]:
                git("-c", f"user.name={name}", "-c", f"user.email={email}",
                    "commit", "--allow-empty", "--quiet", "-m", "Example")
            (root / ".mailmap").write_text(
                "Alice <alice@example.test> A. Example <third@example.test>\n")
            self.assertEqual(contributor_count(root), 2)

            # A shallow history is incomplete: keep the published count.
            head = git("rev-parse", "HEAD").stdout
            (root / ".git/shallow").write_text(head)
            self.assertEqual(contributor_count(root, previous=7), 7)

    def test_source_archive_uses_saved_count_or_unknown(self):
        with TemporaryDirectory() as directory:
            self.assertEqual(contributor_count(Path(directory), previous=3), 3)
            self.assertIsNone(contributor_count(Path(directory)))


class StatisticsHistoryTests(SimpleTestCase):
    def setUp(self):
        temporary = TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.corpus = self.root / "corpus"
        (self.corpus / "nodes").mkdir(parents=True)
        (self.corpus / "entries/alpha").mkdir(parents=True)
        self.entries = {"alpha": {}}
        self.summaries = {"alpha": {"complete": 0, "total": 1, "unmapped_blocks": 0}}
        self.nodes = {"proof": {"module": "Test.Proof", "declaration": "Test.proof"}}
        self.results = {"proof": {"binding": ["Test.Proof", "Test.proof"], "verified": False}}
        self.save_records()
        write_json(self.corpus / "taxonomy.json", {"areas": [{"id": "area"}]})

    def git(self, *args, **kwargs):
        return subprocess.run(["git", "-c", "commit.gpgsign=false", "-c", "core.hooksPath=/dev/null", *args],
                              cwd=self.root, check=True, capture_output=True, text=True, **kwargs).stdout

    def commit(self, day, name="Alice"):
        if not (self.root / ".git").exists():
            self.git("init", "--quiet", "--initial-branch=main")
        self.git("add", "--all")
        at = f"2026-01-{day:02d}T12:00:00+00:00"
        self.git("-c", f"user.name={name}", "-c", f"user.email={name.lower()}@example.test",
                 "commit", "--quiet", "--allow-empty", "-m", "Snapshot",
                 env={**os.environ, "GIT_AUTHOR_DATE": at, "GIT_COMMITTER_DATE": at})
        return at

    def save_records(self):
        for identifier, entry in self.entries.items():
            path = self.corpus / "entries" / identifier / "entry.json"
            path.parent.mkdir(parents=True, exist_ok=True)
            write_json(path, entry)
        for identifier, node in self.nodes.items():
            write_json(self.corpus / "nodes" / f"{identifier}.json", node)
        document = {key: {} for key in (
            "blocks", "anchors", "nodes_by_declaration", "module_nodes", "node_consumers",
            "hint_dependents", "outgoing", "incoming")}
        document.update({
            "schema_version": 7, "revision": "0" * 64, "references": [],
            "nodes": self.results,
            "entries": {identifier: {"blocks": ["block"], "reading_position": 1,
                                     "lean_line_count": 0, "formalization": summary}
                        for identifier, summary in self.summaries.items()},
        })
        write_json(self.corpus / "index.json", document)

    def refresh(self):
        with override_settings(CORPUS_DIR=self.corpus, REPOSITORY_DIR=self.root):
            return call_command("update_statistics", stdout=StringIO())

    def published_snapshot(self):
        # Refresh tests start from published data; Git replay has its own tests.
        snapshot = {"entries": 1, "verified_entries": 0, "nodes": 1,
                    "verified_nodes": 0, "areas": 1, "contributors": 1}
        snapshot["history"] = {
            key: [{"at": "2026-01-01T12:00:00+00:00", "count": 1,
                   **({"verified": 0} if key in {"entries", "nodes"} else {})}]
            for key in ("entries", "nodes", "areas", "contributors")}
        write_json(self.corpus / "statistics.json", snapshot)
        return snapshot

    def test_git_replays_changes_deletions_and_renames_without_rendering(self):
        first = self.commit(1)
        self.results["proof"]["verified"] = True
        self.summaries["alpha"]["complete"] = 1
        self.save_records()
        second = self.commit(2)
        (self.corpus / "nodes/proof.json").unlink()
        self.nodes["renamed"] = self.nodes.pop("proof")
        self.results["renamed"] = self.results.pop("proof")
        self.save_records()
        self.commit(3)
        self.entries["beta"] = {}
        self.summaries["beta"] = {"complete": 0, "total": 1, "unmapped_blocks": 0}
        self.nodes["pending"] = {"module": "Test.Pending", "declaration": "Test.pending"}
        self.results["pending"] = {"binding": ["Test.Pending", "Test.pending"], "verified": False}
        self.save_records()
        write_json(self.corpus / "taxonomy.json", {"areas": [{}, {}]})
        fourth = self.commit(4, "Bob")
        (self.corpus / "entries/alpha/entry.json").unlink()
        (self.corpus / "nodes/renamed.json").unlink()
        fifth = self.commit(5)
        with patch("django.template.loader.render_to_string", side_effect=AssertionError("No rendering")), \
                patch("catalog.sources.parse_source", side_effect=AssertionError("No entry HTML parsing")):
            history = history_from_git(self.corpus, self.root)
        self.assertEqual(
            set(history), {"entries", "nodes", "areas", "contributors"})
        self.assertEqual(history["entries"], [{"at": first, "count": 1, "verified": 0},
                                              {"at": second, "count": 1,
                                                  "verified": 1},
                                              {"at": fourth, "count": 2,
                                                  "verified": 1},
                                              {"at": fifth, "count": 1, "verified": 0}])
        self.assertEqual(history["nodes"], history["entries"])
        self.assertEqual(history["areas"], [
                         {"at": first, "count": 1}, {"at": fourth, "count": 2}])
        self.assertEqual(history["contributors"], [
                         {"at": first, "count": 1}, {"at": fourth, "count": 2}])

    def test_legacy_node_totals_do_not_confuse_reviews_with_proofs(self):
        (self.corpus / "nodes/proof.json").unlink()
        legacy = self.root / "formal/nodes/proof.json"
        legacy.parent.mkdir(parents=True)
        write_json(legacy, {"reviewed": True})
        write_json(self.corpus / "entries/alpha/entry.json",
                   {"status": "approved"})
        (self.corpus / "index.json").unlink()
        first = self.commit(1)
        legacy.unlink()
        self.save_records()
        self.commit(2)
        history = history_from_git(self.corpus, self.root)
        self.assertEqual(history["nodes"], [
                         {"at": first, "count": 1, "verified": 0}])
        self.assertEqual(history["entries"], history["nodes"])

    def test_git_migration_preserves_legacy_verification_and_tracks_index_only_changes(self):
        self.entries["alpha"] = {"formalization": {"status": "complete"}}
        self.save_records()
        # The old structural index did not carry generated entry summaries.
        write_json(self.corpus / "index.json", {
            "schema_version": 5, "entries": {"alpha": {"blocks": []}},
        })
        first = self.commit(1)
        self.entries["alpha"] = {}
        self.summaries["alpha"]["complete"] = 1
        self.save_records()
        self.commit(2)
        # Only the index changes. Every currently bound node is verified, but
        # this entry still has a block whose mapping has not been supplied.
        self.summaries["alpha"]["unmapped_blocks"] = 1
        self.save_records()
        third = self.commit(3)
        history = history_from_git(self.corpus, self.root)
        self.assertEqual(history["entries"], [
            {"at": first, "count": 1, "verified": 1},
            {"at": third, "count": 1, "verified": 0},
        ])

    def test_git_node_migration_tracks_index_results_and_rejects_stale_bindings(self):
        # Older node records, including records without a binding, carried their
        # own proof flag. A schema-6 index supplied entry counts only.
        write_json(self.corpus / "nodes/proof.json", {"verified": True})
        write_json(self.corpus / "index.json", {
            "schema_version": 6, "entries": {"alpha": {
                "formalization": self.summaries["alpha"]}},
        })
        first = self.commit(1)
        self.results["proof"]["verified"] = True
        self.save_records()
        self.commit(2)
        self.results["proof"]["verified"] = False
        self.save_records()
        third = self.commit(3)
        self.results["proof"]["verified"] = True
        self.save_records()
        fourth = self.commit(4)
        self.nodes["proof"]["declaration"] = "Test.changed"
        self.save_records()
        fifth = self.commit(5)
        self.nodes["proof"] = {}
        self.results["proof"] = {"binding": [None, None], "verified": True}
        self.save_records()
        self.commit(6)
        self.assertEqual(history_from_git(self.corpus, self.root)["nodes"], [
            {"at": first, "count": 1, "verified": 1},
            {"at": third, "count": 1, "verified": 0},
            {"at": fourth, "count": 1, "verified": 1},
            {"at": fifth, "count": 1, "verified": 0},
        ])

    def test_merge_counts_corpus_once_and_includes_branch_authors(self):
        self.commit(1)
        self.git("checkout", "--quiet", "-b", "contribution")
        self.nodes["new"] = {"module": "Test.New", "declaration": "Test.new"}
        self.results["new"] = {"binding": ["Test.New", "Test.new"], "verified": False}
        self.save_records()
        self.commit(2, "Bob")
        self.git("checkout", "--quiet", "main")
        self.commit(3)
        self.git("-c", "user.name=Alice", "-c", "user.email=alice@example.test", "merge",
                 "--quiet", "--no-ff", "contribution", "-m", "Merge contribution",
                 env={**os.environ, "GIT_AUTHOR_DATE": "2026-01-04T12:00:00+00:00",
                      "GIT_COMMITTER_DATE": "2026-01-04T12:00:00+00:00"})
        history = history_from_git(self.corpus, self.root)
        self.assertEqual([point["count"]
                         for point in history["nodes"]], [1, 2])
        self.assertEqual(history["nodes"][-1]["at"],
                         "2026-01-04T12:00:00+00:00")
        self.assertEqual(history["contributors"][-1]["count"], 2)
        self.refresh()
        self.assertEqual(
            read_json(self.corpus / "statistics.json")["contributors"], 2)

    def test_refresh_appends_only_changed_counts_and_preserves_history(self):
        first = self.published_snapshot()
        validate_statistics(first)
        with patch("catalog.statistics.history_from_git", side_effect=AssertionError("Already imported")), \
                patch("catalog.statistics.timestamp", return_value="2026-02-02T12:00:00+00:00"):
            self.assertEqual(prepare_statistics(
                self.corpus, self.root), first)
            self.results["proof"]["verified"] = True
            self.save_records()
            changed = prepare_statistics(
                self.corpus, self.root)
        expected = deepcopy(first["history"])
        expected["nodes"].append(
            {"at": "2026-02-02T12:00:00+00:00", "count": 1, "verified": 1})
        self.assertEqual(changed["history"], expected)
        validate_statistics(changed)

    def test_refresh_reads_saved_counts_without_lean_or_html(self):
        self.published_snapshot()
        self.summaries["alpha"]["complete"] = 1
        self.entries["draft"] = {}
        self.summaries["draft"] = {"complete": 0, "total": 0, "unmapped_blocks": 1}
        self.results["proof"]["verified"] = True
        self.save_records()
        records = {path: path.read_bytes() for path in self.corpus.glob("**/*.json")
                   if path.name != "statistics.json"}
        with patch("catalog.proofs.prepare_proof_results", side_effect=AssertionError("No Lean build")), \
                patch("catalog.sources.parse_source", side_effect=AssertionError("No HTML parsing")):
            self.refresh()
        snapshot = read_json(self.corpus / "statistics.json")
        self.assertEqual({key: snapshot[key] for key in ("entries", "verified_entries", "nodes", "verified_nodes")},
                         {"entries": 2, "verified_entries": 1, "nodes": 1, "verified_nodes": 1})
        self.assertEqual({path: path.read_bytes()
                         for path in records}, records)
        validate_statistics(snapshot)

    def test_refresh_only_trusts_index_results_for_the_current_bound_declaration(self):
        self.published_snapshot()
        self.nodes["proof"]["verified"] = True
        self.save_records()
        self.assertEqual(prepare_statistics(self.corpus, self.root)["verified_nodes"], 0)
        self.results["proof"]["verified"] = True
        self.save_records()
        self.assertEqual(prepare_statistics(self.corpus, self.root)["verified_nodes"], 1)
        self.nodes["proof"]["declaration"] = "Test.changed"
        self.save_records()
        self.assertEqual(prepare_statistics(self.corpus, self.root)["verified_nodes"], 0)
        self.nodes["proof"] = {}
        self.save_records()
        self.assertEqual(prepare_statistics(self.corpus, self.root)["verified_nodes"], 0)

    def test_only_nonempty_fully_verified_mapped_entries_count_as_verified(self):
        self.published_snapshot()
        self.entries = {identifier: {} for identifier in ("alpha", "unmapped", "na")}
        # Old generated fields no longer determine the current snapshot.
        self.entries["alpha"]["formalization"] = {"status": "partial"}
        self.summaries = {
            "alpha": {"complete": 1, "total": 1, "unmapped_blocks": 0},
            "unmapped": {"complete": 1, "total": 1, "unmapped_blocks": 1},
            "na": {"complete": 0, "total": 0, "unmapped_blocks": 0},
        }
        self.save_records()
        snapshot = prepare_statistics(self.corpus, self.root)
        self.assertEqual((snapshot["entries"], snapshot["verified_entries"]), (3, 1))

    def test_refresh_requires_saved_entry_counts_and_preserves_snapshot_on_bad_index(self):
        self.published_snapshot()
        published = (self.corpus / "statistics.json").read_bytes()
        index = self.corpus / "index.json"
        valid = read_json(index)
        index.unlink()
        with self.assertRaisesRegex(CommandError, "run build --no-lean"):
            self.refresh()
        invalid = (
            {},
            {**valid, "entries": {}},
            {**valid, "nodes": {}},
            {**valid, "entries": {"alpha": {**valid["entries"]["alpha"],
                "formalization": {"complete": True, "total": 1, "unmapped_blocks": 0}}}},
            {**valid, "entries": {"alpha": {**valid["entries"]["alpha"],
                "formalization": {"complete": 2, "total": 1, "unmapped_blocks": 0}}}},
        )
        for record in invalid:
            with self.subTest(record=record):
                write_json(index, record)
                with self.assertRaisesRegex(CommandError, "entry formalization counts"):
                    self.refresh()
        self.assertEqual((self.corpus / "statistics.json").read_bytes(), published)

    def test_refresh_uses_configured_index_for_configured_corpus(self):
        self.published_snapshot()
        self.summaries["alpha"]["complete"] = 1
        self.save_records()
        selected = self.root / "selected-index.json"
        (self.corpus / "index.json").rename(selected)
        with override_settings(CORPUS_DIR=self.corpus, CORPUS_INDEX_PATH=selected):
            snapshot = prepare_statistics(self.corpus, self.root)
        self.assertEqual(snapshot["verified_entries"], 1)

    def test_new_author_appears_after_commit_but_bot_refresh_changes_nothing(self):
        self.commit(1)
        self.refresh()
        self.commit(2, "github-actions[bot]")
        self.commit(3, "Bob")
        self.refresh()
        path = self.corpus / "statistics.json"
        snapshot = read_json(path)
        self.assertEqual(snapshot["contributors"], 2)
        self.assertEqual([point["count"]
                         for point in snapshot["history"]["contributors"]], [1, 2])
        before, modified = path.read_bytes(), path.stat().st_mtime_ns
        self.commit(4, "github-actions[bot]")
        self.refresh()
        self.assertEqual(path.read_bytes(), before)
        self.assertEqual(path.stat().st_mtime_ns, modified)
        self.assertEqual([point["count"] for point in history_from_git(
            self.corpus, self.root)["contributors"]], [1, 2])

    def test_refresh_errors_preserve_the_published_snapshot(self):
        self.published_snapshot()
        path = self.corpus / "statistics.json"
        before = path.read_bytes()
        with patch("catalog.statistics.contributor_count",
                   side_effect=subprocess.CalledProcessError(1, "git")):
            with self.assertRaises(CommandError):
                self.refresh()
        self.assertEqual(path.read_bytes(), before)
        (self.corpus / "nodes/proof.json").write_text("Invalid JSON")
        with self.assertRaises(CommandError):
            self.refresh()
        self.assertEqual(path.read_bytes(), before)

    def test_refresh_validates_history_before_writing(self):
        self.published_snapshot()
        path = self.corpus / "statistics.json"
        snapshot = read_json(path)
        snapshot["history"]["nodes"][0]["verified"] = 2
        write_json(path, snapshot)
        before = path.read_bytes()
        with self.assertRaises(CommandError):
            self.refresh()
        self.assertEqual(path.read_bytes(), before)

    def test_refresh_keeps_manually_trimmed_history(self):
        self.published_snapshot()
        self.results["proof"]["verified"] = True
        self.save_records()
        previous = prepare_statistics(
            self.corpus, self.root)
        previous["history"]["nodes"].pop(0)
        write_json(self.corpus / "statistics.json", previous)
        with patch("catalog.statistics.history_from_git", side_effect=AssertionError("Keep edited history")):
            self.assertEqual(prepare_statistics(
                self.corpus, self.root), previous)

    def test_shallow_clone_preserves_recorded_history(self):
        previous = self.published_snapshot()
        self.commit(1)
        (self.root / ".git/shallow").write_text(self.git("rev-parse", "HEAD"))
        self.assertEqual(prepare_statistics(
            self.corpus, self.root), previous)

    def test_same_second_changes_and_backwards_clocks_keep_valid_history(self):
        snapshot = self.published_snapshot()
        at = "2026-02-01T12:00:00+00:00"
        snapshot.update(nodes=2, verified_nodes=2)
        append_counts(snapshot["history"], snapshot, at)
        snapshot.update(nodes=1, verified_nodes=1)
        append_counts(snapshot["history"], snapshot, at)
        validate_statistics(snapshot)
        snapshot.update(entries=2, areas=2)
        append_counts(snapshot["history"], snapshot,
                      "2026-01-15T12:00:00+00:00")
        self.assertEqual(snapshot["history"]["entries"][-1]["at"], at)
        self.assertEqual(snapshot["history"]["areas"][-1]["at"], at)
        validate_statistics(snapshot)

    def test_history_validation_rejects_invalid_points_and_inconsistent_totals(self):
        snapshot = self.published_snapshot()
        validate_statistics(snapshot)
        for point in ({"at": "bad", "count": 1, "verified": 0},
                      {"at": "2026-01-01T00:00:00", "count": 1, "verified": 0},
                      {"at": "2026-01-01T12:00:00+00:00",
                          "count": -1, "verified": 0},
                      {"at": "2026-01-01T12:00:00+00:00",
                          "count": True, "verified": 0},
                      {"at": "2026-01-01T12:00:00+00:00",
                          "count": 1, "verified": True},
                      {"at": "2026-01-01T12:00:00+00:00", "count": 1, "verified": -1}):
            with self.subTest(point=point):
                invalid = deepcopy(snapshot)
                invalid["history"]["entries"] = [point]
                with self.assertRaises(ValueError):
                    validate_statistics(invalid)
        invalid = deepcopy(snapshot)
        invalid["history"]["entries"].append(invalid["history"]["entries"][0])
        with self.assertRaisesRegex(ValueError, "changes only"):
            validate_statistics(invalid)
        invalid = deepcopy(snapshot)
        invalid["history"]["nodes"].insert(
            0, {"at": "2025-01-01T00:00:00+00:00", "count": 1, "verified": 2})
        with self.assertRaisesRegex(ValueError, "exceed the total"):
            validate_statistics(invalid)
        invalid = deepcopy(snapshot)
        invalid["history"]["nodes"][-1]["verified"] = 1
        with self.assertRaisesRegex(ValueError, "current verified count"):
            validate_statistics(invalid)
