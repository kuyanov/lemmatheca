"""Statistics history is built once from Git, then records only changed counts."""

from copy import deepcopy
import os
from pathlib import Path
import subprocess
from tempfile import TemporaryDirectory
from unittest.mock import patch

from django.test import SimpleTestCase

from catalog.files import write_json
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
                                ("Bob", "bob@example.test")]:
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
        self.entries = {"alpha": {"formalization": {"status": "partial"}}}
        self.nodes = {"proof": {"verified": False}}
        self.save_records()
        write_json(self.corpus / "taxonomy.json", {"areas": [{"id": "area"}]})
        self.git("init", "--quiet", "--initial-branch=main")

    def git(self, *args, **kwargs):
        return subprocess.run(["git", "-c", "commit.gpgsign=false", "-c", "core.hooksPath=/dev/null", *args],
                              cwd=self.root, check=True, capture_output=True, text=True, **kwargs).stdout

    def commit(self, day, name="Alice"):
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

    def test_git_replays_changes_deletions_and_renames_without_rendering(self):
        first = self.commit(1)
        self.nodes["proof"]["verified"] = True
        self.entries["alpha"]["formalization"]["status"] = "complete"
        self.save_records()
        second = self.commit(2)
        (self.corpus / "nodes/proof.json").rename(self.corpus / "nodes/renamed.json")
        self.commit(3)
        self.entries["beta"] = {"formalization": {"status": "partial"}}
        self.nodes = {"renamed": {"verified": True},
                      "pending": {"verified": False}}
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
        first = self.commit(1)
        legacy.unlink()
        self.save_records()
        self.commit(2)
        history = history_from_git(self.corpus, self.root)
        self.assertEqual(history["nodes"], [
                         {"at": first, "count": 1, "verified": 0}])
        self.assertEqual(history["entries"], history["nodes"])

    def test_merge_counts_corpus_once_and_includes_branch_authors(self):
        self.commit(1)
        self.git("checkout", "--quiet", "-b", "contribution")
        self.nodes["new"] = {"verified": False}
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

    def test_build_appends_only_changed_counts_and_preserves_history(self):
        self.commit(1)
        with patch("catalog.statistics.timestamp", return_value="2026-02-01T12:00:00+00:00"):
            first = prepare_statistics(
                self.corpus, self.root, self.entries, self.nodes)
        write_json(self.corpus / "statistics.json", first)
        validate_statistics(first)
        with patch("catalog.statistics.history_from_git", side_effect=AssertionError("Already imported")), \
                patch("catalog.statistics.timestamp", return_value="2026-02-02T12:00:00+00:00"):
            self.assertEqual(prepare_statistics(
                self.corpus, self.root, self.entries, self.nodes), first)
            self.nodes["proof"]["verified"] = True
            changed = prepare_statistics(
                self.corpus, self.root, self.entries, self.nodes)
        expected = deepcopy(first["history"])
        expected["nodes"].append(
            {"at": "2026-02-02T12:00:00+00:00", "count": 1, "verified": 1})
        self.assertEqual(changed["history"], expected)
        validate_statistics(changed)

    def test_build_keeps_manually_trimmed_history(self):
        self.commit(1)
        self.nodes["proof"]["verified"] = True
        self.save_records()
        self.commit(2)
        previous = prepare_statistics(
            self.corpus, self.root, self.entries, self.nodes)
        previous["history"]["nodes"].pop(0)
        write_json(self.corpus / "statistics.json", previous)
        with patch("catalog.statistics.history_from_git", side_effect=AssertionError("Keep edited history")):
            self.assertEqual(prepare_statistics(
                self.corpus, self.root, self.entries, self.nodes), previous)

    def test_shallow_clone_preserves_recorded_history(self):
        self.commit(1)
        previous = prepare_statistics(
            self.corpus, self.root, self.entries, self.nodes)
        write_json(self.corpus / "statistics.json", previous)
        (self.root / ".git/shallow").write_text(self.git("rev-parse", "HEAD"))
        self.assertEqual(prepare_statistics(
            self.corpus, self.root, self.entries, self.nodes), previous)

    def test_same_second_changes_and_backwards_clocks_keep_valid_history(self):
        self.commit(1)
        snapshot = prepare_statistics(
            self.corpus, self.root, self.entries, self.nodes)
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
        self.commit(1)
        snapshot = prepare_statistics(
            self.corpus, self.root, self.entries, self.nodes)
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
