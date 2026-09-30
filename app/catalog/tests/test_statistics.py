"""Contributor counts use canonical Git authors, without requiring Git at runtime."""

from pathlib import Path
import subprocess
from tempfile import TemporaryDirectory

from django.test import SimpleTestCase

from catalog.statistics import contributor_count


class ContributorTests(SimpleTestCase):
    def test_author_names_and_mailmap_avoid_counting_email_aliases_twice(self):
        with TemporaryDirectory() as directory:
            root = Path(directory)

            def git(*args):
                return subprocess.run(
                    ["git", "-c", "commit.gpgsign=false", "-c", "core.hooksPath=/dev/null", *args],
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
