"""Small, build-time snapshot for the home page; requests never scan the corpus."""

import subprocess

from django.conf import settings

from .files import read_json


def read_statistics(corpus=None):
    try:
        return read_json((corpus or settings.CORPUS_DIR) / "statistics.json")
    except FileNotFoundError:
        return dict.fromkeys(("entries", "verified_entries", "nodes",
                              "verified_nodes", "contributors"))


def contributor_count(repository, previous=None):
    # Source archives can serve and build using the last published count.
    if not (repository / ".git").exists():
        return previous
    shallow = subprocess.run(
        ["git", "rev-parse", "--is-shallow-repository"], cwd=repository,
        check=True, capture_output=True, text=True).stdout.strip()
    if shallow == "true":
        return previous
    authors = subprocess.run(
        ["git", "shortlog", "--summary", "HEAD"], cwd=repository,
        check=True, capture_output=True, text=True).stdout
    # shortlog groups by author name and respects .mailmap aliases. Neither
    # author names nor email addresses are published in the statistics file.
    return len(authors.splitlines())


def prepare_statistics(corpus, repository, entries, nodes):
    return {
        "entries": len(entries),
        "verified_entries": sum(entry["formalization"]["status"] == "complete"
                                for entry in entries.values()),
        "nodes": len(nodes),
        "verified_nodes": sum(node["verified"] for node in nodes.values()),
        "contributors": contributor_count(
            repository, read_statistics(corpus).get("contributors")),
    }
