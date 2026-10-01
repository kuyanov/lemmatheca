"""Small, build-time snapshot for the home page; requests never scan the corpus."""

from collections import Counter
from datetime import datetime, timezone
import json
import re
import subprocess

from django.conf import settings

from .files import read_json

COUNTS = ("entries", "verified_entries", "nodes",
          "verified_nodes", "areas", "contributors")
METRICS = ("entries", "nodes", "areas", "contributors")


def timestamp():
    return datetime.now(timezone.utc).isoformat()


def append_counts(history, counts, at):
    """Store changes only; rebuilding an unchanged corpus leaves its history intact."""
    # Commits and local clocks can go backwards; preserve order across all series.
    at = max([at, *(points[-1]["at"] for points in history.values() if points)],
             key=datetime.fromisoformat)
    for key in METRICS:
        value = counts.get(key)
        if value is None:
            continue
        values = {"count": value}
        if key in ("entries", "nodes"):
            values["verified"] = counts[f"verified_{key}"]
        points = history.setdefault(key, [])
        if not points or any(points[-1][field] != value for field, value in values.items()):
            points.append({"at": at, **values})


def git(repository, *args):
    return subprocess.run(["git", *args], cwd=repository, check=True,
                          capture_output=True, text=True, encoding="utf-8").stdout


def has_history(repository):
    return ((repository / ".git").exists()
            and git(repository, "rev-parse", "--is-shallow-repository").strip() == "false")


def read_statistics(corpus=None):
    try:
        return read_json((corpus or settings.CORPUS_DIR) / "statistics.json")
    except FileNotFoundError:
        return dict.fromkeys(COUNTS)


def contributor_count(repository, previous=None):
    # Source archives can serve and build using the last published count.
    if not has_history(repository):
        return previous
    authors = git(repository, "shortlog", "--summary", "HEAD")
    # shortlog groups by author name and respects .mailmap aliases. Neither
    # author names nor email addresses are published in the statistics file.
    return len(authors.splitlines())


def history_from_git(corpus, repository):
    """One-time import: replay changed metadata, not full trees or rendered entries.

    Mainline commits describe the published corpus. Legacy formal/nodes contributes
    node totals, but review flags never count as proof verification. Paired counts
    include only recorded proof flags / entry summaries in their verified totals.
    """
    history = {key: [] for key in METRICS}
    if not has_history(repository):
        return history
    prefix = corpus.relative_to(repository).as_posix()
    entry_path = re.compile(
        rf"{re.escape(prefix)}/entries/[^/]+/entry\.json\Z")
    node_path = re.compile(
        rf"(?:{re.escape(prefix)}/nodes|formal/nodes)/[^/]+\.json\Z")
    taxonomy = f"{prefix}/taxonomy.json"
    counts = Counter(entries=0, verified_entries=0,
                     nodes=0, verified_nodes=0, areas=0)
    records = {}
    previous = None
    commits = git(repository, "log", "--first-parent",
                  "--reverse", "--format=%H %cI", "HEAD")
    # One process streams blobs by object ID; retain only a kind and proof flag per path.
    with subprocess.Popen(["git", "cat-file", "--batch"], cwd=repository,
                          stdin=subprocess.PIPE, stdout=subprocess.PIPE) as blobs:
        for line in commits.splitlines():
            commit, date = line.split(" ", 1)
            at = datetime.fromisoformat(date).astimezone(
                timezone.utc).isoformat(timespec="seconds")
            revisions = [previous, commit] if previous else ["--root", commit]
            changes = git(repository, "diff-tree", "--no-commit-id", "--raw", "-z",
                          "--no-abbrev", "--no-renames", "-r", *revisions, "--",
                          f"{prefix}/entries", f"{prefix}/nodes", taxonomy, "formal/nodes").split("\0")
            for header, path in zip(changes[0::2], changes[1::2]):
                kind = "entries" if entry_path.fullmatch(
                    path) else "nodes" if node_path.fullmatch(path) else None
                if kind is None and path != taxonomy:
                    continue
                old = records.pop(path, None)
                if old:
                    category, verified = old
                    counts[category] -= 1
                    counts[f"verified_{category}"] -= verified is True
                object_id = header.split()[3]
                if set(object_id) == {"0"}:
                    if path == taxonomy:
                        counts["areas"] = 0
                    continue
                blobs.stdin.write(f"{object_id}\n".encode())
                blobs.stdin.flush()
                size = int(blobs.stdout.readline().split()[2])
                data = blobs.stdout.read(size)
                blobs.stdout.read(1)
                try:
                    record = json.loads(data)
                except (ValueError, UnicodeDecodeError):
                    record = {}
                if not isinstance(record, dict):
                    record = {}
                if path == taxonomy:
                    counts["areas"] = len(record["areas"]) if isinstance(
                        record.get("areas"), list) else None
                    continue
                verified = record.get("verified") if kind == "nodes" else None
                if kind == "entries" and isinstance(record.get("formalization"), dict):
                    verified = record["formalization"].get(
                        "status") == "complete"
                verified = verified if type(verified) is bool else None
                records[path] = kind, verified
                counts[kind] += 1
                counts[f"verified_{kind}"] += verified is True
            append_counts(history, counts, at)
            previous = commit
        blobs.stdin.close()

    # Include authors from merged branches as well; %aN respects the current mailmap.
    authors = set()
    author_log = git(repository, "log", "--format=%cI%x09%aN", "HEAD")
    dated_authors = [(datetime.fromisoformat(date).astimezone(timezone.utc).isoformat(timespec="seconds"), name)
                     for date, name in (line.split("\t", 1) for line in author_log.splitlines())]
    author_history = {"contributors": []}
    for at, name in sorted(dated_authors):
        authors.add(name)
        append_counts(author_history, {"contributors": len(authors)}, at)
    history["contributors"] = author_history["contributors"]
    return history


def prepare_statistics(corpus, repository, entries, nodes):
    previous = read_statistics(corpus)
    counts = {
        "entries": len(entries),
        "verified_entries": sum(entry["formalization"]["status"] == "complete"
                                for entry in entries.values()),
        "nodes": len(nodes),
        "verified_nodes": sum(node["verified"] for node in nodes.values()),
        "areas": len(read_json(corpus / "taxonomy.json")["areas"]),
        "contributors": contributor_count(repository, previous.get("contributors")),
    }
    history = previous.get("history")
    if history is None:
        history = history_from_git(corpus, repository)
    append_counts(history, counts, timestamp())
    return {**counts, "history": history}
