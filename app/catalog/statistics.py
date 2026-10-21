"""Home-page snapshot updated after merges; requests never scan the corpus."""

from collections import Counter
from datetime import datetime, timezone
import json
from pathlib import Path
import re
import subprocess

from django.conf import settings

from .corpus_index import configured_index_path
from .files import read_json
from .index_reader import get_index, IndexUnavailable
from .node_results import saved_result

COUNTS = ("entries", "verified_entries", "nodes",
          "verified_nodes", "areas", "contributors")
METRICS = ("entries", "nodes", "areas", "contributors")


def timestamp():
    return datetime.now(timezone.utc).isoformat()


def append_counts(history, counts, at):
    """Store changes only; refreshing unchanged counts leaves history intact."""
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
    # Source archives can serve and refresh using the last published count.
    if not has_history(repository):
        return previous
    authors = git(repository, "shortlog", "--summary", "HEAD")
    # shortlog groups names and respects .mailmap. Exclude automation, including
    # the statistics workflow itself. No author identities are published.
    return sum(not line.rsplit("\t", 1)[-1].endswith("[bot]")
               for line in authors.splitlines())


def _complete(summary):
    """Only a nonempty, fully mapped and verified node set is complete."""
    return (isinstance(summary, dict)
            and all(type(summary.get(key)) is int and summary[key] >= 0
                    for key in ("complete", "total", "unmapped_blocks"))
            and 0 < summary["total"] == summary["complete"]
            and summary["unmapped_blocks"] == 0)


def _saved_index(corpus, entry_ids, node_ids):
    """Read the published build snapshot without Lean or entry HTML parsing."""
    path = (configured_index_path() if corpus.resolve() == Path(settings.CORPUS_DIR).resolve()
            else corpus / "index.json")
    try:
        index = get_index(path)
        if set(index["entries"]) != set(entry_ids):
            raise ValueError("entry records do not match the corpus")
        if set(index["nodes"]) != set(node_ids):
            raise ValueError("node records do not match the corpus")
    except (IndexUnavailable, ValueError) as error:
        raise ValueError(
            f"{path}: a built corpus index with entry formalization counts and node results is required; "
            "run build --no-lean before updating statistics.") from error
    return index


def history_from_git(corpus, repository):
    """One-time import: replay changed metadata, not full trees or rendered entries.

    Mainline commits describe the published corpus. Legacy formal/nodes contributes
    node totals, but review flags never count as proof verification. Paired counts
    include only recorded proof flags / entry summaries in their verified totals.
    Once results move to the index, require the cached binding to match its node.
    """
    history = {key: [] for key in METRICS}
    if not has_history(repository):
        return history
    prefix = corpus.relative_to(repository).as_posix()
    entry_path = re.compile(
        rf"{re.escape(prefix)}/entries/[^/]+/entry\.json\Z")
    node_path = re.compile(
        rf"(?:{re.escape(prefix)}/nodes|formal/nodes)/[^/]+\.json\Z")
    taxonomy, index_path = f"{prefix}/taxonomy.json", f"{prefix}/index.json"
    counts = Counter(entries=0, verified_entries=0,
                     nodes=0, verified_nodes=0, areas=0)
    records = {}
    indexed_verification = {}
    indexed_nodes = None
    previous = None
    commits = git(repository, "log", "--first-parent",
                  "--reverse", "--format=%H %cI", "HEAD")
    # Stream blobs by object ID; retain only kinds, proof flags and binding pairs,
    # never historical descriptions or declaration signatures.
    with subprocess.Popen(["git", "cat-file", "--batch"], cwd=repository,
                          stdin=subprocess.PIPE, stdout=subprocess.PIPE) as blobs:
        for line in commits.splitlines():
            commit, date = line.split(" ", 1)
            at = datetime.fromisoformat(date).astimezone(
                timezone.utc).isoformat(timespec="seconds")
            revisions = [previous, commit] if previous else ["--root", commit]
            changes = git(repository, "diff-tree", "--no-commit-id", "--raw", "-z",
                          "--no-abbrev", "--no-renames", "-r", *revisions, "--",
                          f"{prefix}/entries", f"{prefix}/nodes", taxonomy, index_path,
                          "formal/nodes").split("\0")
            for header, path in zip(changes[0::2], changes[1::2]):
                kind = "entries" if entry_path.fullmatch(
                    path) else "nodes" if node_path.fullmatch(path) else None
                if kind is None and path not in (taxonomy, index_path):
                    continue
                old = records.pop(path, None)
                if old:
                    category, _, _ = old
                    counts[category] -= 1
                object_id = header.split()[3]
                if set(object_id) == {"0"}:
                    if path == taxonomy:
                        counts["areas"] = 0
                    elif path == index_path:
                        indexed_verification = {}
                        indexed_nodes = {} if indexed_nodes is not None else None
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
                if path == index_path:
                    # Older structural indexes have no entry summaries. Keep the
                    # legacy entry flags until generated counts become available.
                    entries = record.get("entries", {})
                    indexed_verification = {
                        identifier: _complete(entry["formalization"])
                        for identifier, entry in entries.items()
                        if isinstance(entry, dict) and "formalization" in entry
                    } if isinstance(entries, dict) else {}
                    # Absence in an older index preserves legacy node flags;
                    # absence in the new format means no saved verification.
                    indexed_nodes = None
                    if type(record.get("schema_version")) is int and record["schema_version"] >= 7:
                        nodes = record.get("nodes", {})
                        indexed_nodes = {
                            identifier: {"binding": node.get("binding"),
                                         "verified": node.get("verified") is True}
                            for identifier, node in nodes.items() if isinstance(node, dict)
                        } if isinstance(nodes, dict) else {}
                    continue
                verified = record.get("verified") if kind == "nodes" else None
                if kind == "entries" and isinstance(record.get("formalization"), dict):
                    verified = record["formalization"].get(
                        "status") == "complete"
                verified = verified if type(verified) is bool else None
                binding = (record.get("module"), record.get("declaration")) if kind == "nodes" else None
                records[path] = kind, verified, binding
                counts[kind] += 1
            # Apply the whole commit before recording a point: moving summaries
            # from entry files into the index must not introduce a false dip.
            counts["verified_entries"] = sum(
                indexed_verification.get(Path(path).parent.name, verified) is True
                for path, (kind, verified, _) in records.items() if kind == "entries")
            counts["verified_nodes"] = sum(
                (verified is True if indexed_nodes is None else saved_result(
                    {"id": Path(path).stem, "module": binding[0], "declaration": binding[1]},
                    {"nodes": indexed_nodes})["verified"])
                for path, (kind, verified, binding) in records.items() if kind == "nodes")
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
        if not name.endswith("[bot]"):
            authors.add(name)
        append_counts(author_history, {"contributors": len(authors)}, at)
    history["contributors"] = author_history["contributors"]
    return history


def prepare_statistics(corpus, repository):
    previous = read_statistics(corpus)
    counts = {
        "entries": 0, "verified_entries": 0, "nodes": 0, "verified_nodes": 0,
        "areas": len(read_json(corpus / "taxonomy.json")["areas"]),
        "contributors": contributor_count(repository, previous.get("contributors")),
    }
    # Read one JSON record at a time; neither HTML nor Lean sources are needed.
    identifiers = []
    for path in (corpus / "entries").glob("*/entry.json"):
        read_json(path)
        identifiers.append(path.parent.name)
        counts["entries"] += 1
    node_paths = list((corpus / "nodes").glob("*.json"))
    index = _saved_index(corpus, identifiers, (path.stem for path in node_paths))
    counts["verified_entries"] = sum(_complete(entry["formalization"])
                                     for entry in index["entries"].values())
    for path in node_paths:
        node = read_json(path)
        node.setdefault("id", path.stem)
        counts["nodes"] += 1
        counts["verified_nodes"] += saved_result(node, index)["verified"]
    history = previous.get("history")
    if history is None:
        history = history_from_git(corpus, repository)
    append_counts(history, counts, timestamp())
    return {**counts, "history": history}
