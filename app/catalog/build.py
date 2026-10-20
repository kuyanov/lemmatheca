"""Validate, prepare and publish the corpus's rebuildable data."""

import json
from pathlib import Path

from .authoring_records import build_planning_index, build_source_index
from .corpus_index import CorpusIndex, validate_index_destination
from .entry_files import entry_ids, read_entry, save_entries
from .files import read_json, write_json
from .node_files import read_nodes, save_results
from .progress import entry_progress
from .proofs import prepare_proof_results
from .sources import parse_source
from .validation import validate_corpus


def _entry_results(corpus, nodes):
    entries = {}
    for identifier in entry_ids(corpus):
        entry = read_entry(identifier, corpus)
        blocks, *_ = parse_source(entry.pop("source"), validate=True)
        entry.pop("directory")
        for block in blocks:
            for node_id in block["formal_ids"] or []:
                if node_id not in nodes:
                    raise ValueError(f"{identifier}: unknown formal node: {node_id}")
        entry["formalization"] = entry_progress(blocks, nodes)
        entries[identifier] = entry
    return entries


def _authoring_indexes(corpus):
    builders = (("source-errors", build_source_index),
                ("reference-planning", build_planning_index))
    return {f"{directory}/index.json": builder(corpus)
            for directory, builder in builders if (corpus / directory).exists()}


def _check_saved(corpus, nodes, entries, catalogs, index_path, index):
    stale = []
    for identifier, node in nodes.items():
        path = corpus / "nodes" / f"{identifier}.json"
        saved = read_json(path)
        if any(saved.get(field) != node.get(field) for field in
               ("verified", "signature", "declaration_line", "module")):
            stale.append(str(path.relative_to(corpus)))
    for identifier, entry in entries.items():
        path = corpus / "entries" / identifier / "entry.json"
        if read_json(path).get("formalization") != entry["formalization"]:
            stale.append(str(path.relative_to(corpus)))
    generated = [(corpus / relative, catalog) for relative, catalog in catalogs.items()]
    generated.append((index_path, index))
    for path, expected in generated:
        try:
            saved = read_json(path)
        except (FileNotFoundError, ValueError):
            saved = None
        # Ignore formatting without equating booleans, integers and floats.
        if json.dumps(saved, sort_keys=True) != json.dumps(expected, sort_keys=True):
            stale.append(str(path.relative_to(corpus)) if path.is_relative_to(corpus)
                         else str(path))
    if stale:
        preview = ", ".join(stale[:5])
        remainder = f" (and {len(stale) - 5} more)" if len(stale) > 5 else ""
        raise ValueError(f"Generated corpus data is stale: {preview}{remainder}. Run build.")


def _changed(corpus, records, path_for):
    return {identifier: record for identifier, record in records.items()
            if read_json(corpus / path_for(identifier)) != record}


def build_corpus(corpus, formal, index_path, *, no_lean=False, check=False,
                 check_sources=False):
    """A check never publishes; no-Lean builds retain last-known verification.

    Authored inputs are checked before Lean. Every proposed result is validated
    before any output is replaced. Each replacement is atomic, but publication
    of the complete set of files is not a single filesystem transaction.
    """
    corpus, formal = Path(corpus).resolve(), Path(formal)
    destination = validate_index_destination(corpus, index_path)
    source_root = formal.parent if check_sources else None
    entries_count, nodes_count, areas_count = validate_corpus(
        corpus, source_root=source_root, allow_stale_catalogs=True,
        allow_stale_results=True)
    counts = {"entries": entries_count, "nodes": nodes_count, "areas": areas_count}
    if no_lean and check:
        return {"counts": counts, "verified": None, "index_path": destination,
                "lean_checked": False}

    nodes = read_nodes(corpus) if no_lean else prepare_proof_results(corpus, formal)
    if no_lean:
        for node in nodes.values():
            if not node.get("declaration"):
                node["verified"] = False
                node.pop("signature", None)
                node.pop("declaration_line", None)
    entries = _entry_results(corpus, nodes)
    catalogs = _authoring_indexes(corpus)
    collector = CorpusIndex(corpus)
    validate_corpus(corpus, source_root=source_root, collector=collector,
                    nodes=nodes, entries=entries, authoring_indexes=catalogs)
    document = collector.finish()
    if check:
        _check_saved(corpus, nodes, entries, catalogs, destination, document)
    else:
        save_results(corpus, _changed(corpus, nodes, lambda key: f"nodes/{key}.json"))
        save_entries(corpus, _changed(corpus, entries, lambda key: f"entries/{key}/entry.json"))
        for relative, catalog in catalogs.items():
            path = corpus / relative
            try:
                current = read_json(path)
            except (FileNotFoundError, ValueError):
                current = None
            if current != catalog:
                write_json(path, catalog)
        destination.parent.mkdir(parents=True, exist_ok=True)
        write_json(destination, document)
    return {"counts": counts,
            "verified": sum(node.get("verified", False) for node in nodes.values()),
            "index_path": destination, "lean_checked": not no_lean}
