"""Validate, prepare and publish the corpus's rebuildable data."""

import json
from pathlib import Path

from django.conf import settings

from .authoring_records import build_planning_index, build_source_index
from .corpus_index import CorpusIndex, configured_index_path, validate_index_destination
from .files import read_json, write_json
from .index_reader import IndexUnavailable, get_index
from .proofs import prepare_proof_results
from .validation import validate_corpus


def _authoring_indexes(corpus):
    builders = (("source-errors", build_source_index),
                ("reference-planning", build_planning_index))
    return {f"{directory}/index.json": builder(corpus)
            for directory, builder in builders if (corpus / directory).exists()}


def _check_saved(corpus, catalogs, index_path, index):
    stale = []
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


def _saved_node_results(corpus, destination):
    # An alternate output can start from the normal snapshot. An existing but
    # invalid alternate snapshot must never silently inherit different results.
    source = destination
    try:
        source.stat()
    except FileNotFoundError:
        source = (configured_index_path() if corpus == Path(settings.CORPUS_DIR).resolve()
                  else corpus / "index.json")
    try:
        return get_index(source)["nodes"], None
    except IndexUnavailable as error:
        if isinstance(error.__cause__, FileNotFoundError):
            return {}, source
        raise ValueError(
            f"{source}: cannot reuse saved proof results ({error.__cause__ or error}). "
            "Run build without --no-lean to repair the index.") from error


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
        corpus, source_root=source_root, allow_stale_catalogs=True)
    counts = {"entries": entries_count, "nodes": nodes_count, "areas": areas_count}
    if no_lean and check:
        return {"counts": counts, "verified": None, "index_path": destination,
                "lean_checked": False, "warnings": []}

    missing_index = None
    if no_lean:
        results, missing_index = _saved_node_results(corpus, destination)
    else:
        results = prepare_proof_results(corpus, formal)
    catalogs = _authoring_indexes(corpus)
    collector = CorpusIndex(corpus, formal, node_results=results)
    validate_corpus(corpus, source_root=source_root, collector=collector,
                    authoring_indexes=catalogs)
    document = collector.finish()
    warnings = []
    if missing_index is not None and any(node["binding"][1] for node in document["nodes"].values()):
        warnings.append(
            f"No saved corpus index was available at {missing_index}; bound nodes "
            "have no verification, signatures or source lines. "
            "Run build without --no-lean to check them.")
    if check:
        _check_saved(corpus, catalogs, destination, document)
    else:
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
            "verified": sum(node["verified"] for node in document["nodes"].values()),
            "index_path": destination, "lean_checked": not no_lean,
            "warnings": warnings}
