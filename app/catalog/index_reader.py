"""Load a published index; reader requests never build or write one."""

from functools import lru_cache
import json
import os
from pathlib import Path
import re

from .corpus_index import SCHEMA_VERSION, configured_index_path
from .node_results import validate_result
from .sources import KINDS


class IndexUnavailable(Exception):
    pass


class _IndexChanged(Exception):
    pass


def _signature(stat):
    return stat.st_dev, stat.st_ino, stat.st_size, stat.st_mtime_ns


@lru_cache(maxsize=1)
def _read_index(path, signature):
    # Check the opened file, not only its pathname: publication uses replace().
    # Retry if replacement happened between the caller's stat and this open.
    with path.open(encoding="utf-8") as stream:
        if _signature(os.fstat(stream.fileno())) != signature:
            raise _IndexChanged
        document = json.load(stream)
        if _signature(os.fstat(stream.fileno())) != signature:
            raise _IndexChanged
    if not isinstance(document, dict) or document.get("schema_version") != SCHEMA_VERSION:
        raise ValueError("Unsupported corpus index schema")
    if not isinstance(document.get("revision"), str) or not re.fullmatch(r"[0-9a-f]{64}", document["revision"]):
        raise ValueError("Invalid corpus index revision")
    for field in ("entries", "nodes", "blocks", "anchors", "nodes_by_declaration",
                  "module_nodes", "node_consumers", "hint_dependents", "outgoing", "incoming"):
        if not isinstance(document.get(field), dict):
            raise ValueError(f"Invalid corpus index field: {field}")
    if not isinstance(document.get("references"), list):
        raise ValueError("Invalid corpus index references")
    for result in document["nodes"].values():
        validate_result(result)
    for entry in document["entries"].values():
        if (not isinstance(entry, dict) or not isinstance(entry.get("blocks"), list)
                or any(not isinstance(block, str) for block in entry["blocks"])
                or type(entry.get("reading_position")) is not int or entry["reading_position"] < 1
                or type(entry.get("lean_line_count")) is not int or entry["lean_line_count"] < 0):
            raise ValueError("Invalid corpus index entry")
        counts = entry.get("formalization")
        if (not isinstance(counts, dict) or set(counts) != {"complete", "total", "unmapped_blocks"}
                or any(type(value) is not int or value < 0 for value in counts.values())
                or counts["complete"] > counts["total"]
                or counts["unmapped_blocks"] > len(entry["blocks"])):
            raise ValueError("Invalid corpus index formalization counts")
    for block in document["blocks"].values():
        if (not isinstance(block, dict) or not isinstance(block.get("kind"), str)
                or block["kind"] not in KINDS
                or any(type(block.get(field)) is not int or block[field] < 1
                       for field in ("number", "order"))
                or "formal_ids" not in block
                or (block["formal_ids"] is not None
                    and (not isinstance(block["formal_ids"], list)
                         or any(not isinstance(identifier, str) for identifier in block["formal_ids"])))):
            raise ValueError("Invalid corpus index block")
    for edge in document["references"]:
        if (not isinstance(edge, dict)
                or any(not isinstance(edge.get(field), str) for field in ("source", "target"))
                or type(edge.get("in_answer")) is not bool
                or type(edge.get("link_index")) is not int or edge["link_index"] < 0):
            raise ValueError("Invalid corpus index reference")
    return document


def get_index(path=None):
    """Cache only index snapshots; live metadata is read separately per request."""
    path = Path(path if path is not None else configured_index_path()).resolve()
    try:
        for _ in range(3):
            signature = _signature(path.stat())
            try:
                return _read_index(path, signature)
            except _IndexChanged:
                continue
    except (OSError, ValueError) as error:
        raise IndexUnavailable(
            "Corpus index unavailable. Run python app/manage.py build to restore "
            "proof results. If the index is missing, --no-lean can instead build "
            "an unverified snapshot; an existing invalid index needs a full build."
        ) from error
    raise IndexUnavailable("Corpus index changed during loading; retry the request.")


def clear_index_cache():
    _read_index.cache_clear()
