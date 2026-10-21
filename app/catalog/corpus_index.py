"""Derived relationships and entry metrics for validated corpus files.

The validator supplies core entry/node/navigation records, HTML trees and their exact bytes. This
collector never rereads them, renders templates or invokes Lean; it reads owned
Lean source files only to count their lines. Corpus files
remain authoritative; metadata available through a direct record read is not
copied into the index. Source/planning registries use independent catalogs.
Authored prose is read separately and never retained by
this collector. The output is safe to discard and regenerate.
"""

from collections import Counter, defaultdict
from hashlib import sha256
import json
from pathlib import Path
from urllib.parse import urlsplit

from .equations import LABEL
from .files import write_json
from .node_results import saved_result, validate_result
from .progress import progress_counts
from .sources import Element


SCHEMA_VERSION = 7


def default_index_path(repository):
    return Path(repository) / "corpus" / "index.json"


def configured_index_path():
    from django.conf import settings

    configured = getattr(settings, "CORPUS_INDEX_PATH", None)
    return Path(configured) if configured else default_index_path(settings.REPOSITORY_DIR)


class CorpusIndex:
    """Collect one validated snapshot without relying on file iteration order."""

    def __init__(self, corpus, formal=None, node_results=None):
        self.corpus = Path(corpus).resolve()
        self.formal = Path(formal) if formal is not None else self.corpus.parent / "formal"
        # Per-file digests are temporary inputs to the overall revision, not
        # part of the exported index.
        self._file_hashes = {}
        self.reading_positions = {}
        self.entries = {}
        self.blocks = {}
        self.nodes = {}
        self._node_results = node_results or {}
        self.anchors = {}
        self._references = defaultdict(list)

    def add_file(self, path, raw_bytes):
        relative = Path(path).absolute().relative_to(self.corpus).as_posix()
        # Statistics are refreshed independently after merges. Neither generated
        # snapshot contributes to the structural index's revision.
        if relative in {"index.json", "statistics.json"}:
            return
        self._file_hashes[relative] = sha256(raw_bytes).hexdigest()

    def add_reading_order(self, document):
        self.reading_positions = {
            entry_id: position
            for ids in document["areas"].values()
            for position, entry_id in enumerate(ids, 1)
        }

    def add_node(self, record):
        # Retain only the inputs needed for reverse lookups while collecting.
        # Authored descriptions stay in node files; proof results are separate.
        self.nodes[record["id"]] = (
            record.get("module"), record.get("declaration"),
            tuple(record.get("dependencies", [])),
        )

    def add_entry(self, record, root):
        entry_id = record["id"]
        block_ids = []
        numbers = Counter()
        for section in root.children:
            if not isinstance(section, Element):
                continue
            block_id, kind = section.attrs["id"], section.attrs["data-kind"]
            key = f"{entry_id}#{block_id}"
            numbers[kind] += 1
            block = {
                "kind": kind, "number": numbers[kind], "order": len(block_ids) + 1,
                "formal_ids": (section.attrs["data-formal"].split()
                               if "data-formal" in section.attrs else None),
            }
            link_index = 0

            def visit(node, in_answer=False):
                nonlocal link_index
                if not isinstance(node, Element):
                    return
                in_answer = in_answer or (
                    node.tag == "details"
                    and "question-answer" in node.attrs.get("class", "").split())
                anchor_ids = ([node.attrs["id"]]
                              if node is not section and "id" in node.attrs else [])
                if (node.tag in {"div", "p"}
                        and "math-display" in node.attrs.get("class", "").split()):
                    anchor_ids.extend(LABEL.findall(node.text()))
                for anchor in anchor_ids:
                    self.anchors[f"{entry_id}#{anchor}"] = key
                if node.tag == "a":
                    href = node.attrs["href"]
                    url = urlsplit(href)
                    if not (href.startswith("assets/") or url.scheme or url.netloc):
                        self._references[key].append({
                            "source": key, "target": f"{url.path or entry_id}#{url.fragment}",
                            "in_answer": in_answer, "link_index": link_index,
                        })
                    link_index += 1
                for child in node.children:
                    visit(child, in_answer)

            visit(section)
            self.blocks[key] = block
            block_ids.append(block_id)
        self.entries[entry_id] = {
            "blocks": block_ids, "reading_position": self.reading_positions[entry_id],
        }

    def _lean_line_count(self, entry_id):
        directory = self.formal / "Lemmatheca" / "".join(part.capitalize() for part in entry_id.split("-"))
        count = 0
        for path in directory.rglob("*.lean"):
            if path.is_file():
                with path.open(encoding="utf-8") as source:
                    count += sum(1 for _ in source)
        return count

    def finish(self):
        """Prepare deterministic relationships and entry metrics without publishing."""
        nodes = {}
        for node_id, (module, declaration, _) in sorted(self.nodes.items()):
            result = saved_result({"id": node_id, "module": module, "declaration": declaration},
                                  {"nodes": self._node_results})
            validate_result(result)
            nodes[node_id] = result
        entries = {
            entry_id: {**entry, "formalization": progress_counts(
                [self.blocks[f"{entry_id}#{block_id}"]["formal_ids"] for block_id in entry["blocks"]],
                nodes), "lean_line_count": self._lean_line_count(entry_id)}
            for entry_id, entry in sorted(self.entries.items())}
        revision_input = json.dumps(
            {"schema_version": SCHEMA_VERSION, "files": self._file_hashes,
             "entry_results": {key: {field: entry[field] for field in ("formalization", "lean_line_count")}
                               for key, entry in entries.items()}, "node_results": nodes},
            sort_keys=True, separators=(",", ":"), ensure_ascii=False,
        ).encode("utf-8")
        nodes_by_declaration, module_nodes = defaultdict(list), defaultdict(list)
        hint_dependents = defaultdict(list)
        for node_id, (module, declaration, dependencies) in sorted(self.nodes.items()):
            module = nodes[node_id].get("defining_module", module)
            if declaration:
                nodes_by_declaration[declaration].append(node_id)
            if module:
                module_nodes[module].append(node_id)
            for dependency in dependencies:
                hint_dependents[dependency].append(node_id)
        node_consumers, outgoing, incoming = defaultdict(list), defaultdict(list), defaultdict(list)
        references = []
        for entry_id, entry in entries.items():
            for block_id in entry["blocks"]:
                key = f"{entry_id}#{block_id}"
                block = self.blocks[key]
                for node_id in block["formal_ids"] or []:
                    node_consumers[node_id].append(key)
                for edge in self._references.get(key, []):
                    edge_id = len(references)
                    references.append(edge)
                    outgoing[key].append(edge_id)
                    incoming[edge["target"]].append(edge_id)
        return {
            "schema_version": SCHEMA_VERSION,
            "revision": sha256(revision_input).hexdigest(),
            "entries": entries, "blocks": dict(sorted(self.blocks.items())),
            "nodes": nodes,
            "anchors": dict(sorted(self.anchors.items())),
            "nodes_by_declaration": dict(sorted(nodes_by_declaration.items())),
            "module_nodes": dict(sorted(module_nodes.items())),
            "node_consumers": dict(sorted(node_consumers.items())),
            "hint_dependents": dict(sorted(hint_dependents.items())),
            "references": references, "outgoing": dict(sorted(outgoing.items())),
            "incoming": dict(sorted(incoming.items())),
        }


def validate_index_destination(corpus, destination):
    """Allow the reserved corpus cache or a destination outside the corpus."""
    corpus, destination = Path(corpus).resolve(), Path(destination).resolve()
    if destination.is_relative_to(corpus) and destination != corpus / "index.json":
        raise ValueError(
            "An index inside the corpus must use the reserved path corpus/index.json")
    return destination


def write_index(corpus, destination, *, source_root=None, node_results=None):
    """Validate once and atomically replace the derived structural index."""
    from .validation import validate_corpus

    corpus = Path(corpus).resolve()
    destination = validate_index_destination(corpus, destination)
    if node_results is None:
        from .index_reader import IndexUnavailable, get_index
        try:
            node_results = get_index(destination)["nodes"]
        except IndexUnavailable:
            node_results = {}
    collector = CorpusIndex(corpus, node_results=node_results)
    validate_corpus(corpus, source_root=source_root, collector=collector)
    document = collector.finish()
    destination.parent.mkdir(parents=True, exist_ok=True)
    write_json(destination, document)
    return document
