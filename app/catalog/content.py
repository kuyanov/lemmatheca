"""Prepare entries, nodes, and navigation for the reader."""

from collections import Counter, defaultdict
from urllib.parse import quote

from django.conf import settings
from django.urls import reverse

from .entry_files import read_entry, read_entry_metadata
from .index_reader import IndexUnavailable, get_index
from .node_files import read_node, read_source, source_for_module
from .node_results import with_node_result
from .progress import block_progress, entry_progress, format_progress
from .sources import parse_source


def optional_index():
    """Reader pages can display authored content before the first build."""
    try:
        return get_index()
    except IndexUnavailable:
        return {}


def load_node(identifier, index=None):
    index = optional_index() if index is None else index
    node = with_node_result(read_node(identifier), index)
    module = node.get("module")
    return {**node, "source": source_for_module(module) if module else None,
            "url": reverse("catalog:node", args=[identifier])}


def node_source(node):
    lines = read_source(node["module"], settings.REPOSITORY_DIR)
    line = node.get("declaration_line")
    if type(line) is not int or not 1 <= line <= len(lines):
        line = None
    return {
        "source_lines": [{"number": number, "text": value, "selected": number == line}
                         for number, value in enumerate(lines, 1)],
        "declaration_line": line,
    }


def ancestors(area, taxonomy):
    trail = []
    while area:
        trail.append(area)
        area = taxonomy.get(area["parent"])
    return list(reversed(trail))


def area_path(area, taxonomy):
    return "/".join(item["id"] for item in ancestors(area, taxonomy))


def area_link(area, taxonomy):
    return {**area, "url": reverse("catalog:area", args=[area_path(area, taxonomy)])}


def area_list(parent_id, taxonomy, reading_order):
    counts = Counter()
    for area_id, identifiers in reading_order.items():
        for ancestor in ancestors(taxonomy[area_id], taxonomy):
            counts[ancestor["id"]] += len(identifiers)
    children = defaultdict(list)
    for area in taxonomy.values():
        children[area["parent"]].append(area)
    return [{**area_link(area, taxonomy), "children_count": len(children[area["id"]]),
             "entry_count": counts[area["id"]]} for area in children[parent_id]]


def saved_entry_metrics(identifier, index=None):
    """Use published summaries when available, while keeping drafts readable."""
    index = optional_index() if index is None else index
    indexed = index.get("entries", {}).get(identifier)
    if indexed is None:
        return {}
    return {"formalization": format_progress(indexed["formalization"], len(indexed["blocks"])),
            "lean_line_count": indexed["lean_line_count"]}


def load_entry_metadata(identifier, index=None):
    return {**read_entry_metadata(identifier), **saved_entry_metrics(identifier, index),
            "url": reverse("catalog:entry", args=[identifier])}


def load_entry(identifier, index=None):
    """Parse one entry without loading its nodes or following its references."""
    entry = read_entry(identifier)
    blocks, counts, captioned = parse_source(entry.pop("source"))
    return {
        **entry,
        **saved_entry_metrics(identifier, index),
        "url": reverse("catalog:entry", args=[identifier]),
        "blocks": blocks,
        "blocks_by_id": {block["id"]: block for block in blocks},
        "captioned": captioned,
        "contents_summary": " · ".join(
            f"{count} {kind}{'s' if count != 1 else ''}" for kind, count in counts.items()),
        "based_on": [{**citation, "doi_url": "https://doi.org/" + quote(citation["doi"], safe="/")
                      if citation.get("doi") else None} for citation in entry.get("based_on", [])],
    }


def add_progress(entry, index=None):
    """Attach saved proof status from only the nodes used by this entry."""
    index = optional_index() if index is None else index
    nodes = {identifier: load_node(identifier, index) for identifier in
             {identifier for block in entry["blocks"] for identifier in block["formal_ids"] or []}}
    for block in entry["blocks"]:
        block["formalization"] = block_progress(block["formal_ids"], nodes)
        block["formal_nodes"] = [nodes[identifier]
                                 for identifier in block["formal_ids"] or []]
    entry["formalization"] = entry_progress(entry["blocks"], nodes)
    return entry


def next_entry(entry, reading_order, index=None):
    """Read only the next entry's metadata, following its area's index."""
    siblings = reading_order.get(entry["primary_area"], [])
    try:
        position = siblings.index(entry["id"])
    except ValueError:
        return None
    if position + 1 < len(siblings):
        return load_entry_metadata(siblings[position + 1], index)
