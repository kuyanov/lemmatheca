"""Prepare entries, nodes, and navigation for the reader."""

from collections import Counter, defaultdict
from urllib.parse import quote

from django.conf import settings
from django.urls import reverse

from .entry_files import read_entry, read_entry_metadata
from .node_files import read_node, read_source, source_for_module
from .progress import block_progress, entry_progress
from .sources import parse_source


def load_node(identifier):
    node = read_node(identifier)
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


def area_list(parent_id, taxonomy, area_entries):
    counts = Counter()
    for area_id, identifiers in area_entries.items():
        for ancestor in ancestors(taxonomy[area_id], taxonomy):
            counts[ancestor["id"]] += len(identifiers)
    children = defaultdict(list)
    for area in taxonomy.values():
        children[area["parent"]].append(area)
    return [{**area_link(area, taxonomy), "children_count": len(children[area["id"]]),
             "entry_count": counts[area["id"]]} for area in children[parent_id]]


def load_entry_metadata(identifier):
    return {**read_entry_metadata(identifier),
            "url": reverse("catalog:entry", args=[identifier])}


def load_entry(identifier):
    """Parse one entry without loading its nodes or following its references."""
    entry = read_entry(identifier)
    blocks, anchors, counts, captioned = parse_source(entry.pop("source"))
    return {
        **entry,
        "url": reverse("catalog:entry", args=[identifier]),
        "blocks": blocks,
        "blocks_by_id": {block["id"]: block for block in blocks},
        "anchors": anchors,
        "captioned": captioned,
        "contents_summary": " · ".join(
            f"{count} {kind}{'s' if count != 1 else ''}" for kind, count in counts.items()),
        "based_on": [{**citation, "doi_url": "https://doi.org/" + quote(citation["doi"], safe="/")
                      if citation.get("doi") else None} for citation in entry.get("based_on", [])],
    }


def add_progress(entry):
    """Attach saved proof status from only the nodes used by this entry."""
    nodes = {identifier: load_node(identifier) for identifier in
             {identifier for block in entry["blocks"] for identifier in block["formal_ids"] or []}}
    for block in entry["blocks"]:
        block["formalization"] = block_progress(block["formal_ids"], nodes)
        block["formal_nodes"] = [nodes[identifier]
                                 for identifier in block["formal_ids"] or []]
    entry["formalization"] = entry_progress(entry["blocks"], nodes)
    return entry


def next_entry(entry, area_entries):
    """Read only the next entry's metadata, following its area's index."""
    siblings = area_entries.get(entry["primary_area"], [])
    try:
        position = siblings.index(entry["id"])
    except ValueError:
        return None
    if position + 1 < len(siblings):
        return load_entry_metadata(siblings[position + 1])
