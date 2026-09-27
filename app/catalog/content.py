"""Prepare entries, nodes, and navigation for the reader."""

from collections import Counter
from urllib.parse import quote

from django.conf import settings
from django.urls import reverse

from .entry_files import read_areas, read_entries, read_reading_order
from .node_files import read_nodes, read_source, source_for_module
from .progress import block_progress, entry_progress
from .sources import parse_source


def load_nodes(corpus=None):
    nodes = read_nodes(corpus or settings.CORPUS_DIR)
    for identifier, node in nodes.items():
        module = node.get("module")
        node.update(
            source=source_for_module(module) if module else None,
            url=reverse("catalog:node", args=[identifier]),
        )
    return nodes


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


def areas():
    return read_areas(settings.CORPUS_DIR)


def children(parent_id=None):
    return [area for area in areas().values() if area["parent"] == parent_id]


def ancestors(area):
    taxonomy = areas()
    trail = []
    while area:
        trail.append(area)
        area = taxonomy.get(area["parent"])
    return list(reversed(trail))


def area_path(area):
    return "/".join(item["id"] for item in ancestors(area))


def area_link(area):
    return {**area, "url": reverse("catalog:area", args=[area_path(area)])}


def area_list(parent_id, catalog):
    taxonomy = areas()
    counts = Counter(ancestor["id"] for entry in catalog.values()
                     for ancestor in ancestors(taxonomy[entry["primary_area"]]))
    return [{**area_link(area), "children_count": len(children(area["id"])),
             "entry_count": counts[area["id"]]} for area in children(parent_id)]


def entries(corpus=None):
    """Load entries in reading order, followed by unlisted entries sorted by ID."""
    corpus = corpus or settings.CORPUS_DIR
    catalog = read_entries(corpus)
    nodes = load_nodes(corpus)
    for entry in catalog.values():
        blocks, anchors, counts, captioned = parse_source(
            entry.pop("source"))
        for block in blocks:
            block["formalization"] = block_progress(block["formal_ids"], nodes)
            block["formal_nodes"] = [nodes[identifier]
                                     for identifier in block["formal_ids"] or []]
        entry.update(
            url=reverse("catalog:entry", args=[entry["id"]]),
            blocks=blocks,
            blocks_by_id={block["id"]: block for block in blocks},
            anchors=anchors,
            captioned=captioned,
            formalization=entry_progress(blocks, nodes),
            contents_summary=" · ".join(
                f"{count} {kind}{'s' if count != 1 else ''}" for kind, count in counts.items()),
            based_on=[{**citation, "doi_url": "https://doi.org/" + quote(citation["doi"], safe="/")
                       if citation.get("doi") else None} for citation in entry.get("based_on", [])],
        )
    order = read_reading_order(corpus)
    ordered = {}
    for group in order.values():
        for identifier in group:
            if identifier in catalog:
                ordered[identifier] = catalog[identifier]
    ordered.update((identifier, catalog[identifier])
                   for identifier in sorted(catalog.keys() - ordered.keys()))
    return ordered


def next_entry(entry, catalog):
    """Return the next entry in the same area, following the catalog's order."""
    siblings = (item for item in catalog.values()
                if item["primary_area"] == entry["primary_area"])
    for item in siblings:
        if item["id"] == entry["id"]:
            return next(siblings, None)
