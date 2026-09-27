"""Load the file-backed corpus and its explicit editorial reading order."""

from functools import lru_cache
from collections import Counter
from urllib.parse import quote

from django.conf import settings
from django.urls import reverse

from .sources import ContentError, Element, IDENTIFIER, asset_path, parse_source, reference_target
from .metadata import validate_entry_metadata
from .files import file_signature, read_json
from .reviews import entry_review_hash
from formalization.nodes import load_nodes, block_progress, entry_progress, formal_signature


def areas():
    source = settings.CORPUS_DIR / "taxonomy.json"
    return {area["id"]: area for area in read_json(source)["areas"]}


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


def load_catalog(corpus_dir, repository_dir):
    """Validate all sources before making any entry available to the reader."""
    catalog = {}
    formal_nodes = load_nodes(repository_dir)
    taxonomy = {area["id"] for area in read_json(
        corpus_dir / "taxonomy.json")["areas"]}
    for directory in sorted((corpus_dir / "entries").iterdir()):
        if not directory.is_dir():
            continue
        try:
            entry = read_json(directory / "entry.json")
            validate_entry_metadata(entry)
            if entry["id"] != directory.name or not IDENTIFIER.fullmatch(entry["id"]):
                raise ContentError("Entry ID must match its folder name")
            if not {entry["primary_area"], *entry.get("additional_areas", [])} <= taxonomy:
                raise ContentError("Unknown area")
            source = (directory / "entry.html").read_bytes()
            blocks, anchors, counts, captioned = parse_source(source.decode())
            for block in blocks:
                block['formalization'] = block_progress(
                    block['formal_ids'], formal_nodes)
                block['formal_nodes'] = [
                    formal_nodes[node_id]
                    for node_id in block['formal_ids'] or []]
            descriptions = {node['id']: node['description']
                            for block in blocks for node in block['formal_nodes']}
            target_hash = entry_review_hash(entry, source, directory, descriptions)
            review_current = entry['review'] is not None and entry['review']['sha256'] == target_hash
            catalog[entry["id"]] = {
                **entry, "directory": directory,
                "status": "final" if review_current else "draft",
                "review_current": review_current, "target_sha256": target_hash,
                "url": reverse("catalog:entry", args=[entry["id"]]),
                "blocks": blocks, "blocks_by_id": {block["id"]: block for block in blocks},
                "anchors": anchors, "captioned": captioned,
                "formalization": entry_progress(blocks, formal_nodes),
                "based_on": [
                    {**citation, 'doi_url': 'https://doi.org/' + quote(citation['doi'], safe='/')
                     if citation.get('doi') else None}
                    for citation in entry['based_on']],
                "contents_summary": " · ".join(
                    f"{count} {kind}{'s' if count != 1 else ''}" for kind, count in counts.items()),
            }
        except (KeyError, TypeError, ValueError, OSError) as error:
            raise ContentError(f"{directory}: {error}") from error

    order = read_json(corpus_dir / "reading-order.json")
    if order["format_version"] != 1:
        raise ContentError("Unsupported reading-order format_version")
    ordered = {}
    for area_id, entry_ids in order["areas"].items():
        if area_id not in taxonomy:
            raise ContentError(f"Unknown reading-order area: {area_id}")
        for entry_id in entry_ids:
            if entry_id in ordered or entry_id not in catalog:
                raise ContentError(
                    f"Duplicate or unknown reading-order entry: {entry_id}")
            if catalog[entry_id]["primary_area"] != area_id:
                raise ContentError(
                    f"{entry_id}: reading order must use its primary area")
            ordered[entry_id] = catalog[entry_id]
    if set(ordered) != set(catalog):
        raise ContentError("Every entry must appear in reading-order.json")

    for entry in ordered.values():
        try:
            for block in entry["blocks"]:
                for root in block["nodes"]:
                    if not isinstance(root, Element):
                        continue
                    for node in root.walk():
                        if node.tag == "a":
                            href = node.attrs.get("href", "")
                            if href.startswith("assets/"):
                                asset_path(entry["directory"], href)
                                continue
                            reference_target(href, entry["id"], catalog)
                        if node.tag == "img":
                            asset_path(entry["directory"],
                                       node.attrs.get("src", ""))
        except (KeyError, TypeError, ValueError, OSError) as error:
            raise ContentError(f"{entry['directory']}: {error}") from error
    return ordered


@lru_cache(maxsize=1)
def _cached_catalog(corpus_dir, repository_dir, signature):
    return load_catalog(corpus_dir, repository_dir)


def entries():
    # Saving HTML, JSON, or an asset invalidates the cache without a server restart.
    # Backups and the full taxonomy are reference material, not live corpus inputs.
    paths = [settings.CORPUS_DIR /
             name for name in ('taxonomy.json', 'reading-order.json')]
    paths.extend(path for path in (settings.CORPUS_DIR /
                 'entries').rglob('*') if path.is_file())
    signature = tuple(file_signature(path) for path in sorted(paths))
    signature += formal_signature(settings.REPOSITORY_DIR)
    return _cached_catalog(settings.CORPUS_DIR, settings.REPOSITORY_DIR, signature)


def next_entry(entry, catalog):
    """Continue in the same primary area, following its catalog display order."""
    siblings = (item for item in catalog.values()
                if item["primary_area"] == entry["primary_area"])
    for item in siblings:
        if item["id"] == entry["id"]:
            return next(siblings, None)
    return None


def area_link(area):
    return {**area, "url": reverse("catalog:area", args=[area_path(area)])}


def area_list(parent_id, catalog):
    """Add listing counts once, without loading the corpus for navigation links."""
    taxonomy = areas()
    counts = Counter(ancestor['id'] for entry in catalog.values()
                     for ancestor in ancestors(taxonomy[entry['primary_area']]))
    return [{**area_link(area), 'children_count': len(children(area['id'])),
             'entry_count': counts[area['id']]} for area in children(parent_id)]
