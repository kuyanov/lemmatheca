"""Load the file-backed corpus and its explicit editorial reading order."""

import json
from functools import lru_cache

from django.conf import settings
from django.urls import reverse

from .sources import ContentError, Element, IDENTIFIER, asset_path, parse_source, reference_target


def read_json(path):
    def unique_object(pairs):
        result = {}
        for key, value in pairs:
            if key in result:
                raise ContentError(f"{path}: duplicate JSON key {key}")
            result[key] = value
        return result
    return json.loads(path.read_text(), object_pairs_hook=unique_object)


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
    taxonomy = {area["id"] for area in read_json(
        corpus_dir / "taxonomy.json")["areas"]}
    for directory in sorted((corpus_dir / "entries").iterdir()):
        if not directory.is_dir():
            continue
        try:
            entry = read_json(directory / "entry.json")
            if entry["format_version"] != 1:
                raise ContentError("Unsupported entry format_version")
            if entry["id"] != directory.name or not IDENTIFIER.fullmatch(entry["id"]):
                raise ContentError("Entry ID must match its folder name")
            if not {entry["primary_area"], *entry.get("additional_areas", [])} <= taxonomy:
                raise ContentError("Unknown area")
            blocks, anchors, counts = parse_source(
                (directory / "entry.html").read_text(), entry["blocks"])
            catalog[entry["id"]] = {
                **entry, "directory": directory, "display_title": entry["title"],
                "blocks": blocks, "blocks_by_id": {block["id"]: block for block in blocks},
                "anchors": anchors,
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

    def validate_metadata(value):
        if isinstance(value, dict):
            if "entry_id" in value:
                target = catalog.get(value["entry_id"])
                if (not target or value.get("block_id") not in target["blocks_by_id"]
                        or value.get("revision") != target["revision"]):
                    raise ContentError(
                        f"Broken or stale metadata reference: {value}")
            if value.get("status") == "checked" and "declaration" in value:
                module = value.get("module", "")
                if not module.startswith("Lemmatheca.") or not all(
                        IDENTIFIER.fullmatch(part) for part in module.split(".")):
                    raise ContentError(f"Invalid Lean module: {module}")
                expected = f"formal/{module.replace('.', '/')}.lean"
                if value.get("source") != expected or not (repository_dir / expected).is_file():
                    raise ContentError(f"Missing Lean source: {expected}")
                report_path = (repository_dir /
                               value["verification_report"]).resolve()
                if not report_path.is_relative_to((repository_dir / "formal/checks").resolve()):
                    raise ContentError(
                        "Verification report must be inside formal/checks")
                report = read_json(report_path)
                if value["declaration"] not in {item["name"] for item in report["declarations"]}:
                    raise ContentError(
                        f"Declaration missing from report: {value['declaration']}")
            for child in value.values():
                validate_metadata(child)
        elif isinstance(value, list):
            for child in value:
                validate_metadata(child)

    for entry in ordered.values():
        try:
            for block in entry["blocks"]:
                validate_metadata(
                    {k: v for k, v in block.items() if k != "nodes"})
                for proof_id in block.get("proofs", {}):
                    if proof_id not in entry["anchors"]:
                        raise ContentError(
                            f"Proof has no source anchor: {proof_id}")
                referenced = set()
                for root in block["nodes"]:
                    if not isinstance(root, Element):
                        continue
                    for node in root.walk():
                        if node.tag == "a":
                            href = node.attrs.get("href", "")
                            if href.startswith("assets/"):
                                asset_path(entry["directory"], href)
                                continue
                            target = reference_target(
                                href, entry["id"], catalog)
                            if target:
                                referenced.add(
                                    (target[0]["id"], target[1]["id"]))
                        if node.tag == "img":
                            asset_path(entry["directory"],
                                       node.attrs.get("src", ""))
                recorded = {(ref["entry_id"], ref["block_id"])
                            for ref in block.get("references", [])}
                if referenced != recorded:
                    raise ContentError(
                        f"{block['id']}: HTML citations and metadata references differ")
        except (KeyError, TypeError, ValueError, OSError) as error:
            raise ContentError(f"{entry['directory']}: {error}") from error
    return ordered


@lru_cache(maxsize=1)
def _cached_catalog(corpus_dir, repository_dir, signature):
    return load_catalog(corpus_dir, repository_dir)


def entries():
    # Saving HTML, JSON, or an asset invalidates the cache without a server restart.
    signature = tuple((str(path), path.stat().st_mtime_ns, path.stat().st_size)
                      for path in sorted(settings.CORPUS_DIR.rglob("*")) if path.is_file())
    return _cached_catalog(settings.CORPUS_DIR, settings.REPOSITORY_DIR, signature)


def example_entry():
    return entries()["thm-sumset-lower-bound"]


def next_entry(entry):
    """Continue in the same primary area, following its catalog display order."""
    siblings = (item for item in entries().values()
                if item["primary_area"] == entry["primary_area"])
    for item in siblings:
        if item["id"] == entry["id"]:
            return next(siblings, None)
    return None


def area_link(area):
    path = area_path(area)
    entry_count = sum(
        area["id"] in {item["id"]
                       for item in ancestors(areas()[entry["primary_area"]])}
        for entry in entries().values()
    )
    return {**area, "url": reverse("catalog:area", args=[path]),
            "children_count": len(children(area["id"])), "entry_count": entry_count}
