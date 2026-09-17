"""Read the versioned seed taxonomy; keep public browsing independent of a DB."""

import json
from collections import Counter
from functools import lru_cache

from django.conf import settings
from django.urls import reverse


@lru_cache(maxsize=1)
def areas():
    source = settings.REPOSITORY_DIR / "examples" / "taxonomy.json"
    return {area["id"]: area for area in json.loads(source.read_text())["areas"]}


def children(parent_id=None):
    return [area for area in areas().values() if area["parent"] == parent_id]


def ancestors(area):
    trail = []
    while area:
        trail.append(area)
        area = areas().get(area["parent"])
    return list(reversed(trail))


def area_path(area):
    return "/".join(item["id"] for item in ancestors(area))


@lru_cache(maxsize=1)
def entries():
    """Articles contain independently addressable mathematical blocks.

    Numbers are presentation only: references use stable article and block IDs.
    Templates and metadata are trusted, repository-owned content.
    """
    source = settings.REPOSITORY_DIR / "examples" / "sumsets" / "entries.json"
    result = {}
    for entry in json.loads(source.read_text())["entries"]:
        counts = Counter()
        blocks = []
        for item in entry["blocks"]:
            counts[item["kind"]] += 1
            block = {**item, "label": f"{item['kind'].capitalize()} {counts[item['kind']]}"}
            if item.get("record"):
                record = json.loads((source.parent / item["record"]).read_text())
                block["record_id"] = record["id"]
                block["formalization"] = record["formalization"]
            blocks.append(block)
        result[entry["id"]] = {
            **entry, "display_title": entry["title"], "blocks": blocks,
            "blocks_by_id": {block["id"]: block for block in blocks},
            "contents_summary": " · ".join(
                f"{count} {kind}{'s' if count != 1 else ''}" for kind, count in counts.items()
            ),
        }
    return result


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
        area["id"] in {item["id"] for item in ancestors(areas()[entry["primary_area"]])}
        for entry in entries().values()
    )
    return {**area, "url": reverse("catalog:area", args=[path]),
            "children_count": len(children(area["id"])), "entry_count": entry_count}
