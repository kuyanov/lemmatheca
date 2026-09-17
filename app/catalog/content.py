"""Read the versioned seed taxonomy; keep public browsing independent of a DB."""

import json
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
def example_entry():
    source = settings.REPOSITORY_DIR / "examples" / "sumsets" / "lower-bound.json"
    entry = json.loads(source.read_text())
    return {**entry, "display_title": "A lower bound for sumsets", "summary":
            "A short proof that a sumset contains a translated copy of each summand."}


def area_link(area):
    path = area_path(area)
    entry_area = areas()[example_entry()["primary_area"]]
    has_example = area["id"] in {item["id"] for item in ancestors(entry_area)}
    return {**area, "url": reverse("catalog:area", args=[path]),
            "children_count": len(children(area["id"])), "has_example": has_example}
