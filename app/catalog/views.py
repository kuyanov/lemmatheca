from django.http import Http404
from django.shortcuts import render
from django.urls import reverse
from django.views.decorators.http import require_safe

from .content import ancestors, area_link, area_path, areas, children, example_entry


def entry_context():
    entry = example_entry()
    return {**entry, "url": reverse("catalog:entry", args=[entry["id"], entry["slug"]])}


@require_safe
def home(request):
    return render(request, "catalog/home.html", {
        "areas": [area_link(area) for area in children()],
        "example": entry_context(),
    })


@require_safe
def area(request, path):
    current = areas().get(path.split("/")[-1])
    if current is None or area_path(current) != path:
        raise Http404("This area is not in the library.")
    return render(request, "catalog/area.html", {
        "area": current,
        "breadcrumbs": [area_link(item) for item in ancestors(current)],
        "areas": [area_link(item) for item in children(current["id"])],
        "example": entry_context() if current["id"] == example_entry()["primary_area"] else None,
    })


@require_safe
def entry(request, entry_id, slug):
    example = entry_context()
    if entry_id != example["id"] or slug != example["slug"]:
        raise Http404("This statement is not in the library.")
    return render(request, "catalog/proofs/sumset_lower_bound.html", {
        "entry": example,
        "breadcrumbs": [area_link(item) for item in ancestors(areas()[example["primary_area"]])],
    })
