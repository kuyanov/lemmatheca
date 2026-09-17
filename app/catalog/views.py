from urllib.parse import urlencode

from django.http import Http404
from django.shortcuts import render
from django.urls import reverse
from django.views.decorators.http import require_safe

from .content import ancestors, area_link, area_path, areas, children, entries, example_entry


def entry_context(entry):
    return {**entry, "url": reverse("catalog:entry", args=[entry["id"], entry["slug"]])}


@require_safe
def home(request):
    return render(request, "catalog/home.html", {
        "areas": [area_link(area) for area in children()],
        "example": entry_context(example_entry()),
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
        "entries": [entry_context(item) for item in entries().values()
                    if item["primary_area"] == current["id"]],
    })


@require_safe
def entry(request, entry_id, slug):
    record = entries().get(entry_id)
    if record is None or slug != record["slug"]:
        raise Http404("This entry is not in the library.")
    current = entry_context(record)
    # The source is an entry ID, never a client-supplied URL. This also works in
    # a new tab or without JavaScript, unlike relying solely on history.back().
    source = entries().get(request.GET.get("from"))
    return_entry = entry_context(source) if source and source["id"] != entry_id else None
    return_block = source["blocks_by_id"].get(request.GET.get("at")) if return_entry else None
    entry_area = area_link(areas()[record["primary_area"]])
    return_url = return_entry["url"] if return_entry else entry_area["url"]
    if return_block:
        if return_block["kind"] == "question":
            return_url += "?" + urlencode({"answer": return_block["id"]})
        return_url += f"#{return_block['id']}"
    return_label = f"Back to {return_entry['title']}" if return_entry else f"Back to {entry_area['title']}"
    return render(request, "catalog/entry.html", {
        "entry": current,
        "return_entry": return_entry,
        "return_block": return_block,
        "expanded_answer": request.GET.get("answer"),
        "return_url": return_url,
        "return_label": return_label,
        "breadcrumbs": [area_link(item) for item in ancestors(areas()[record["primary_area"]])],
    })
