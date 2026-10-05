from functools import cache
from urllib.parse import urlencode

from django.http import Http404, JsonResponse
from django.shortcuts import render
from django.views.decorators.http import require_safe

from .axioms import AXIOM_LABELS
from .content import (add_progress, ancestors, area_link, area_list, area_path,
                      load_entry, load_entry_metadata, load_node, next_entry, node_source)
from .entry_files import read_area_entries, read_areas
from .node_files import node_ids
from .sources import render_block
from .statistics import read_statistics


@require_safe
def home(request):
    taxonomy, area_entries = read_areas(), read_area_entries()
    statistics = read_statistics()
    roots = sum(area["parent"] is None for area in taxonomy.values())
    return render(request, "catalog/home.html", {
        "areas": area_list(None, taxonomy, area_entries),
        "statistics": statistics,
        "area_count": len(taxonomy),
        "root_area_count": roots,
        "subarea_count": len(taxonomy) - roots,
    })


@require_safe
def area(request, path):
    taxonomy = read_areas()
    current = taxonomy.get(path.split("/")[-1])
    if current is None or area_path(current, taxonomy) != path:
        raise Http404("This area is not in the library.")
    area_entries = read_area_entries()
    return render(request, "catalog/area.html", {
        "area": current,
        "breadcrumbs": [area_link(item, taxonomy) for item in ancestors(current, taxonomy)],
        "areas": area_list(current["id"], taxonomy, area_entries),
        "entries": [load_entry_metadata(identifier)
                    for identifier in area_entries.get(current["id"], [])],
    })


@require_safe
def entry(request, entry_id):
    @cache
    def read_entry(identifier):
        try:
            return load_entry(identifier)
        except FileNotFoundError:
            return None

    record = read_entry(entry_id)
    if record is None:
        raise Http404("This entry is not in the library.")
    add_progress(record)
    blocks = [
        {**block, "html": render_block(block, record,
                                       read_entry, request.GET.get("answer"))}
        for block in record["blocks"]
    ]
    # The source is an entry ID, never a client-supplied URL. This also works in
    # a new tab or without JavaScript, unlike relying solely on history.back().
    source_id = request.GET.get("from")
    source = read_entry(source_id) if source_id else None
    return_block = source["blocks_by_id"].get(
        request.GET.get("at")) if source else None
    return_entry = source if source and (
        source["id"] != entry_id or return_block) else None
    taxonomy = read_areas()
    entry_area = area_link(taxonomy[record["primary_area"]], taxonomy)
    return_url = return_entry["url"] if return_entry else entry_area["url"]
    if return_block:
        if return_block["kind"] == "question":
            return_url += "?" + urlencode({"answer": return_block["id"]})
        return_url += f"#{return_block['id']}"
    return_label = f"Back to {return_entry['title']}" if return_entry else f"Back to {entry_area['title']}"
    if return_block and source['id'] == entry_id:
        return_label = f"Back to {return_block['label']}"
    return render(request, "catalog/entry.html", {
        "entry": {**record, "blocks": blocks},
        "next_entry": next_entry(record, read_area_entries()),
        "return_entry": return_entry,
        "return_block": return_block,
        "return_url": return_url,
        "return_label": return_label,
        "breadcrumbs": [area_link(item, taxonomy)
                        for item in ancestors(taxonomy[record["primary_area"]], taxonomy)],
    })


def get_node(identifier):
    try:
        return load_node(identifier)
    except FileNotFoundError as error:
        raise Http404("This formal node is not in the library.") from error


@require_safe
def node_page(request, node_id):
    node = get_node(node_id)
    context = {"node": node, "dependencies": [
        load_node(identifier) for identifier in node.get("dependencies", [])]}
    context["axiom_labels"] = [AXIOM_LABELS[axiom]
                               for axiom in node.get("axioms", [])]
    if node["source"]:
        context.update(node_source(node))
    return render(request, "catalog/node.html", context)


@require_safe
def node_list(request):
    return JsonResponse({"nodes": [load_node(identifier) for identifier in node_ids()]})


@require_safe
def node_detail(request, node_id):
    return JsonResponse(get_node(node_id))
