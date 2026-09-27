from urllib.parse import urlencode

from django.http import Http404, JsonResponse
from django.shortcuts import render
from django.views.decorators.http import require_safe

from .content import (ancestors, area_link, area_list, area_path, areas,
                      entries, load_nodes, next_entry, node_source)
from .sources import render_block


@require_safe
def home(request):
    catalog = entries()
    example = next(iter(catalog.values()), None)
    return render(request, "catalog/home.html", {
        "areas": area_list(None, catalog),
        "example": example,
        "example_area": areas()[example['primary_area']] if example else None,
    })


@require_safe
def area(request, path):
    current = areas().get(path.split("/")[-1])
    if current is None or area_path(current) != path:
        raise Http404("This area is not in the library.")
    catalog = entries()
    return render(request, "catalog/area.html", {
        "area": current,
        "breadcrumbs": [area_link(item) for item in ancestors(current)],
        "areas": area_list(current["id"], catalog),
        "entries": [item for item in catalog.values()
                    if item["primary_area"] == current["id"]],
    })


@require_safe
def entry(request, entry_id):
    catalog = entries()
    record = catalog.get(entry_id)
    if record is None:
        raise Http404("This entry is not in the library.")
    blocks = [
        {**block, "html": render_block(block, record,
                                       catalog, request.GET.get("answer"))}
        for block in record["blocks"]
    ]
    # The source is an entry ID, never a client-supplied URL. This also works in
    # a new tab or without JavaScript, unlike relying solely on history.back().
    source = catalog.get(request.GET.get("from"))
    return_block = source["blocks_by_id"].get(
        request.GET.get("at")) if source else None
    return_entry = source if source and (
        source["id"] != entry_id or return_block) else None
    entry_area = area_link(areas()[record["primary_area"]])
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
        "next_entry": next_entry(record, catalog),
        "return_entry": return_entry,
        "return_block": return_block,
        "return_url": return_url,
        "return_label": return_label,
        "breadcrumbs": [area_link(item) for item in ancestors(areas()[record["primary_area"]])],
    })


def get_node(nodes, identifier):
    if identifier not in nodes:
        raise Http404("This formal node is not in the library.")
    return nodes[identifier]


@require_safe
def node_page(request, node_id):
    nodes = load_nodes()
    node = get_node(nodes, node_id)
    context = {"node": node, "dependencies": [
        nodes[identifier] for identifier in node.get("dependencies", [])]}
    if node["source"]:
        context.update(node_source(node))
    return render(request, "catalog/node.html", context)


@require_safe
def node_list(request):
    return JsonResponse({"nodes": list(load_nodes().values())})


@require_safe
def node_detail(request, node_id):
    return JsonResponse(get_node(load_nodes(), node_id))
