from urllib.parse import urlencode

from django.conf import settings
from django.http import Http404
from django.shortcuts import render
from django.urls import reverse
from django.views.decorators.http import require_safe

from .content import ancestors, area_link, area_path, areas, children, entries, example_entry, next_entry, read_json
from .sources import ContentError, render_block
from .lean import lean_source_path


def entry_context(entry):
    return {**entry, "url": reverse("catalog:entry", args=[entry["id"]])}


@require_safe
def lean_file(request, source):
    try:
        path = lean_source_path(source, settings.REPOSITORY_DIR)
        lean_source = path.read_text()
    except (ContentError, OSError, ValueError) as error:
        raise Http404('This Lean source file is not available.') from error

    context = {'source': source, 'filename': path.name, 'lean_source': lean_source,
               'return_url': reverse('catalog:home'), 'return_label': 'Back to repository'}
    # Context is optional. Status comes from a matching corpus binding, never
    # from a query parameter or from the mere presence of a source file.
    record = entries().get(request.GET.get('from')) if request.GET.get('from') else None
    block = record['blocks_by_id'].get(request.GET.get('at')) if record else None
    if block:
        formal = block['formalization']
        candidates = [(formal, formal['status'], False)] + [
            (item, 'partial', True) for item in formal['unformalized_dependencies']]
        for binding, status, pending in candidates:
            if binding['source'] != source or binding['declaration'] != request.GET.get('declaration'):
                continue
            entry_url = reverse('catalog:entry', args=[record['id']])
            if block['kind'] == 'question':
                entry_url += '?' + urlencode({'answer': block['id']})
            context.update(
                entry=entry_context(record), source_block=block, binding=binding,
                binding_status=status, pending=pending,
                return_url=entry_url + '#' + block['id'], return_label='Back to ' + block['title'])
            break
    if source.startswith('Mathlib/'):
        manifest = read_json(settings.REPOSITORY_DIR / 'formal/lake-manifest.json')
        commit = next(item['rev'] for item in manifest['packages'] if item['name'] == 'mathlib')
        context['upstream_url'] = f'https://github.com/leanprover-community/mathlib4/blob/{commit}/{source}'
    return render(request, 'catalog/lean_file.html', context)


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
def entry(request, entry_id):
    catalog = entries()
    record = catalog.get(entry_id)
    if record is None:
        raise Http404("This entry is not in the library.")
    current = entry_context(record)
    current["blocks"] = [
        {**block, "html": render_block(block, record,
                                       catalog, request.GET.get("answer"))}
        for block in record["blocks"]
    ]
    # The source is an entry ID, never a client-supplied URL. This also works in
    # a new tab or without JavaScript, unlike relying solely on history.back().
    source = catalog.get(request.GET.get("from"))
    return_entry = entry_context(
        source) if source and source["id"] != entry_id else None
    return_block = source["blocks_by_id"].get(
        request.GET.get("at")) if return_entry else None
    entry_area = area_link(areas()[record["primary_area"]])
    return_url = return_entry["url"] if return_entry else entry_area["url"]
    if return_block:
        if return_block["kind"] == "question":
            return_url += "?" + urlencode({"answer": return_block["id"]})
        return_url += f"#{return_block['id']}"
    return_label = f"Back to {return_entry['title']}" if return_entry else f"Back to {entry_area['title']}"
    following = next_entry(record)
    return render(request, "catalog/entry.html", {
        "entry": current,
        "next_entry": entry_context(following) if following else None,
        "return_entry": return_entry,
        "return_block": return_block,
        "return_url": return_url,
        "return_label": return_label,
        "breadcrumbs": [area_link(item) for item in ancestors(areas()[record["primary_area"]])],
    })
