"""Read-only node API and node pages, separate from human entry metadata."""

from urllib.parse import urlencode

from django.conf import settings
from django.http import Http404, JsonResponse
from django.shortcuts import render
from django.urls import reverse
from django.views.decorators.http import require_safe

from .lean import source_context
from .nodes import load_nodes


@require_safe
def node_list(request):
    return JsonResponse({'nodes': list(load_nodes(settings.REPOSITORY_DIR).values())})


def get_node(node_id):
    node = load_nodes(settings.REPOSITORY_DIR).get(node_id)
    if node is None:
        raise Http404('This formal node is not in the library.')
    return node


@require_safe
def node_detail(request, node_id):
    return JsonResponse(get_node(node_id))


@require_safe
def node_page(request, node_id):
    node = get_node(node_id)
    nodes = load_nodes(settings.REPOSITORY_DIR)
    context = {'node': node, 'dependencies': [nodes[item] for item in node['dependencies']],
               'return_url': reverse('catalog:home'), 'return_label': 'Back to library'}
    if node['source']:
        context.update(source_context(
            node['source'], settings.REPOSITORY_DIR, node['declaration']))
    # Only a block actually linked to this node can supply return context.
    if request.GET.get('from'):
        from catalog.content import entries
        entry = entries().get(request.GET.get('from'))
        block = entry['blocks_by_id'].get(
            request.GET.get('at')) if entry else None
        if block and node_id in (block['formal_ids'] or []):
            url = reverse('catalog:entry', args=[entry['id']])
            if block['kind'] == 'question':
                url += '?' + urlencode({'answer': block['id']})
            context.update(return_url=url + '#' +
                           block['id'], return_label='Back to ' + block['title'])
    return render(request, 'formalization/node.html', context)
