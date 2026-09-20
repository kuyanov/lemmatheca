"""Read-only node API and node pages, separate from human entry metadata."""

from django.conf import settings
from django.http import Http404, JsonResponse
from django.shortcuts import render
from django.views.decorators.http import require_safe

from .lean import source_context
from .nodes import load_nodes


@require_safe
def node_list(request):
    return JsonResponse({'nodes': list(load_nodes(settings.REPOSITORY_DIR).values())})


def get_node(nodes, node_id):
    node = nodes.get(node_id)
    if node is None:
        raise Http404('This formal node is not in the library.')
    return node


@require_safe
def node_detail(request, node_id):
    return JsonResponse(get_node(load_nodes(settings.REPOSITORY_DIR), node_id))


@require_safe
def node_page(request, node_id):
    nodes = load_nodes(settings.REPOSITORY_DIR)
    node = get_node(nodes, node_id)
    context = {'node': node, 'dependencies': [nodes[item] for item in node['dependencies']]}
    if node['source']:
        context.update(source_context(
            node['source'], settings.REPOSITORY_DIR, node['declaration']))
    return render(request, 'formalization/node.html', context)
