"""File-backed formal nodes. Completion is evidence, not an editable status."""

from graphlib import CycleError, TopologicalSorter

from django.urls import reverse

from catalog.files import file_signature, read_json
from catalog.metadata import fields
from catalog.sources import ContentError, IDENTIFIER

from .lean import LEAN_NAME, lean_source_path, source_for_module
from .reviews import review_target_hash, validate_review
from .verification import (
    REPORT, checked_source_location, current_node_evidence, module_is_current,
    normalize_verification_report, successful_module_snapshot, verification_signature,
)


NODE_FIELDS = {'id', 'description', 'declaration',
               'module', 'dependencies', 'review'}
NODE_STATUS_LABELS = {
    'declaration_missing': 'Declaration missing',
    'review_pending': 'Pending review',
    'review_outdated': 'Review outdated',
    'verification_needed': 'Verification needed',
    'proof_pending': 'Proof pending',
    'complete': 'Complete',
}


def node_status(node, checked, target_hash):
    """Report this node's first remaining review or verification requirement."""
    if not node['declaration']:
        return 'declaration_missing'
    if node['review'] is None:
        return 'review_pending'
    if not checked:
        return 'verification_needed'
    if node['review']['sha256'] != target_hash:
        return 'review_outdated'
    if checked['status'] == 'pending':
        return 'proof_pending'
    return 'complete'


def read_registry(root):
    """Load and validate node records independently of verification evidence."""
    nodes = {}
    directory = root / 'formal/nodes'
    resolved_directory = directory.resolve()
    for path in sorted(directory.glob('*.json')):
        if not path.resolve().is_relative_to(resolved_directory):
            raise ContentError('Formal node is outside formal/nodes')
        node = read_json(path)
        fields(node, NODE_FIELDS)
        if not isinstance(node['id'], str) or not IDENTIFIER.fullmatch(node['id']) or path.stem != node['id']:
            raise ContentError('Formal node ID must match its filename')
        if not isinstance(node['description'], str) or not node['description'].strip():
            raise ContentError('Node description must be nonempty text')
        validate_review(node['review'])
        if not isinstance(node['dependencies'], list) or any(
                not isinstance(item, str) or not IDENTIFIER.fullmatch(item) for item in node['dependencies']):
            raise ContentError('Node dependencies must be a list of node IDs')
        if len(set(node['dependencies'])) != len(node['dependencies']):
            raise ContentError('Duplicate formal dependency')
        declaration, module = node['declaration'], node['module']
        if (declaration is None) != (module is None):
            raise ContentError(
                'A node needs both a declaration and module, or neither')
        source = None
        if declaration is not None:
            if not isinstance(declaration, str) or not LEAN_NAME.fullmatch(declaration):
                raise ContentError('Invalid Lean declaration name')
            source = source_for_module(module)
            # A missing module makes its evidence stale, not the whole registry invalid.
            lean_source_path(source, root, require_file=False)
        if node['review'] is not None and declaration is None:
            raise ContentError(
                'A node without a declaration cannot be reviewed')
        nodes[node['id']] = {**node, 'source': source}
    validate_dependencies(nodes)
    return nodes


def validate_dependencies(nodes):
    """Proof plans must reference an acyclic graph; they never gate completion."""
    graph = {node_id: node['dependencies'] for node_id, node in nodes.items()}
    for dependencies in graph.values():
        for dependency in dependencies:
            if dependency not in nodes:
                raise ContentError(f'Unknown formal node: {dependency}')
    try:
        TopologicalSorter(graph).prepare()
    except CycleError as error:
        raise ContentError(
            f'Formal dependency cycle at {error.args[1][0]}') from error


def load_nodes(root, *, check_reports=True):
    """Attach each node's own review and verification status to the registry."""
    nodes = read_registry(root)

    report_path = root / REPORT
    report = read_json(
        report_path) if check_reports and nodes and report_path.exists() else {}
    report = normalize_verification_report(report, nodes)
    evidence = report.get('nodes', {})
    modules = report.get('modules', {})
    input_cache = {}
    current_modules = {module for module in {node['module'] for node in nodes.values()}
                       if module in modules and module_is_current(modules[module], root, module,
                                                                  input_cache=input_cache)}
    for node_id, node in nodes.items():
        group = node['module']
        module_report = modules.get(group, {})
        successful = successful_module_snapshot(module_report)
        last_checked = current_node_evidence(
            node, evidence.get(node_id), successful.get('sha256', {})
        ) if successful else {}
        # Stale or failed verification does not retract a recorded approval. Compare current
        # prose with the last checked semantics for the historical review label,
        # but expose a current target only after the module has been rechecked.
        last_target = (review_target_hash(node, last_checked['declaration_sha256'])
                       if last_checked else None)
        review_matches_last_check = bool(last_checked and node['review'] is not None
                                         and node['review']['sha256'] == last_target)
        checked = last_checked if group in current_modules else {}
        target_hash = last_target if checked else None
        status = node_status(node, checked, target_hash)
        signature = checked.get('signature')
        source, line = (checked_source_location(node, checked, module_report)
                        if checked else (node['source'], None))
        node.update(source=source, status=status, status_label=NODE_STATUS_LABELS[status],
                    signature=signature if isinstance(
                        signature, str) else None,
                    target_sha256=target_hash,
                    review_matches_last_check=review_matches_last_check,
                    review_current=bool(checked and review_matches_last_check),
                    verification_complete=bool(
                        checked and checked['status'] == 'complete'),
                    declaration_line=line,
                    checked_on=module_report.get(
                        'checked_on') if checked else None,
                    url=reverse('formalization:node', args=[node_id]))
    return nodes


def formal_signature(root):
    """Watch the registry and its verification inputs for catalog/review changes."""
    paths = sorted((root / 'formal/nodes').glob('*.json'))
    if not paths:
        return ()
    return tuple(file_signature(path) for path in paths) + verification_signature(root)


def progress(ids, nodes, *, unplanned=0, applicable=True):
    ids = set(ids)
    unknown = ids - nodes.keys()
    if unknown:
        raise ContentError(f'Unknown formal node: {sorted(unknown)[0]}')
    complete = sum(nodes[node_id]['status'] == 'complete' for node_id in ids)
    total = len(ids)
    status = ('not_applicable' if not applicable else
              'not_started' if not total else
              'complete' if complete == total and not unplanned else 'partial')
    percent = complete * 100 // total if total else 0
    label = {'not_started': 'Not started', 'not_applicable': 'N/A',
             'complete': 'Complete', 'partial': f'{percent}%'}[status]
    description = {'not_started': 'Formalization not started',
                   'not_applicable': 'Nothing to formalize',
                   'complete': 'Formalization complete',
                   'partial': f'{complete} of {total} nodes verified'}[status]
    if unplanned and total:
        description += f'; {unplanned} blocks awaiting planning'
    return {'status': status, 'complete': complete, 'total': total, 'percent': percent,
            'unplanned': unplanned, 'label': label, 'description': description}


def block_progress(ids, nodes):
    return progress(ids or [], nodes, unplanned=int(ids is None), applicable=ids != [])


def entry_progress(blocks, nodes):
    result = progress([node_id for block in blocks for node_id in block['formal_ids'] or []], nodes,
                      unplanned=sum(block['formal_ids']
                                    is None for block in blocks),
                      applicable=any(block['formal_ids'] != [] for block in blocks))
    if result['unplanned']:
        # An unmapped block leaves the entry's total number of nodes unknown.
        result.pop('percent')
        if result['unplanned'] < len(blocks):
            result.update(status='partial', label='Partial')
            result['description'] = 'Formalization partial; '
            if result['total']:
                result['description'] += f'{result["complete"]} of {result["total"]} nodes verified; '
            result['description'] += f'{result["unplanned"]} blocks awaiting planning'
    elif result['total']:
        result['label'] = f'{result["percent"]}%'
        result['description'] = f'{result["complete"]} of {result["total"]} nodes verified'
    else:
        result.pop('percent')
    return result
