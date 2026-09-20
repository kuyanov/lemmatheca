"""File-backed formal nodes. Completion is evidence, not an editable status."""

from functools import lru_cache
import hashlib
import json
import re

from django.urls import reverse

from catalog.files import file_signature, read_json
from .lean import lean_source_path, local_sources
from catalog.metadata import fields
from catalog.sources import ContentError, IDENTIFIER


NODE_FIELDS = {'id', 'declaration', 'module', 'dependencies', 'reviewed'}
LEAN_NAME = re.compile(r"[^\W\d][\w']*(?:\.[^\W\d][\w']*)*\Z", re.UNICODE)
ALLOWED_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}
REPORT = 'formal/checks/nodes.json'
REPORT_VERSION = 2
ENVIRONMENT = ('lean-toolchain', 'lake-manifest.json', 'lakefile.toml')
NODE_STATUS_LABELS = {
    'declaration_missing': 'Declaration missing',
    'review_pending': 'Pending review',
    'verification_needed': 'Verification needed',
    'proof_pending': 'Proof pending',
    'dependencies_pending': 'Dependencies pending',
    'complete': 'Complete',
}


def source_for_module(module):
    if not isinstance(module, str) or not LEAN_NAME.fullmatch(module):
        raise ContentError('Invalid Lean module')
    if module.startswith('Lemmatheca.'):
        return 'formal/' + module.replace('.', '/') + '.lean'
    if module.startswith('Mathlib.'):
        return module.replace('.', '/') + '.lean'
    raise ContentError('Nodes must use Lemmatheca or Mathlib modules')


def node_fingerprint(node):
    # Review is a human decision, independent of Lean's evidence for the target.
    record = {key: node[key] for key in sorted(NODE_FIELDS - {'reviewed'})}
    return hashlib.sha256(json.dumps(record, sort_keys=True).encode()).hexdigest()


def file_hash(path):
    stat = path.stat()
    return _file_hash(path, stat.st_mtime_ns, stat.st_ctime_ns, stat.st_size)


@lru_cache(maxsize=16384)
def _file_hash(path, modified, changed, size):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def report_input_path(root, relative):
    """Reports may fingerprint Lean sources and environment files, never arbitrary files."""
    parts = relative.split('/')
    if any(not part or part in ('.', '..') for part in parts) or '\\' in relative:
        raise ContentError('Invalid verification input path')
    path = root / relative
    formal = root / 'formal'
    allowed = (relative in {f'formal/{name}' for name in ENVIRONMENT}
               or (relative.startswith('formal/') and relative.endswith('.lean')))
    if not allowed or not path.resolve().is_relative_to(formal.resolve()):
        raise ContentError(
            'Verification input is outside the formal source tree')
    return path


def report_is_current(report, root):
    if report.get('format_version') != REPORT_VERSION or report.get('build') != 'passed':
        return False
    hashes = report.get('sha256')
    if not isinstance(hashes, dict) or not {f'formal/{name}' for name in ENVIRONMENT} <= hashes.keys():
        return False
    # Changing any local source invalidates the run, including adding a new module.
    local = {path.relative_to(root).as_posix() for path in local_sources(root)}
    if local != {name for name in hashes if name.startswith('formal/Lemmatheca/')
                 or name == 'formal/Lemmatheca.lean'}:
        return False
    for relative, expected in hashes.items():
        path = report_input_path(root, relative)
        # A web-only deployment may omit Lake's pinned dependency checkout.
        if not path.exists() and relative.startswith('formal/.lake/packages/'):
            continue
        if not path.is_file() or file_hash(path) != expected:
            return False
    return True


def load_nodes(root, *, check_reports=True):
    nodes = {}
    directory = root / 'formal/nodes'
    for path in sorted(directory.glob('*.json')):
        if not path.resolve().is_relative_to(directory.resolve()):
            raise ContentError('Formal node is outside formal/nodes')
        node = read_json(path)
        fields(node, NODE_FIELDS)
        if not isinstance(node['id'], str) or not IDENTIFIER.fullmatch(node['id']) or path.stem != node['id']:
            raise ContentError('Formal node ID must match its filename')
        if type(node['reviewed']) is not bool:
            raise ContentError('Node reviewed must be true or false')
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
            lean_source_path(
                source, root, require_file=not module.startswith('Mathlib.'))
        if node['reviewed'] and declaration is None:
            raise ContentError(
                'A node without a declaration cannot be reviewed')
        nodes[node['id']] = {**node, 'source': source}

    report_path = root / REPORT
    report = read_json(
        report_path) if check_reports and nodes and report_path.exists() else {}
    current = bool(report) and report_is_current(report, root)
    evidence = report.get('nodes', {}) if current else {}
    visiting, visited = set(), set()

    def resolve(node_id):
        if node_id not in nodes:
            raise ContentError(f'Unknown formal node: {node_id}')
        if node_id in visiting:
            raise ContentError(f'Formal dependency cycle at {node_id}')
        if node_id in visited:
            return
        visiting.add(node_id)
        node = nodes[node_id]
        for dependency in node['dependencies']:
            resolve(dependency)
        checked = evidence.get(node_id, {})
        source_key = (('formal/.lake/packages/mathlib/' + node['source'])
                      if (node['module'] or '').startswith('Mathlib.') else node['source'])
        axioms = checked.get('axioms')
        checked_current = (checked.get('fingerprint') == node_fingerprint(node)
                           and isinstance(axioms, list)
                           and all(isinstance(axiom, str) for axiom in axioms)
                           and set(axioms) <= ALLOWED_AXIOMS | {'sorryAx'}
                           and checked.get('status') == ('pending' if 'sorryAx' in axioms else 'complete')
                           and source_key in report.get('sha256', {}))
        # A stale proof result cannot describe the current declaration.
        status = ('declaration_missing' if not node['declaration'] else
                  'review_pending' if not node['reviewed'] else
                  'verification_needed' if not checked_current else
                  'proof_pending' if checked['status'] == 'pending' else
                  'dependencies_pending' if any(nodes[item]['status'] != 'complete' for item in node['dependencies']) else
                  'complete')
        node.update(status=status, status_label=NODE_STATUS_LABELS[status],
                    checked_on=report.get(
                        'checked_on') if checked_current else None,
                    url=reverse('formalization:node', args=[node_id]))
        visiting.remove(node_id)
        visited.add(node_id)

    for node_id in nodes:
        resolve(node_id)
    return nodes


def formal_signature(root):
    paths = set((root / 'formal/nodes').glob('*.json'))
    if not paths:
        return ()
    paths.update(local_sources(root))
    paths.update(root / 'formal' / name for name in ENVIRONMENT)
    report = root / REPORT
    paths.add(report)
    if report.exists():
        paths.update(report_input_path(root, name)
                     for name in read_json(report).get('sha256', {}))
    return tuple(file_signature(path) for path in sorted(paths))


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
    # Linked nodes do not measure how much of an entire entry has been covered.
    result.pop('percent')
    if result['status'] == 'partial':
        result['label'] = 'Partial'
        result['description'] = 'Formalization partial; ' + \
            result['description']
    return result
