"""File-backed formal nodes. Completion is evidence, not an editable status."""

from functools import lru_cache
import hashlib
import json
import re

from django.urls import reverse

from catalog.files import file_signature, read_json
from catalog.metadata import fields
from catalog.sources import ContentError, IDENTIFIER

from .lean import TOOLCHAIN_MODULES, lean_source_path, local_sources
from .reviews import SHA256, validate_review


NODE_FIELDS = {'id', 'description', 'declaration',
               'module', 'dependencies', 'review'}
# Editorial prose is reviewed through Git, separately from Lean target approval.
TARGET_FIELDS = {'id', 'declaration', 'module', 'dependencies'}
LEAN_NAME = re.compile(r"[^\W\d][\w']*(?:\.[^\W\d][\w']*)*\Z", re.UNICODE)
ALLOWED_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}
REPORT = 'formal/checks/nodes.json'
REPORT_VERSION = 3
ENVIRONMENT = ('lean-toolchain', 'lake-manifest.json', 'lakefile.toml')
NODE_STATUS_LABELS = {
    'declaration_missing': 'Declaration missing',
    'review_pending': 'Pending review',
    'review_outdated': 'Review outdated',
    'verification_needed': 'Verification needed',
    'proof_pending': 'Proof pending',
    'dependencies_pending': 'Dependencies pending',
    'complete': 'Complete',
}


def source_for_module(module, *, allow_toolchain=False):
    if not isinstance(module, str) or not LEAN_NAME.fullmatch(module):
        raise ContentError('Invalid Lean module')
    if module.startswith('Lemmatheca.'):
        return 'formal/' + module.replace('.', '/') + '.lean'
    if module.startswith('Mathlib.') or (allow_toolchain and '.' in module
                                         and module.split('.')[0] in TOOLCHAIN_MODULES):
        return module.replace('.', '/') + '.lean'
    raise ContentError('Nodes must use Lemmatheca or Mathlib modules')


def checked_source_location(node, checked, report):
    """A declaration can originate in a different module from the node's import."""
    location = checked.get('location')
    if isinstance(location, dict) and type(location.get('line')) is int and location['line'] > 0:
        try:
            source = source_for_module(
                location.get('module'), allow_toolchain=True)
        except ContentError:
            return node['source'], None
        # Imported sources need current fingerprints; bundled Lean sources are
        # covered by the pinned toolchain in the verification report.
        if source.split('/')[0] in TOOLCHAIN_MODULES or source_input_key(source) in report.get('sha256', {}):
            return source, location['line']
    return node['source'], None


def source_input_key(source):
    if source and source.startswith('Mathlib/'):
        return 'formal/.lake/packages/mathlib/' + source
    return source


def node_fingerprint(node):
    # Editorial descriptions and review decisions do not change the Lean target.
    record = {key: node[key] for key in sorted(TARGET_FIELDS)}
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


def current_node_evidence(node, checked, inputs):
    """Ignore incomplete, stale, or inconsistent evidence for a declaration."""
    if not isinstance(checked, dict) or checked.get('fingerprint') != node_fingerprint(node):
        return {}
    target_hash = checked.get('target_sha256')
    axioms = checked.get('axioms')
    if (not isinstance(target_hash, str) or not SHA256.fullmatch(target_hash)
            or not isinstance(axioms, list) or any(not isinstance(axiom, str) for axiom in axioms)
            or set(axioms) - ALLOWED_AXIOMS - {'sorryAx'}
            or checked.get('status') != ('pending' if 'sorryAx' in axioms else 'complete')
            or source_input_key(node['source']) not in inputs):
        return {}
    return checked


def node_status(node, checked, nodes):
    """Report the first remaining requirement, after resolving dependencies."""
    if not node['declaration']:
        return 'declaration_missing'
    if node['review'] is None:
        return 'review_pending'
    if not checked:
        return 'verification_needed'
    if node['review']['sha256'] != checked['target_sha256']:
        return 'review_outdated'
    if checked['status'] == 'pending':
        return 'proof_pending'
    if any(nodes[item]['status'] != 'complete' for item in node['dependencies']):
        return 'dependencies_pending'
    return 'complete'


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
            lean_source_path(
                source, root, require_file=not module.startswith('Mathlib.'))
        if node['review'] is not None and declaration is None:
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
        checked = current_node_evidence(
            node, evidence.get(node_id), report.get('sha256', {}))
        status = node_status(node, checked, nodes)
        target_hash = checked.get('target_sha256')
        signature = checked.get('signature')
        source, line = (checked_source_location(node, checked, report)
                        if checked else (node['source'], None))
        node.update(source=source, status=status, status_label=NODE_STATUS_LABELS[status],
                    signature=signature if isinstance(
                        signature, str) else None,
                    target_sha256=target_hash,
                    review_current=bool(checked and node['review'] is not None
                                        and node['review']['sha256'] == target_hash),
                    verification_complete=bool(checked and checked['status'] == 'complete'),
                    declaration_line=line,
                    checked_on=report.get('checked_on') if checked else None,
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
