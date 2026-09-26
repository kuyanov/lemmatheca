"""File-backed formal nodes. Completion is evidence, not an editable status."""

from functools import lru_cache
import hashlib
import json
import re

from django.urls import reverse

from catalog.files import file_signature, read_json
from catalog.metadata import fields
from catalog.sources import ContentError, IDENTIFIER

from .lean import (LIBRARY_INPUT, REVIEW_MODULE, TOOLCHAIN_MODULES, lean_source_path,
                   library_overrides, library_revisions, local_sources, module_source_path, source_roots)
from .reviews import SHA256, digest, review_target_hash, validate_review


NODE_FIELDS = {'id', 'description', 'declaration',
               'module', 'dependencies', 'review'}
# Only the binding selects what Lean checks; proof planning is resolved separately.
VERIFICATION_FIELDS = {'id', 'declaration', 'module'}
LEAN_NAME = re.compile(r"[^\W\d][\w']*(?:\.[^\W\d][\w']*)*\Z", re.UNICODE)
ALLOWED_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}
REPORT = 'formal/checks/nodes.json'
REPORT_VERSION = 7
# Storage-only report changes must not invalidate existing verification.
VERIFICATION_POLICY_VERSION = 5
ENVIRONMENT = ('lean-toolchain', 'lake-manifest.json', 'lakefile.toml')
NODE_STATUS_LABELS = {
    'declaration_missing': 'Declaration missing',
    'review_pending': 'Pending review',
    'review_outdated': 'Review outdated',
    'verification_needed': 'Verification needed',
    'proof_pending': 'Proof pending',
    'complete': 'Complete',
}


def verification_group(module):
    """Library bindings share one audit; project modules remain independent."""
    return 'Mathlib' if module and module.startswith('Mathlib.') else module


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
        if (source.split('/')[0] in TOOLCHAIN_MODULES
                or source_is_fingerprinted(source, report.get('sha256', {}))):
            return source, location['line']
    return node['source'], None


def source_input_key(source):
    if source and source.startswith('Mathlib/'):
        return LIBRARY_INPUT
    return source


def source_is_fingerprinted(source, inputs):
    return isinstance(inputs, dict) and source_input_key(source) in inputs


def node_fingerprint(node):
    # Descriptions affect correspondence review, not Lean verification.
    record = {key: node[key] for key in sorted(VERIFICATION_FIELDS)}
    return hashlib.sha256(json.dumps(record, sort_keys=True).encode()).hexdigest()


def file_hash(path):
    stat = path.stat()
    return _file_hash(path, stat.st_mtime_ns, stat.st_ctime_ns, stat.st_size)


@lru_cache(maxsize=16384)
def _file_hash(path, modified, changed, size):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def library_hash(root, *, required=False):
    revisions = library_revisions(root)
    if required and (not revisions or any(revision is None for revision in revisions.values())):
        raise ContentError(
            'Missing installed Lean libraries or unreadable package revisions')
    overrides = {path.relative_to(root).as_posix(): file_hash(path)
                 for path in library_overrides(root)}
    return digest({'revisions': revisions, 'overrides': overrides}) if revisions or overrides else None


def verification_input_hash(path, root):
    if path != root / LIBRARY_INPUT:
        return file_hash(path)
    return library_hash(root, required=True)


def report_input_path(root, relative):
    """Reports may fingerprint Lean sources and environment files, never arbitrary files."""
    if not isinstance(relative, str):
        raise ContentError('Invalid verification input path')
    parts = relative.split('/')
    if any(not part or part in ('.', '..') for part in parts) or '\\' in relative:
        raise ContentError('Invalid verification input path')
    path = root / relative
    formal = root / 'formal'
    allowed = (relative == LIBRARY_INPUT or relative in {f'formal/{name}' for name in ENVIRONMENT}
               or (relative.startswith('formal/') and relative.endswith('.lean')
                   and not any(part.startswith('.') for part in parts)))
    if not allowed or not path.resolve().is_relative_to(formal.resolve()):
        raise ContentError(
            'Verification input is outside the formal source tree')
    return path


def verification_policy_hash():
    return digest({'version': VERIFICATION_POLICY_VERSION, 'allowed_axioms': sorted(ALLOWED_AXIOMS)})


def input_module(relative):
    """Recover the module name from a recorded local Lean source path."""
    return '.'.join(relative.split('/')[1:]).removesuffix('.lean')


def module_is_current(record, root, module, *, input_cache=None):
    if (not isinstance(record, dict) or record.get('status') != 'passed'
            or record.get('policy_sha256') != verification_policy_hash()
            or not isinstance(record.get('checked_on'), str) or not record['checked_on']):
        return False
    hashes = record.get('sha256')
    required = {f'formal/{name}' for name in ENVIRONMENT}
    module_input = (LIBRARY_INPUT if module == 'Mathlib'
                    else source_input_key(source_for_module(module)))
    required.update((module_input,
                     source_for_module(REVIEW_MODULE)))
    if not isinstance(hashes, dict) or not required <= hashes.keys():
        return False
    cache = input_cache if input_cache is not None else {}
    roots = source_roots(root)

    def matches(relative, expected):
        path = report_input_path(root, relative)
        if relative == LIBRARY_INPUT:
            # With no dependency checkout, serve pinned, committed evidence.
            actual = library_hash(root)
            return actual is None or actual == expected
        if relative.endswith('.lean'):
            resolved = module_source_path(input_module(
                relative), root, roots=roots, required=False)
            if resolved is not None and resolved != path:
                # A new source shadows the previously resolved module.
                return False
        return path.is_file() and file_hash(path) == expected

    for relative, expected in hashes.items():
        if not isinstance(expected, str) or not SHA256.fullmatch(expected):
            return False
        key = (relative, expected)
        if key not in cache:
            try:
                cache[key] = matches(relative, expected)
            except ContentError:
                cache[key] = False
        if not cache[key]:
            return False
    return True


def current_node_evidence(node, checked, inputs):
    """Validate a node snapshot; source freshness is checked at module level."""
    if not isinstance(checked, dict) or checked.get('fingerprint') != node_fingerprint(node):
        return {}
    declaration_hash = checked.get('declaration_sha256')
    axioms = checked.get('axioms')
    if (not isinstance(declaration_hash, str) or not SHA256.fullmatch(declaration_hash)
            or not isinstance(axioms, list) or any(not isinstance(axiom, str) for axiom in axioms)
            or set(axioms) - ALLOWED_AXIOMS - {'sorryAx'}
            or checked.get('status') != ('pending' if 'sorryAx' in axioms else 'complete')
            or not source_is_fingerprinted(node['source'], inputs)):
        return {}
    return checked


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
            # A missing module makes its evidence stale, not the whole registry invalid.
            lean_source_path(source, root, require_file=False)
        if node['review'] is not None and declaration is None:
            raise ContentError(
                'A node without a declaration cannot be reviewed')
        nodes[node['id']] = {**node, 'source': source}

    report_path = root / REPORT
    report = read_json(
        report_path) if check_reports and nodes and report_path.exists() else {}
    supported = report.get('format_version') == REPORT_VERSION
    evidence = report.get('nodes', {}) if supported else {}
    modules = report.get('modules', {}) if supported else {}
    input_cache = {}
    current_modules = {module: modules[module] for module in {verification_group(node['module']) for node in nodes.values()}
                       if module in modules and module_is_current(modules[module], root, module,
                                                                  input_cache=input_cache)}
    # Validate the proof plan's references and acyclicity, independently of status.
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
        group = verification_group(node['module'])
        module_report = modules.get(group, {})
        last_checked = current_node_evidence(
            node, evidence.get(node_id), module_report.get('sha256', {})
        ) if module_report.get('status') == 'passed' else {}
        # A stale source does not retract a recorded approval. Compare current
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
    library_signature = ()
    if report.exists():
        saved = read_json(report)
        records = saved.get('modules', {}).values() if saved.get(
            'format_version') == REPORT_VERSION else ()
        inputs = {name for record in records if isinstance(record.get('sha256'), dict)
                  for name in record['sha256']}
        roots = source_roots(root)
        for name in inputs:
            try:
                paths.add(report_input_path(root, name))
            except ContentError:
                # Invalid evidence is stale; its report is still watched.
                continue
            if name == LIBRARY_INPUT:
                library_signature = ((LIBRARY_INPUT, library_hash(root)),)
            if name.endswith('.lean'):
                relative = input_module(name).replace('.', '/') + '.lean'
                paths.update(base / relative for base in roots)
    return tuple(file_signature(path) for path in sorted(paths)) + library_signature


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
