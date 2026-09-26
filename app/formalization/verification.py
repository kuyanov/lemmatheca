"""Verification reports, fingerprints, evidence freshness, and cache invalidation.

This layer does not load node JSON, derive review status, or invoke Lean.
"""

from functools import lru_cache
import hashlib
import json

from catalog.files import file_signature, read_json
from catalog.sources import ContentError

from .lean import (ENVIRONMENT, LIBRARY_INPUT, REVIEW_MODULE, TOOLCHAIN_MODULES,
                   library_overrides, library_revisions, local_sources,
                   module_source_path, source_for_module, source_roots)
from .reviews import SHA256, digest


# Descriptions and proof planning do not select what Lean verifies.
VERIFICATION_FIELDS = ('declaration', 'id', 'module')
ALLOWED_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}
REPORT = 'formal/checks/nodes.json'
REPORT_VERSION = 8
# Storage-only report changes must not invalidate existing verification.
VERIFICATION_POLICY_VERSION = 6


def normalize_verification_report(report, nodes):
    """Split the former shared audit without inventing checks or changing dates."""
    if report.get('format_version') == REPORT_VERSION:
        return report
    if report.get('format_version') != 7:
        return {}
    modules = dict(report.get('modules', {}))
    shared = modules.pop('Mathlib', None)
    if shared is not None:
        for module in {node['module'] for node in nodes.values()
                       if node['module'] and node['module'].startswith('Mathlib.')}:
            # The shared audit checked each import separately. Retain its full
            # input hashes and any failure history; node fingerprints still gate
            # reuse if a binding has changed or a node has been added since then.
            modules.setdefault(module, shared)
    return {**report, 'format_version': REPORT_VERSION, 'modules': modules}


def node_fingerprint(node):
    # Descriptions affect correspondence review, not Lean verification.
    record = {key: node[key] for key in VERIFICATION_FIELDS}
    # Keep the existing JSON encoding: changing it would discard stored evidence.
    return hashlib.sha256(json.dumps(record, sort_keys=True).encode()).hexdigest()


def file_hash(path):
    stat = path.stat()
    return _file_hash(path, stat.st_mtime_ns, stat.st_ctime_ns, stat.st_size)


@lru_cache(maxsize=16384)
def _file_hash(path, modified, changed, size):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def library_hash(root, *, required=False):
    revisions = library_revisions(root, required=required)
    if required and not revisions:
        raise ContentError(
            'Missing installed Lean libraries; install clean Git checkouts with Lake')
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
    if any(not part or part in ('.', '..') for part in parts) or '\\' in relative or '\x00' in relative:
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


def successful_module_snapshot(record):
    """The last successful input snapshot, even after a later failed attempt."""
    if not isinstance(record, dict):
        return {}
    snapshot = record if record.get(
        'status') == 'passed' else record.get('last_success', {})
    return snapshot if isinstance(snapshot, dict) and snapshot.get('status') == 'passed' else {}


def input_module(relative):
    """Recover the module name from a recorded local Lean source path."""
    return '.'.join(relative.split('/')[1:]).removesuffix('.lean')


def source_input_key(source):
    if source and source.startswith('Mathlib/'):
        return LIBRARY_INPUT
    return source


def source_is_fingerprinted(source, inputs):
    return isinstance(inputs, dict) and source_input_key(source) in inputs


def module_is_current(record, root, module, *, input_cache=None, require_libraries=False):
    """Compare recorded inputs with a shared, per-operation snapshot of current inputs.

    Cache actual hashes, not matches to old hashes: partial module checks can leave
    several recorded versions of one input. Never reuse this cache across operations.
    """
    if (not isinstance(record, dict) or record.get('status') != 'passed'
            or record.get('policy_sha256') != verification_policy_hash()
            or not isinstance(record.get('checked_on'), str) or not record['checked_on']):
        return False
    hashes = record.get('sha256')
    required = {f'formal/{name}' for name in ENVIRONMENT}
    module_input = source_input_key(source_for_module(module))
    required.update((module_input,
                     source_for_module(REVIEW_MODULE)))
    if not isinstance(hashes, dict) or not required <= hashes.keys():
        return False
    cache = input_cache if input_cache is not None else {}

    def current_hash(relative):
        path = report_input_path(root, relative)
        if relative == LIBRARY_INPUT:
            # With no dependency checkout, serve pinned, committed evidence.
            return library_hash(root, required=require_libraries)
        if relative.endswith('.lean'):
            resolved = module_source_path(input_module(
                relative), root, required=False)
            if resolved is not None and resolved != path:
                # A new source shadows the previously resolved module.
                return False
        return file_hash(path) if path.is_file() else False

    for relative, expected in hashes.items():
        if not isinstance(expected, str) or not SHA256.fullmatch(expected):
            return False
        key = (root, relative, require_libraries)
        if key not in cache:
            try:
                cache[key] = current_hash(relative)
            except (ContentError, OSError):
                cache[key] = False
        if cache[key] is not None and cache[key] != expected:
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


def verification_signature(root):
    """Watch verification inputs, including failed groups' last successful snapshots."""
    paths = local_sources(root)
    paths.update(root / 'formal' / name for name in ENVIRONMENT)
    report = root / REPORT
    paths.add(report)
    library_signature = ()
    if report.exists():
        saved = read_json(report)
        records = saved.get('modules', {}).values() if saved.get(
            'format_version') in (7, REPORT_VERSION) else ()
        inputs = {name for record in records for snapshot in (record, successful_module_snapshot(record))
                  if isinstance(snapshot.get('sha256'), dict) for name in snapshot['sha256']}
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
