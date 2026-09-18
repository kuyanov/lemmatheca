"""The deliberately small entry metadata contract."""

import re
from urllib.parse import urlsplit

from .sources import ContentError
from .lean import lean_source_path

ENTRY_FIELDS = {'id', 'title', 'authors', 'license', 'primary_area', 'additional_areas',
                'status', 'reading_time', 'summary', 'abstract', 'blocks'}
FORMAL_FIELDS = {'status', 'declaration', 'source', 'verification_report', 'module',
                 'unformalized_dependencies'}
FORMAL_STATUSES = {'not_started', 'partial', 'complete'}
DEPENDENCY_FIELDS = {'declaration', 'module', 'source'}
LEAN_NAME = re.compile(r"[^\W\d][\w']*(?:\.[^\W\d][\w']*)*\Z", re.UNICODE)


def fields(value, required, optional=frozenset()):
    if not isinstance(value, dict) or not required <= value.keys() or value.keys() - required - optional:
        raise ContentError(f"Expected fields: {', '.join(sorted(required))}")


def validate_entry_metadata(entry):
    fields(entry, ENTRY_FIELDS, {'source'})
    for key in ('id', 'title', 'license', 'primary_area', 'status', 'summary', 'abstract'):
        if not isinstance(entry[key], str) or not entry[key].strip():
            raise ContentError(f"{key} must be nonempty text")
    if not re.fullmatch(r'[A-Za-z0-9.+-]+', entry['license']):
        raise ContentError('Use an SPDX license identifier')
    if not isinstance(entry['authors'], list) or not entry['authors'] or not all(
            isinstance(name, str) and name.strip() for name in entry['authors']):
        raise ContentError('authors must be a nonempty list of names')
    if not isinstance(entry['additional_areas'], list) or not all(
            isinstance(area, str) for area in entry['additional_areas']):
        raise ContentError('additional_areas must be a list of area IDs')
    if type(entry['reading_time']) is not int or entry['reading_time'] <= 0:
        raise ContentError('reading_time must be a positive number of minutes')
    if not isinstance(entry['blocks'], dict):
        raise ContentError('blocks must be keyed by block ID')
    if 'source' in entry:
        fields(entry['source'], {'title', 'url'})
        source = entry['source']
        if not isinstance(source['title'], str) or not source['title'].strip():
            raise ContentError('A material source needs a title')
        if not isinstance(source['url'], str):
            raise ContentError('A material source needs an HTTP(S) URL')
        url = urlsplit(source['url'])
        if url.scheme not in ('http', 'https') or not url.netloc:
            raise ContentError('A material source needs an HTTP(S) URL')


def formal_source_path(formal, repository_dir, *, require_file=True):
    module = formal['module']
    if not module or not LEAN_NAME.fullmatch(module):
        raise ContentError(f'Invalid Lean module: {module}')
    relative = module.replace('.', '/') + '.lean'
    if module.startswith('Mathlib.'):
        expected = relative
    elif module.startswith('Lemmatheca.'):
        expected = 'formal/' + relative
    else:
        raise ContentError('Use a Lemmatheca or Mathlib module')
    if formal['source'] != expected:
        raise ContentError(f'Missing or mismatched Lean source: {expected}')
    return lean_source_path(expected, repository_dir, require_file=require_file)


def validate_block_metadata(block, repository_dir, read_json, check_reports=True):
    fields(block, {'formalization', 'references'})
    formal = block['formalization']
    fields(formal, FORMAL_FIELDS)
    if formal['status'] not in FORMAL_STATUSES:
        raise ContentError('Formalization status must be not_started, partial, or complete')
    for key in ('declaration', 'source', 'verification_report', 'module'):
        if formal[key] is not None and (not isinstance(formal[key], str) or not formal[key]):
            raise ContentError(f'{key} must be text or null')
    if formal['declaration'] and not LEAN_NAME.fullmatch(formal['declaration']):
        raise ContentError('Invalid Lean declaration name')
    pending = formal['unformalized_dependencies']
    if not isinstance(pending, list):
        raise ContentError('unformalized_dependencies must be a list of Lean bindings')
    if formal['status'] == 'complete' and pending:
        raise ContentError('Complete formalizations cannot have unformalized dependencies')
    declarations = set()
    for dependency in pending:
        fields(dependency, DEPENDENCY_FIELDS)
        if not all(isinstance(value, str) and value.strip() for value in dependency.values()):
            raise ContentError('Pending dependencies need a declaration, module, and source')
        name = dependency['declaration']
        if not LEAN_NAME.fullmatch(name):
            raise ContentError('Invalid pending Lean declaration name')
        if name in declarations:
            raise ContentError(f'Duplicate pending dependency: {name}')
        declarations.add(name)
        if not dependency['module'].startswith('Lemmatheca.'):
            raise ContentError('Pending dependencies must use local Lemmatheca sources')
        formal_source_path(dependency, repository_dir)
    if formal['module'] or formal['source']:
        # A read-only server can use the committed verification report without
        # installing Lake's ignored mathlib checkout. Local sources stay required.
        formal_source_path(formal, repository_dir,
                           require_file=not (formal['module'] or '').startswith('Mathlib.'))
    if formal['status'] == 'complete' and not all(formal[key] for key in
            ('declaration', 'source', 'module', 'verification_report')):
        raise ContentError('Complete formalizations need a declaration, module, source, and report')
    if formal['verification_report']:
        report_path = (repository_dir / formal['verification_report']).resolve()
        if not report_path.is_relative_to((repository_dir / 'formal/checks').resolve()):
            raise ContentError('Verification report must be inside formal/checks')
        if check_reports and formal['status'] == 'complete':
            report = read_json(report_path)
            if report.get('build') != 'passed' or formal['declaration'] not in {
                    item['name'] for item in report['declarations']}:
                raise ContentError(f"Declaration missing from a passing report: {formal['declaration']}")
            if formal['module'].startswith('Mathlib.'):
                report_source = 'formal/.lake/packages/mathlib/' + formal['source']
                if report_source not in report.get('sha256', {}):
                    raise ContentError(f"Mathlib source missing from the verification report: {formal['source']}")
    if not isinstance(block['references'], list):
        raise ContentError('references must be a list')
    for reference in block['references']:
        fields(reference, {'entry_id', 'block_id'})
        if not all(isinstance(value, str) and value for value in reference.values()):
            raise ContentError('References require entry and block IDs')


def entry_formalization(blocks):
    statuses = [block['formalization']['status'] for block in blocks]
    complete = statuses.count('complete')
    status = ('complete' if complete == len(statuses) else
              'not_started' if all(value == 'not_started' for value in statuses) else 'partial')
    return {'status': status, 'complete': complete, 'total': len(statuses),
            'label': {'complete': 'Formalization complete', 'partial': 'Partially formalized',
                      'not_started': 'Not formalized'}[status]}
