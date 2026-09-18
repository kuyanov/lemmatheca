"""Read-only Lean source paths and links, independent of corpus membership."""

from pathlib import PurePosixPath
from urllib.parse import urlencode

from django.urls import reverse

from .sources import ContentError


class MissingLeanSource(ContentError):
    """A valid source path whose file is not installed locally."""


def lean_source_path(source, repository_dir, *, require_file=True):
    parts = source.split('/')
    if (len(parts) < 2 or any(not part or part.startswith('.') for part in parts)
            or '\\' in source or '\x00' in source or PurePosixPath(source).suffix != '.lean'):
        raise ContentError('Invalid Lean source path')
    if parts[0] == 'formal':
        root = repository_dir / 'formal'
    elif parts[0] == 'Mathlib':
        root = repository_dir / 'formal/.lake/packages/mathlib/Mathlib'
    else:
        raise ContentError('Use a formal/ or Mathlib/ source path')
    path = root.joinpath(*parts[1:])
    if not path.resolve().is_relative_to(root.resolve()):
        raise ContentError(f'Lean source is outside its source tree: {source}')
    if path.exists() and not path.is_file():
        raise ContentError(f'Lean source is not a file: {source}')
    if require_file and not path.is_file():
        raise MissingLeanSource(f'Missing Lean source: {path}')
    return path


def lean_source_url(binding, *, entry_id=None, block_id=None):
    if not binding['source']:
        return None
    url = reverse('catalog:lean_file', args=[binding['source']])
    if entry_id and block_id:
        context = {'from': entry_id, 'at': block_id}
        if binding['declaration']:
            context['declaration'] = binding['declaration']
        url += '?' + urlencode(context)
    return url
