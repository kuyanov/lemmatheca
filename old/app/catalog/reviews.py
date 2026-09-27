"""Content-bound editorial approval, independent of Lean verification."""

import hashlib

from .files import file_signature, read_json
from .sources import ContentError
from formalization.reviews import digest


def entry_review_hash(metadata, source, directory, descriptions):
    """Hash entry content and its linked human statements, independently of Lean."""
    assets = {}
    for path in sorted((directory / 'assets').rglob('*')):
        if path.is_file():
            if not path.resolve().is_relative_to(directory.resolve()):
                raise ContentError('Entry review asset is outside the entry directory')
            assets[path.relative_to(directory).as_posix()] = hashlib.sha256(path.read_bytes()).hexdigest()
    return digest({
        'version': 2,
        'metadata': {key: value for key, value in metadata.items() if key != 'review'},
        'source_sha256': hashlib.sha256(source).hexdigest(),
        'assets': assets,
        'node_descriptions': descriptions,
    })


def descriptions_match(node_directory, descriptions):
    """Guard approval against changed linked descriptions, ignoring other node fields."""
    for node_id, expected in descriptions.items():
        try:
            node = read_json(node_directory / f'{node_id}.json')
        except (ValueError, OSError):
            return False
        if not isinstance(node, dict) or node.get('description') != expected:
            return False
    return True


def entry_review_signature(directory):
    """Detect edits to the entry and its assets during approval."""
    paths = [directory / 'entry.json', directory / 'entry.html']
    paths.extend(path for path in (directory / 'assets').rglob('*') if path.is_file())
    return tuple(file_signature(path) for path in sorted(paths))
