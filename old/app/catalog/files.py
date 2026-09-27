"""JSON files and change detection shared by the human and formal catalogs."""

from contextlib import contextmanager
import json
from pathlib import Path
import tempfile

from .sources import ContentError


def file_signature(path):
    """A cache key that also detects replacement or removal of a file."""
    try:
        stat = path.stat()
    except FileNotFoundError:
        return (str(path), None)
    return (str(path), stat.st_mtime_ns, stat.st_ctime_ns, stat.st_size)


def read_json(path):
    def unique_object(pairs):
        result = {}
        for key, value in pairs:
            if key in result:
                raise ContentError(f"{path}: duplicate JSON key {key}")
            result[key] = value
        return result
    return json.loads(path.read_text(), object_pairs_hook=unique_object)


@contextmanager
def staged_json(path, value):
    """Stage beside the destination for atomic replacement, cleaning up on failure."""
    temporary_path = None
    try:
        with tempfile.NamedTemporaryFile('w', dir=path.parent, prefix=f'.{path.stem}.',
                                         suffix='.tmp', delete=False) as temporary:
            temporary_path = Path(temporary.name)
            json.dump(value, temporary, indent=2)
            temporary.write('\n')
        yield temporary_path
    finally:
        if temporary_path is not None:
            temporary_path.unlink(missing_ok=True)
