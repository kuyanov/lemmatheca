"""Strict JSON loading shared by the human and formal catalogs."""

import json

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
