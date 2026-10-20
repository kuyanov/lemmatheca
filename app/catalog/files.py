"""Shared corpus JSON reads and atomic replacement of records and catalogs."""

import json
from pathlib import Path
import re
from tempfile import NamedTemporaryFile


def read_json(path):
    return json.loads(path.read_text(encoding="utf-8"))


def read_record(path, identifier):
    # IDs may come from URLs, including the contextual back-link query string.
    if not isinstance(identifier, str) or not re.fullmatch(r"[A-Za-z0-9][A-Za-z0-9_-]*", identifier):
        raise FileNotFoundError(f"Invalid corpus ID: {identifier}")
    return read_json(path)


def write_json(path, record):
    with NamedTemporaryFile(mode="w", encoding="utf-8", dir=path.parent, delete=False) as file:
        temporary = Path(file.name)
        try:
            json.dump(record, file, indent=2, ensure_ascii=False)
            file.write("\n")
        except BaseException:
            temporary.unlink(missing_ok=True)
            raise
    try:
        temporary.replace(path)
    finally:
        temporary.unlink(missing_ok=True)
