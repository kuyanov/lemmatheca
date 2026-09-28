"""The corpus JSON files are the application's only persistent storage."""

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


def records(corpus, kind):
    pattern = "nodes/*.json" if kind == "node" else "entries/*/entry.json"
    result = {}
    for path in sorted(corpus.glob(pattern)):
        expected = path.stem if kind == "node" else path.parent.name
        result[expected] = read_record(path, expected)
    return result
