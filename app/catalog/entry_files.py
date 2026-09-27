"""Read entry metadata, HTML, navigation files, and validate local asset paths."""

from .files import read_json, records


def read_entries(corpus):
    entries = records(corpus, "entry")
    for entry in entries.values():
        directory = corpus / "entries" / entry["id"]
        entry["directory"] = directory
        entry["source"] = (
            directory / "entry.html").read_text(encoding="utf-8")
    return entries


def read_areas(corpus):
    return {area["id"]: area for area in read_json(corpus / "taxonomy.json")["areas"]}


def read_reading_order(corpus):
    return read_json(corpus / "reading-order.json")["areas"]


def is_local_asset(directory, source):
    path = (directory / source).resolve()
    return path.is_relative_to((directory / "assets").resolve()) and path.is_file()
