"""Read entry metadata, HTML, navigation files, and validate local asset paths."""

from django.conf import settings

from .files import read_json, read_record


def read_entry_metadata(identifier, corpus=None):
    corpus = corpus or settings.CORPUS_DIR
    return read_record(corpus / "entries" / str(identifier) / "entry.json", identifier)


def read_entry(identifier, corpus=None):
    corpus = corpus or settings.CORPUS_DIR
    entry = read_entry_metadata(identifier, corpus)
    directory = corpus / "entries" / identifier
    return {**entry, "directory": directory,
            "source": (directory / "entry.html").read_text(encoding="utf-8")}


def read_areas(corpus=None):
    corpus = corpus or settings.CORPUS_DIR
    return {area["id"]: area for area in read_json(corpus / "taxonomy.json")["areas"]}


def read_area_entries(corpus=None):
    corpus = corpus or settings.CORPUS_DIR
    return read_json(corpus / "area_entries.json")["areas"]


def is_local_asset(directory, source):
    path = (directory / source).resolve()
    return path.is_relative_to((directory / "assets").resolve()) and path.is_file()
