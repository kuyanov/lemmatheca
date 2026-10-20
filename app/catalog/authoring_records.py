"""Small navigation catalogs for source reviews and future-reference plans.

Catalogs contain identifiers and lookup keys only. Exact lookups open one JSON
record; filtered listings intersect catalog keys before reading candidate prose.
They are independent of the Lean-derived corpus index.
"""

from collections import defaultdict
import re
from urllib.parse import urldefrag, urlsplit

from .files import read_json, write_json


class AuthoringRecordError(ValueError):
    def __init__(self, message, *, status=503, code="authoring_records_unavailable"):
        super().__init__(message)
        self.status, self.code = status, code


def identifier(value):
    if not isinstance(value, str) or not re.fullmatch(r"[A-Za-z0-9][A-Za-z0-9_-]*", value):
        raise ValueError("Expected a corpus identifier.")
    return value


def normalized_url(value):
    if not isinstance(value, str) or not value.strip() or any(c.isspace() for c in value):
        raise ValueError("url must be an absolute HTTP or HTTPS URL.")
    parsed = urlsplit(value)
    if parsed.scheme not in {"http", "https"} or not parsed.netloc:
        raise ValueError("url must be an absolute HTTP or HTTPS URL.")
    return urldefrag(value)[0]


def _strings(record, key):
    values = record.get(key)
    if (not isinstance(values, list) or any(not isinstance(item, str) or not item.strip()
                                           for item in values) or len(values) != len(set(values))):
        raise ValueError(f"{record.get('id', 'Record')}: {key} must be an array of nonempty strings.")
    return values


def _entry_ids(record):
    return {identifier(ref.split("#", 1)[0]) for ref in _strings(record, "entry_refs")}


def _check_record(record, expected, kind):
    if not isinstance(record, dict) or record.get("id") != identifier(expected):
        raise ValueError(f"Invalid {kind} record: {expected}.")
    _entry_ids(record)
    if kind == "sources":
        if not isinstance(record.get("publication"), str) or not record["publication"].strip():
            raise ValueError(f"{expected}: publication must be nonempty text.")
        _strings(record, "finding_ids")
        reviews = record.get("reviews")
        if (not isinstance(reviews, list) or not reviews
                or any(not isinstance(review, dict) or any(
                    not isinstance(review.get(field), str) or not review[field].strip()
                    for field in ("checked_passages", "consumers", "outcome", "checked_on"))
                       for review in reviews)):
            raise ValueError(f"{expected}: reviews must contain scoped review records.")
    elif kind == "findings":
        if record.get("severity") not in {"serious", "local"}:
            raise ValueError(f"{expected}: invalid finding severity.")
        for field in ("source_ids", "related_findings"):
            for item in _strings(record, field):
                identifier(item)
        if not record["source_ids"] or not isinstance(record.get("details"), str) or not record["details"].strip():
            raise ValueError(f"{expected}: finding must identify sources and explain the defect.")
    else:
        identifier(record.get("kind"))
        for item in _strings(record, "areas"):
            identifier(item)
        if "planned_entry_ids" in record:
            for item in _strings(record, "planned_entry_ids"):
                identifier(item)
    if kind != "findings":
        for url in _strings(record, "urls"):
            normalized_url(url)
    if kind != "sources" and (not isinstance(record.get("title"), str) or not record["title"].strip()):
        raise ValueError(f"{expected}: title must be nonempty text.")
    return record


def _mapping(pairs):
    result = defaultdict(set)
    for key, value in pairs:
        result[key].add(value)
    return {key: sorted(values) for key, values in sorted(result.items())}


def _text(value):
    if isinstance(value, str):
        return value
    if isinstance(value, dict):
        return " ".join(_text(item) for item in value.values())
    return " ".join(_text(item) for item in value) if isinstance(value, list) else ""


def source_catalog(sources, findings):
    for kind, records in (("sources", sources), ("findings", findings)):
        for key, record in records.items():
            _check_record(record, key, kind)
    owned = {key: set() for key in sources}
    for finding in findings.values():
        if any(key not in sources for key in finding["source_ids"]):
            raise ValueError(f"{finding['id']}: unknown source.")
        for source in finding["source_ids"]:
            owned[source].add(finding["id"])
        if any(key not in findings for key in finding["related_findings"]):
            raise ValueError(f"{finding['id']}: unknown related finding.")
    for source in sources.values():
        expected = sorted(owned[source["id"]])
        if sorted(source["finding_ids"]) != expected:
            raise ValueError(f"{source['id']}: finding_ids do not match the finding records.")
    entries = [(entry, key) for key, source in sources.items() for entry in _entry_ids(source)]
    entries += [(entry, source) for finding in findings.values()
                for entry in _entry_ids(finding) for source in finding["source_ids"]]
    return {"schema_version": 1, "sources": sorted(sources),
            "findings": {key: sorted(record["source_ids"]) for key, record in sorted(findings.items())},
            "by_entry": _mapping(entries),
            "by_url": _mapping((normalized_url(url), key)
                               for key, source in sources.items() for url in source["urls"])}


def planning_catalog(records):
    for key, record in records.items():
        _check_record(record, key, "records")
    return {"schema_version": 1, "records": sorted(records),
            "by_entry": _mapping((entry, key) for key, record in records.items()
                                 for entry in _entry_ids(record) | {
                                     identifier(item) for item in record.get("planned_entry_ids", [])}),
            "by_area": _mapping((area, key) for key, record in records.items() for area in record["areas"]),
            "by_kind": _mapping((record["kind"], key) for key, record in records.items()),
            "by_url": _mapping((normalized_url(url), key)
                               for key, record in records.items() for url in record["urls"])}


def _records(directory, kind):
    if not directory.is_dir():
        raise ValueError(f"Missing authoring-record directory: {directory}.")
    return {path.stem: _check_record(read_json(path), path.stem, kind)
            for path in sorted(directory.glob("*.json"))}


def build_source_index(corpus):
    directory = corpus / "source-errors"
    return source_catalog(_records(directory / "sources", "sources"),
                          _records(directory / "findings", "findings"))


def build_planning_index(corpus):
    return planning_catalog(_records(corpus / "reference-planning" / "records", "records"))


def write_authoring_indexes(corpus):
    # Compute both before replacing either catalog; each replacement is atomic.
    sources, planning = build_source_index(corpus), build_planning_index(corpus)
    for directory, catalog in (("source-errors", sources), ("reference-planning", planning)):
        path = corpus / directory / "index.json"
        try:
            existing = read_json(path)
        except (FileNotFoundError, ValueError):
            existing = None
        if existing != catalog:
            write_json(path, catalog)
    return sources, planning


class AuthoringRecords:
    def __init__(self, corpus):
        self.corpus = corpus

    def record(self, kind, key, *, required=False):
        identifier(key)
        directory = "reference-planning" if kind == "records" else "source-errors"
        try:
            return _check_record(read_json(self.corpus / directory / kind / f"{key}.json"), key, kind)
        except FileNotFoundError as error:
            if not required:
                raise AuthoringRecordError(f"Unknown {kind} record: {key}.", status=404,
                                           code="not_found") from error
            raise AuthoringRecordError(f"Missing indexed {kind} record: {key}.") from error
        except (OSError, ValueError, TypeError) as error:
            raise AuthoringRecordError(f"Invalid {kind} record: {key}.") from error

    def catalog(self, planning=False):
        directory = "reference-planning" if planning else "source-errors"
        try:
            catalog = read_json(self.corpus / directory / "index.json")
            ids = catalog["records" if planning else "sources"]
            if (type(catalog["schema_version"]) is not int or catalog["schema_version"] != 1
                    or not isinstance(ids, list) or len(ids) != len(set(ids))):
                raise ValueError("Invalid schema or identifiers.")
            for key in ids:
                identifier(key)
            maps = ["by_entry", "by_url", "by_area", "by_kind"] if planning else ["by_entry", "by_url", "findings"]
            for field in maps:
                mapping = catalog[field]
                if not isinstance(mapping, dict):
                    raise ValueError("Invalid navigation map.")
                for key, values in mapping.items():
                    if not key or not isinstance(values, list) or len(values) != len(set(values)) or any(item not in ids for item in values):
                        raise ValueError("Invalid navigation targets.")
                    if field == "findings":
                        identifier(key)
            return catalog
        except (OSError, ValueError, TypeError, KeyError) as error:
            raise AuthoringRecordError(f"Invalid or missing {directory} catalog; run build --no-lean.") from error

    def listing(self, kind, filters, *, limit=20, offset=0):
        catalog = self.catalog(planning=kind == "records")
        candidates = set(catalog["records" if kind == "records" else "sources"])
        for param, index in (("entry_id", "by_entry"), ("url", "by_url"), ("area", "by_area"), ("kind", "by_kind")):
            if param in filters:
                value = normalized_url(filters[param]) if param == "url" else identifier(filters[param])
                candidates.intersection_update(catalog[index].get(value, []))
        if kind == "findings":
            candidates = {key for key, sources in catalog["findings"].items()
                          if set(sources).intersection(candidates)}
            if "source_id" in filters:
                source = identifier(filters["source_id"])
                candidates = {key for key in candidates if source in catalog["findings"][key]}
        keys, loaded = sorted(candidates), {}
        if "q" in filters or (kind == "findings" and ("severity" in filters or "entry_id" in filters)):
            terms = filters.get("q", "").casefold().split()
            selected = []
            for key in keys:
                record = loaded[key] = self.record(kind, key, required=True)
                haystack = (record["publication"] if kind == "sources" else
                            _text(record)).casefold()
                if (all(term in haystack for term in terms)
                        and ("severity" not in filters or record["severity"] == filters["severity"])
                        and (kind != "findings" or "entry_id" not in filters
                             or filters["entry_id"] in _entry_ids(record))):
                    selected.append(key)
            keys = selected
        fields = {"sources": ("id", "publication"), "findings": ("id", "title", "severity", "source_ids"),
                  "records": ("id", "title", "kind", "areas", "entry_refs")}[kind]
        results = []
        for key in keys[offset:offset + limit]:
            record = loaded.get(key) or self.record(kind, key, required=True)
            results.append({field: record[field] for field in fields})
        return {"count": len(keys), "limit": limit, "offset": offset, "results": results}
