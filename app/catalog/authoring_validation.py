"""Offline checks for the source register and outstanding development records."""

import re
from urllib.parse import urlsplit

from .validation import checking, fields, identifier, identifiers, json_object, require, text


def _references(values, blocks):
    require(isinstance(values, list), "entry_refs must be a list")
    seen = set()
    for value in values:
        text(value, "Entry reference")
        require(value not in seen, f"Duplicate entry reference: {value}")
        seen.add(value)
        entry, separator, anchor = value.partition("#")
        require(entry in blocks, f"Unknown referenced entry: {entry}")
        if separator:
            require(anchor in blocks[entry], f"Unknown referenced block: {value}")


def _urls(values):
    require(isinstance(values, list), "urls must be a list")
    for value in values:
        text(value, "URL")
        url = urlsplit(value)
        require(url.scheme in {"http", "https"} and bool(url.netloc),
                f"Invalid publication URL: {value}")
    require(len(values) == len(set(values)), "Duplicate URLs")


def _records(directory):
    require(directory.is_dir(), f"Missing record directory: {directory}")
    records = {}
    for path in sorted(directory.glob("*.json")):
        with checking(path):
            record = json_object(path)
            identifier(record.get("id"))
            require(record["id"] == path.stem, "Record ID must match its filename")
            records[record["id"]] = record
    return records


def _links(value, corpus, blocks, entry_refs=None):
    """Record prose uses corpus-root-relative links, regardless of file depth."""
    if isinstance(value, dict):
        for item in value.values():
            _links(item, corpus, blocks, entry_refs)
    elif isinstance(value, list):
        for item in value:
            _links(item, corpus, blocks, entry_refs)
    elif isinstance(value, str):
        for href in re.findall(r"\[[^\]]*\]\(([^\s()]+)\)", value):
            target = urlsplit(href)
            if target.scheme or target.netloc:
                continue
            path = corpus / target.path
            require(bool(target.path) and path.is_file(), f"Missing record link: {href}")
            if target.path.startswith("entries/"):
                entry = target.path.split("/")[1]
                reference = entry + (f"#{target.fragment}" if target.fragment else "")
                _references([reference], blocks)
                if entry_refs is not None:
                    require(reference in entry_refs, f"entry_refs does not index link: {reference}")


def validate_authoring_records(corpus, blocks):
    """Read each record once; catalogs must describe exactly those records.

    Small test corpora and core-only installations may omit these registries.
    Once a registry directory exists, all of its records and navigation are checked.
    These independent catalogs are not inputs to the entry/node derived index.
    """
    from .authoring_records import source_catalog, planning_catalog

    source_root = corpus / "source-errors"
    if source_root.exists():
        sources = _records(source_root / "sources")
        findings = _records(source_root / "findings")
        for source_id, source in sources.items():
            with checking(source_root / "sources" / f"{source_id}.json"):
                fields(source, ("id", "publication", "urls", "reviews", "entry_refs", "finding_ids"))
                text(source["publication"], "Publication and inspected version")
                _urls(source["urls"])
                _references(source["entry_refs"], blocks)
                _links(source, corpus, blocks, source["entry_refs"])
                identifiers(source["finding_ids"], "finding_ids")
                require(isinstance(source["reviews"], list) and bool(source["reviews"]),
                        "A source must have at least one scoped review")
                for review in source["reviews"]:
                    fields(review, ("checked_passages", "consumers", "outcome", "checked_on"))
                    for key, value in review.items():
                        text(value, key)
                for finding_id in source["finding_ids"]:
                    require(finding_id in findings, f"Unknown finding: {finding_id}")
        for finding_id, finding in findings.items():
            with checking(source_root / "findings" / f"{finding_id}.json"):
                fields(finding, ("id", "source_ids", "severity", "title", "details", "entry_refs", "related_findings"))
                identifiers(finding["source_ids"], "source_ids")
                require(bool(finding["source_ids"]), "A finding must identify its source")
                require(finding["severity"] in ("serious", "local"), "Invalid finding severity")
                text(finding["title"], "Finding title")
                text(finding["details"], "Finding evidence and repair")
                _references(finding["entry_refs"], blocks)
                _links(finding, corpus, blocks, finding["entry_refs"])
                identifiers(finding["related_findings"], "related_findings")
                for related in finding["related_findings"]:
                    require(related in findings, f"Unknown related finding: {related}")
                for source_id in finding["source_ids"]:
                    require(source_id in sources, f"Unknown source: {source_id}")
                    require(finding_id in sources[source_id]["finding_ids"],
                            f"Source {source_id} does not list {finding_id}")
        for source_id, source in sources.items():
            with checking(source_root / "sources" / f"{source_id}.json"):
                for finding_id in source["finding_ids"]:
                    require(source_id in findings[finding_id]["source_ids"],
                            f"Finding {finding_id} does not belong to {source_id}")
        path = source_root / "index.json"
        with checking(path):
            require(json_object(path) == source_catalog(sources, findings),
                    "Source catalog is stale; run index_authoring_records")
        with checking(source_root / "policy.json"):
            _links(json_object(source_root / "policy.json"), corpus, blocks)

    plan_root = corpus / "reference-planning"
    if plan_root.exists():
        records = _records(plan_root / "records")
        for record_id, record in records.items():
            with checking(plan_root / "records" / f"{record_id}.json"):
                for key in ("kind", "title", "areas", "entry_refs", "urls"):
                    require(key in record, f"Missing field: {key}")
                identifier(record["kind"], "kind")
                text(record["title"], "Planning title")
                identifiers(record["areas"], "areas")
                _references(record["entry_refs"], blocks)
                _links(record, corpus, blocks, record["entry_refs"])
                _urls(record["urls"])
                if "planned_entry_ids" in record:
                    identifiers(record["planned_entry_ids"], "planned_entry_ids")
        path = plan_root / "index.json"
        with checking(path):
            require(json_object(path) == planning_catalog(records),
                    "Planning catalog is stale; run index_authoring_records")
        with checking(plan_root / "policy.json"):
            _links(json_object(plan_root / "policy.json"), corpus, blocks)
