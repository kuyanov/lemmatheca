"""Offline corpus checks: one record/tree at a time, compact reference indexes only."""

from contextlib import contextmanager
from datetime import datetime, timedelta
import json
from pathlib import PurePosixPath
import re
from urllib.parse import urlsplit

from .axioms import check_axiom_dependencies, check_axioms
from .entry_files import is_local_asset
from .equations import EQREF, LABEL
from .node_files import LEAN_MODULE, source_path
from .sources import Element, KINDS, SourceParser
from .statistics import COUNTS, METRICS

ID = re.compile(r"[A-Za-z0-9][A-Za-z0-9_-]*\Z")
ANCHOR = re.compile(r"[A-Za-z0-9][A-Za-z0-9_.:-]*\Z")
MAX_HTML_DEPTH = 128


class CorpusError(ValueError):
    pass


def require(condition, message):
    if not condition:
        raise CorpusError(message)


@contextmanager
def checking(path):
    try:
        yield
    except (OSError, ValueError) as error:
        raise CorpusError(f"{path}: {error}") from error


def json_object(path):
    def pairs(items):
        result = {}
        for key, value in items:
            require(key not in result, f"Duplicate JSON key: {key}")
            result[key] = value
        return result

    def constant(value):
        raise CorpusError(f"Invalid JSON constant: {value}")

    with path.open(encoding="utf-8") as stream:
        result = json.load(stream, object_pairs_hook=pairs,
                           parse_constant=constant)
    require(isinstance(result, dict), "Expected a JSON object")
    return result


def fields(record, required, optional=()):
    require(isinstance(record, dict), "Expected an object")
    require(not (set(required) - record.keys()),
            f"Missing fields: {', '.join(set(required) - record.keys())}")
    require(not (record.keys() - set(required) - set(optional)),
            f"Unknown fields: {', '.join(record.keys() - set(required) - set(optional))}")


def text(value, field):
    require(isinstance(value, str) and bool(value.strip()),
            f"{field} must be a nonempty string")
    # JSON permits escaped lone surrogates; an HTTP response cannot encode them.
    value.encode("utf-8")


def identifier(value, field="id"):
    require(isinstance(value, str) and ID.fullmatch(
        value), f"Invalid {field}: {value!r}")


def identifiers(value, field):
    require(isinstance(value, list), f"{field} must be a list")
    seen = set()
    for item in value:
        identifier(item, field)
        require(item not in seen, f"Duplicate {field}: {item}")
        seen.add(item)
    return seen


def acyclic(graph, name):
    """Iterative DFS: each vertex and edge is visited once, including long chains."""
    done, active = set(), set()
    for start in graph:
        if start in done:
            continue
        active.add(start)
        stack = [(start, iter(graph[start]))]
        while stack:
            current, edges = stack[-1]
            target = next(edges, None)
            if target is None:
                active.remove(current)
                done.add(current)
                stack.pop()
            else:
                require(target in graph,
                        f"{name}: {current} references missing {target}")
                require(target not in active,
                        f"{name}: cycle through {current} -> {target}")
                if target not in done:
                    active.add(target)
                    stack.append((target, iter(graph[target])))


class CheckedParser(SourceParser):
    def handle_starttag(self, tag, attrs):
        require(len(dict(attrs)) == len(attrs),
                f"Duplicate attributes on <{tag}>")
        require(len(self.stack) <= MAX_HTML_DEPTH,
                "HTML nesting is too deep for the reader")
        super().handle_starttag(tag, attrs)

    def handle_endtag(self, tag):
        require(len(self.stack) > 1 and self.stack[-1].tag == tag,
                f"Unbalanced closing tag </{tag}>")
        super().handle_endtag(tag)

    def handle_decl(self, decl):
        raise CorpusError(
            "Use an HTML fragment, without a document declaration")

    def handle_pi(self, data):
        raise CorpusError("Processing instructions are not entry content")


def checked_source(source):
    """Check structure and local references without rendering or opening other entries.

    Return the tree plus only the block IDs, cross-entry links and node IDs needed
    by the corpus pass. The build also uses this check before publishing summaries.
    """
    parser = CheckedParser()
    parser.feed(source)
    parser.close()
    require(len(parser.stack) == 1, f"Unclosed <{parser.stack[-1].tag}>")
    root = parser.root
    blocks, formal_ids = set(), set()
    for node in root.children:
        if isinstance(node, str) and not node.strip():
            continue
        require(isinstance(node, Element) and node.tag == "section",
                "Entry content must be inside top-level <section> blocks")
        block_id = node.attrs.get("id")
        require(isinstance(block_id, str) and ANCHOR.fullmatch(
            block_id), "Each section needs an id")
        require(node.attrs.get("data-kind") in KINDS,
                f"{block_id}: unsupported data-kind")
        headings = [child for child in node.children if isinstance(
            child, Element) and child.tag == "h2"]
        require(len(headings) == 1 and headings[0].text().strip(),
                f"{block_id}: expected one nonempty <h2> title")
        # The reader replaces this title with plain text and its own anchor.
        require(not headings[0].attrs and not any(isinstance(child, Element) for child in headings[0].children),
                f"{block_id}: h2 must contain plain text, without attributes")
        if "data-formal" in node.attrs:
            value = node.attrs["data-formal"]
            require(isinstance(value, str),
                    'Use data-formal="" for an empty mapping')
            formal_ids.update(identifiers(
                value.split(), f"{block_id} formal node ID"))
        blocks.add(block_id)
    require(blocks, "An entry must contain at least one block")

    anchors, labels, eqrefs, local, references, assets = set(), set(), set(), [
    ], [], set()
    stack = [(root, False)]
    while stack:
        node, skip_math = stack.pop()
        skip_math = skip_math or node.tag in {"pre", "code", "script", "style"}
        attrs = node.attrs
        for key in ("id", "class", "href", "src", "data-kind", "data-formal"):
            if key in attrs:
                require(isinstance(attrs[key], str),
                        f"<{node.tag}>: {key} needs a value")
        if "id" in attrs:
            anchor = attrs["id"]
            require(ANCHOR.fullmatch(anchor) and anchor not in anchors,
                    f"Invalid or duplicate anchor: {anchor}")
            anchors.add(anchor)
        if node.tag in {"figure", "table"}:
            caption = "figcaption" if node.tag == "figure" else "caption"
            require(sum(isinstance(child, Element) and child.tag == caption for child in node.children) == 1,
                    f"Each {node.tag} needs one direct {caption}")
        if node.tag == "img":
            text(attrs.get("alt"), "Image alt")
            text(attrs.get("src"), "Image src")
            assets.add(attrs["src"])
        if node.tag == "a":
            href = attrs.get("href")
            text(href, "Link href")
            link = urlsplit(href)
            if href.startswith("assets/"):
                assets.add(href)
            elif not link.scheme and not link.netloc:
                require(not link.query and link.fragment,
                        f"Broken source link: {href}")
                if link.path:
                    identifier(link.path, "entry reference")
                    references.append((link.path, link.fragment))
                else:
                    local.append(link.fragment)
        labelled = False
        if node.tag in {"div", "p"} and "math-display" in attrs.get("class", "").split():
            value = node.text()
            found = LABEL.findall(value)
            if found:
                require(len(found) == 1 and re.fullmatch(r"\s*\\\[.*?\\\]\s*", value, re.DOTALL)
                        and not any(isinstance(child, Element) for child in node.children),
                        "Use one equation label in one plain display-math element")
                label = found[0]
                require(label not in labels and (not attrs.get("id") or attrs["id"] == label),
                        f"Duplicate or conflicting equation label: {label}")
                require(r"\tag" not in value,
                        "Labelled equations are numbered automatically; omit \\tag")
                labels.add(label)
                if not attrs.get("id"):
                    require(label not in anchors, f"Duplicate anchor: {label}")
                    anchors.add(label)
                labelled = True
        for child in reversed(node.children):
            if isinstance(child, Element):
                stack.append((child, skip_math))
            elif not skip_math:
                require(labelled or r"\label{" not in child,
                        "Equation labels belong inside a math-display element")
                eqrefs.update(EQREF.findall(child))
    require(not eqrefs - labels,
            f"Unknown equation references: {', '.join(eqrefs - labels)}")
    require(not set(local) - anchors,
            f"Broken local links: {', '.join(set(local) - anchors)}")
    require(not {f"{block}-title" for block in blocks}
            & anchors, "Reserved block heading anchor")
    return root, blocks, references, formal_ids, assets


def check_asset(directory, source):
    path = PurePosixPath(source)
    require(source.startswith("assets/") and ".." not in path.parts and "\\" not in source,
            f"Assets must use entry-local assets/ paths: {source}")
    require(is_local_asset(directory, source),
            f"Missing or escaped asset: {source}")


def entry_metadata(record, expected, areas):
    fields(record, ("id", "title", "based_on", "primary_area", "additional_areas",
                    "reading_time", "summary", "abstract"), ("formalization",))
    require(record["id"] == expected, "ID does not match directory")
    for key in ("title", "summary", "abstract"):
        text(record[key], key)
    identifier(record["primary_area"], "primary_area")
    additional = identifiers(record["additional_areas"], "additional_areas")
    require(record["primary_area"] not in additional,
            "Primary area is also in additional_areas")
    require({record["primary_area"]} | additional <=
            areas, "Unknown entry area")
    require(type(record["reading_time"]) is int and record["reading_time"] > 0,
            "reading_time must be a positive integer")
    require(isinstance(record["based_on"], list), "based_on must be a list")
    for citation in record["based_on"]:
        fields(citation, ("authors", "title"), ("year", "venue",
               "volume", "issue", "pages", "doi", "url"))
        text(citation["title"], "Citation title")
        require(isinstance(citation["authors"], list) and citation["authors"],
                "Citation authors must be a nonempty list")
        for author in citation["authors"]:
            text(author, "Citation author")
        for key in ("venue", "pages", "doi", "url"):
            if key in citation:
                text(citation[key], f"Citation {key}")
        for key in ("year", "volume", "issue"):
            if key in citation:
                require(type(citation[key]) is int or isinstance(
                    citation[key], str), f"Invalid citation {key}")
                if isinstance(citation[key], str):
                    text(citation[key], f"Citation {key}")
        if "url" in citation:
            url = urlsplit(citation["url"])
            require(url.scheme in {"http", "https"}
                    and url.netloc, "Citation url must be HTTP(S)")
        if "doi" in citation:
            require(citation["doi"].startswith("10.")
                    and "/" in citation["doi"], "Use a bare DOI")
    if "formalization" in record:
        summary = record["formalization"]
        fields(summary, ("status", "complete", "total",
               "unplanned", "label", "description"), ("percent",))
        require(isinstance(summary["status"], str) and summary["status"] in
                {"not_started", "not_applicable", "partial", "complete"}, "Invalid formalization status")
        for key in ("complete", "total", "unplanned", "percent"):
            if key in summary:
                require(type(summary[key]) is int and summary[key]
                        >= 0, f"Invalid formalization {key}")
        require(summary["complete"] <= summary["total"],
                "Verified count exceeds total")
        require(summary.get("percent", 0) <= 100,
                "Invalid formalization percent")
        text(summary["label"], "formalization label")
        text(summary["description"], "formalization description")


def node_metadata(record, expected):
    fields(record, ("id", "description", "axioms", "verified"),
           ("module", "declaration", "dependencies", "signature", "declaration_line"))
    require(record["id"] == expected, "ID does not match filename")
    text(record["description"], "description")
    check_axioms(record["axioms"])
    require(type(record["verified"]) is bool, "verified must be a boolean")
    dependencies = record.get("dependencies", [])
    identifiers(dependencies, "dependency")
    module, declaration = record.get("module"), record.get("declaration")
    require((module is None) == (declaration is None),
            "module and declaration must be supplied together")
    if module is not None:
        require(isinstance(module, str) and LEAN_MODULE.fullmatch(
            module), "Invalid Lean module")
        text(declaration, "declaration")
    else:
        require(not record["verified"], "An unbound node cannot be verified")
    if "signature" in record:
        text(record["signature"], "signature")
    if "declaration_line" in record:
        require(type(record["declaration_line"]) is int and record["declaration_line"] > 0,
                "declaration_line must be a positive integer")
    return dependencies


def validate_statistics(snapshot):
    fields(snapshot, ("entries", "verified_entries", "nodes", "verified_nodes", "contributors"),
           ("areas", "history"))
    for key in COUNTS:
        if key not in snapshot or (key == "contributors" and snapshot[key] is None):
            continue
        require(type(snapshot[key]) is int and snapshot[key] >= 0,
                f"{key} must be a nonnegative integer")
    for kind in ("entries", "nodes"):
        require(snapshot[f"verified_{kind}"] <=
                snapshot[kind], f"Verified {kind} exceed the total")
    if "history" not in snapshot:
        return
    history = snapshot["history"]
    fields(history, METRICS)
    for key, points in history.items():
        require(isinstance(points, list), f"History for {key} must be a list")
        counts = ("count", "verified") if key in (
            "entries", "nodes") else ("count",)
        previous, previous_at = None, None
        for point in points:
            fields(point, ("at", *counts))
            text(point["at"], "History timestamp")
            at = datetime.fromisoformat(point["at"])
            require(at.utcoffset() == timedelta(0),
                    "History timestamps must use UTC")
            for field in counts:
                require(type(point[field]) is int and point[field] >= 0,
                        "History counts must be nonnegative integers")
            if "verified" in counts:
                require(point["verified"] <= point["count"],
                        f"Historical verified {key} exceed the total")
            if previous is not None:
                require(at >= previous_at,
                        "History timestamps must be chronological")
                require(any(point[field] != previous[field] for field in counts),
                        "History must record changes only")
            previous, previous_at = point, at
        if points:
            require(points[-1]["count"] == snapshot.get(key),
                    f"History for {key} must end at the current count")
            if "verified" in counts:
                require(points[-1]["verified"] == snapshot[f"verified_{key}"],
                        f"History for {key} must end at the current verified count")


def validate_corpus(corpus, *, source_root=None):
    """O(input bytes + reference edges) time; never retain whole entry/node records.

    Indexes contain area parents, entry block IDs, cross-entry links and node hint
    edges. Generated proof data need not be present or current. Optional source
    checks use the installed files only; neither mode invokes Lean or the build.
    """
    statistics = corpus / "statistics.json"
    if statistics.exists():
        with checking(statistics):
            validate_statistics(json_object(statistics))
    taxonomy = corpus / "taxonomy.json"
    with checking(taxonomy):
        document = json_object(taxonomy)
        fields(document, ("areas",))
        require(isinstance(document["areas"], list), "areas must be a list")
        areas = {}
        for area in document["areas"]:
            fields(area, ("id", "title", "parent", "description"))
            identifier(area["id"])
            require(area["id"] not in areas, f"Duplicate area: {area['id']}")
            text(area["title"], "Area title")
            text(area["description"], "Area description")
            if area["parent"] is not None:
                identifier(area["parent"], "parent")
            areas[area["id"]] = [] if area["parent"] is None else [area["parent"]]
        acyclic(areas, "Area hierarchy")
        areas = set(areas)
    del document

    index = corpus / "area_entries.json"
    with checking(index):
        document = json_object(index)
        fields(document, ("areas",))
        require(isinstance(document["areas"], dict), "areas must be an object")
        listed = {}
        for area, ids in document["areas"].items():
            require(area in areas, f"Unknown area: {area}")
            identifiers(ids, "entry ID")
            for entry_id in ids:
                require(entry_id not in listed,
                        f"Entry listed more than once: {entry_id}")
                listed[entry_id] = area
    del document

    graph, requirements, modules = {}, {}, set()
    nodes_dir = corpus / "nodes"
    require(nodes_dir.is_dir(), f"Missing node directory: {nodes_dir}")
    for path in nodes_dir.iterdir():
        if path.suffix != ".json":
            continue
        with checking(path):
            identifier(path.stem)
            record = json_object(path)
            graph[path.stem] = node_metadata(record, path.stem)
            requirements[path.stem] = set(record["axioms"])
            module = record.get("module")
            if source_root is not None and module and module not in modules:
                modules.add(module)
                source = source_path(module, source_root)
                require(source.is_file(), f"Missing Lean source: {source}")
                # Check readability/encoding once per module without retaining its text.
                with source.open(encoding="utf-8") as stream:
                    for _ in stream:
                        pass
    with checking(nodes_dir):
        acyclic(graph, "Node dependencies")
        check_axiom_dependencies(graph, requirements)
    node_ids = set(graph)
    del graph, requirements

    blocks_by_entry, links = {}, []
    entries_dir = corpus / "entries"
    require(entries_dir.is_dir(), f"Missing entries directory: {entries_dir}")
    for directory in entries_dir.iterdir():
        if not directory.is_dir():
            continue
        metadata = directory / "entry.json"
        with checking(metadata):
            identifier(directory.name)
            record = json_object(metadata)
            entry_metadata(record, directory.name, areas)
            require(listed.get(directory.name) == record["primary_area"],
                    "Entry must be listed once under its primary area in area_entries.json")
        source = directory / "entry.html"
        with checking(source):
            root, blocks, references, formal_ids, assets = checked_source(
                source.read_text(encoding="utf-8"))
            missing = formal_ids - node_ids
            require(not missing, f"Unknown formal nodes: {', '.join(missing)}")
            for asset in assets:
                check_asset(directory, asset)
            blocks_by_entry[directory.name] = blocks
            links.extend((source, target, anchor)
                         for target, anchor in references)
            del root
    with checking(index):
        missing = listed.keys() - blocks_by_entry.keys()
        require(not missing, f"Missing entries: {', '.join(missing)}")
    for source, target, anchor in links:
        with checking(source):
            require(target in blocks_by_entry,
                    f"Missing referenced entry: {target}")
            require(anchor in blocks_by_entry[target],
                    f"Reference must name a mathematical block: {target}#{anchor}")
    return len(blocks_by_entry), len(node_ids), len(areas)
