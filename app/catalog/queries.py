"""Read-only authoring queries over a derived index and live corpus metadata.

The index supplies structural relationships. A bounded runtime cache supplies
parsed entry text; entry/node JSON is read directly from current files.
No request runs Lean. Saved proof flags describe the last build.
"""

from collections import defaultdict
from pathlib import Path
import re
from urllib.parse import quote

from django.templatetags.static import static

from .entry_files import read_area_entries, read_areas, read_entry_metadata
from .entry_text import get_entry_text, render_text
from .node_files import node_ids, read_node, source_for_module
from .progress import block_progress, entry_progress
from .sources import KINDS
from .validation import ANCHOR


class QueryError(ValueError):
    def __init__(self, message, *, status=400, code="invalid_query"):
        super().__init__(message)
        self.status = status
        self.code = code


def _page_arguments(limit, offset):
    if type(limit) is not int or not 1 <= limit <= 100:
        raise QueryError("limit must be an integer from 1 to 100")
    if type(offset) is not int or offset < 0:
        raise QueryError("offset must be a nonnegative integer")


def _terms(query):
    if not isinstance(query, str) or len(query) > 200:
        raise QueryError("query must be a string of at most 200 characters")
    return query.casefold().split()


def _selected_fields(fields, allowed):
    if fields is None:
        return None
    if (not isinstance(fields, (list, tuple, set, frozenset)) or not fields
            or any(not isinstance(field, str) or field not in allowed for field in fields)):
        raise QueryError("fields must be a nonempty selection of known fields")
    return set(fields) | {"id"}


def _entry_url(identifier):
    return f"/entries/{quote(identifier, safe='')}/"


def _target_url(target):
    identifier, _, anchor = target.partition("#")
    return _entry_url(identifier) + (f"#{quote(anchor, safe='')}" if anchor else "")


def _outdated(message):
    return QueryError(message + "; rebuild with validate_corpus --write-index",
                      status=409, code="index_outdated")


class CorpusQuery:
    """One request's queries; cached metadata never outlives this instance."""

    INCLUDES = {"blocks", "nodes", "references", "coverage", "navigation"}
    NODE_FIELDS = {"id", "description", "module", "declaration", "dependencies", "verified",
                   "signature", "declaration_line", "url", "source_path", "matched_queries"}
    ENTRY_DEFAULT_FIELDS = {"id", "title", "primary_area", "additional_areas",
                            "reading_position", "block_count", "url"}
    ENTRY_FIELDS = ENTRY_DEFAULT_FIELDS | {
        "abstract", "summary", "reading_time", "based_on", "formalization"}

    def __init__(self, index, corpus):
        self.index = index
        self.corpus = Path(corpus)
        self._entries = {}
        self._nodes = {}
        self._anchors_by_block = None

    def _entry(self, identifier, *, cache=True):
        if not isinstance(identifier, str) or identifier not in self.index["entries"]:
            raise QueryError("Entry not found", status=404, code="not_found")
        if identifier not in self._entries:
            try:
                record = read_entry_metadata(identifier, self.corpus)
            except (OSError, ValueError) as error:
                raise _outdated(f"Cannot read indexed entry {identifier}") from error
            if not isinstance(record, dict):
                raise _outdated(f"Indexed entry {identifier} is not a JSON object")
            if record.get("id") != identifier:
                raise _outdated(f"Indexed entry {identifier} has a different ID")
            if cache:
                self._entries[identifier] = record
            return record
        return self._entries[identifier]

    def _node(self, identifier, *, expected=False, cache=True):
        if (not isinstance(identifier, str)
                or not re.fullmatch(r"[A-Za-z0-9][A-Za-z0-9_-]*", identifier)):
            raise QueryError("Node not found", status=404, code="not_found")
        if identifier not in self._nodes:
            try:
                record = read_node(identifier, self.corpus)
            except (OSError, ValueError) as error:
                if expected:
                    raise _outdated(f"Cannot read indexed node {identifier}") from error
                raise QueryError("Node not found", status=404, code="not_found") from error
            if not isinstance(record, dict):
                raise _outdated(f"Node {identifier} is not a JSON object")
            if record.get("id") != identifier:
                raise _outdated(f"Node {identifier} has a different ID")
            if cache:
                self._nodes[identifier] = record
            return record
        return self._nodes[identifier]

    def _node_result(self, identifier, *, expected=False, fields=None, matched_queries=None):
        node = self._node(identifier, expected=expected)
        result = dict(node) if fields is None else {
            key: value for key, value in node.items() if key in fields}
        if fields is None or "url" in fields:
            result["url"] = f"/nodes/{quote(identifier, safe='')}/"
        if node.get("module") and (fields is None or "source_path" in fields):
            if not isinstance(node["module"], str):
                raise _outdated(f"Node {identifier} has an invalid module")
            result["source_path"] = source_for_module(node["module"])
        if matched_queries is not None and (fields is None or "matched_queries" in fields):
            result["matched_queries"] = matched_queries
        return result

    def _resolve_areas(self, area, include_descendants=True):
        """Resolve live taxonomy once; entry membership remains live metadata."""
        if type(include_descendants) is not bool:
            raise QueryError("include_descendants must be a boolean")
        if area is None:
            return None, None
        try:
            taxonomy = read_areas(self.corpus)
        except (OSError, ValueError, KeyError, TypeError, AttributeError) as error:
            raise _outdated("Cannot read area taxonomy") from error
        for identifier, record in taxonomy.items():
            if not isinstance(record, dict):
                raise _outdated("Area taxonomy has an invalid record")
            parent = record.get("parent")
            if (not isinstance(identifier, str)
                    or (parent is not None and (not isinstance(parent, str) or parent not in taxonomy))):
                raise _outdated("Area taxonomy has an invalid parent")
        completed = set()
        for identifier in taxonomy:
            path = set()
            ancestor = identifier
            while ancestor is not None and ancestor not in completed:
                if ancestor in path:
                    raise _outdated("Area taxonomy has a parent cycle")
                path.add(ancestor)
                ancestor = taxonomy[ancestor].get("parent")
            completed.update(path)
        if not isinstance(area, str) or area not in taxonomy:
            raise QueryError("Area not found", status=404, code="not_found")
        areas = {area}
        if include_descendants:
            pending = [area]
            children = defaultdict(list)
            for identifier, record in taxonomy.items():
                children[record.get("parent")].append(identifier)
            while pending:
                for child in children[pending.pop()]:
                    if child not in areas:
                        areas.add(child)
                        pending.append(child)
        return areas, taxonomy

    def _entry_areas(self, entry, taxonomy=None):
        primary = entry.get("primary_area")
        additional = entry.get("additional_areas", [])
        if (not isinstance(primary, str) or not isinstance(additional, list)
                or any(not isinstance(identifier, str) for identifier in additional)
                or (taxonomy is not None and
                    any(identifier not in taxonomy for identifier in [primary, *additional]))):
            raise _outdated(f"Entry {entry['id']} has invalid areas")
        return {primary, *additional}

    def list_entries(self, *, area=None, include_descendants=True, fields=None,
                     limit=20, offset=0):
        _page_arguments(limit, offset)
        selected_fields = _selected_fields(fields, self.ENTRY_FIELDS)
        if selected_fields is None:
            selected_fields = self.ENTRY_DEFAULT_FIELDS
        areas, taxonomy = self._resolve_areas(area, include_descendants)
        candidates = []
        for identifier in self.index["entries"]:
            entry = self._entry(identifier, cache=False)
            memberships = self._entry_areas(entry, taxonomy)
            if areas is None or areas.intersection(memberships):
                candidates.append((entry["primary_area"],
                                   self.index["entries"][identifier]["reading_position"], identifier))
        candidates.sort()
        results = []
        for _, _, identifier in candidates[offset:offset + limit]:
            record = self._entry(identifier)
            result = {field: value for field, value in record.items() if field in selected_fields}
            derived = {"reading_position": self.index["entries"][identifier]["reading_position"],
                       "block_count": len(self.index["entries"][identifier]["blocks"]),
                       "url": _entry_url(identifier)}
            result.update({field: value for field, value in derived.items() if field in selected_fields})
            results.append(result)
        return {"count": len(candidates), "limit": limit, "offset": offset, "results": results}

    def _entry_text(self, entry_id):
        """Validate just the needed entry, without retaining it on this service."""
        try:
            blocks = get_entry_text(self.corpus, entry_id)
        except (OSError, ValueError) as error:
            raise _outdated(f"Cannot parse indexed entry {entry_id}") from error
        if list(blocks) != self.index["entries"][entry_id]["blocks"]:
            raise _outdated(f"Blocks for indexed entry {entry_id} have changed")
        for identifier, block in blocks.items():
            key = f"{entry_id}#{identifier}"
            indexed = self.index["blocks"][key]
            if (block["kind"] != indexed["kind"]
                    or block["formal_ids"] != indexed["formal_ids"]):
                raise _outdated(f"Structure of indexed block {entry_id}#{identifier} has changed")
            current_links = [(position, link["target"], link["in_answer"])
                             for position, link in enumerate(block["links"])
                             if link["kind"] == "internal"]
            indexed_links = [
                (reference["link_index"], reference["target"], reference["in_answer"])
                for edge_id in self.index["outgoing"].get(key, [])
                for reference in [self.index["references"][edge_id]]
            ]
            if current_links != indexed_links:
                raise _outdated(f"Links in indexed block {key} have changed")
        return blocks

    def _context_link(self, link, entry_id, parsed):
        """Resolve live labels without rendering or mutating cached source text."""
        result = link.copy()
        if link["kind"] == "internal":
            target = link["target"]
            result["url"] = _target_url(target)
            if not link["text"]:
                target_entry, _, anchor = target.partition("#")
                if target in self.index["blocks"]:
                    if target_entry == entry_id:
                        block = self.index["blocks"][target]
                        result["text"] = f'{block["kind"].capitalize()} {block["number"]}'
                    else:
                        target_blocks = self._entry_text(target_entry)
                        result["text"] = target_blocks[anchor]["title"]
                elif target in self.index["anchors"]:
                    owner = self.index["anchors"][target].partition("#")[2]
                    target_blocks = parsed if target_entry == entry_id else self._entry_text(target_entry)
                    result["text"] = target_blocks[owner].get("anchor_labels", {}).get(anchor, anchor)
                elif not anchor:
                    result["text"] = self._entry(target_entry)["title"]
                else:
                    raise _outdated(f"Cannot resolve indexed reference {target}")
        elif link["kind"] == "asset":
            result["url"] = static(f"entries/{entry_id}/{link['href'].removeprefix('assets/')}")
        else:
            result["url"] = link["href"]
        return result

    def _block_summary(self, key, parsed):
        entry_id, _, identifier = key.partition("#")
        block = self.index["blocks"][key]
        return {"key": key, "entry_id": entry_id, "id": identifier,
                "title": parsed[identifier]["title"], "kind": block["kind"],
                "label": f'{block["kind"].capitalize()} {block["number"]}',
                "url": _target_url(key)}

    def _block_keys(self, entry_id):
        return [f"{entry_id}#{identifier}"
                for identifier in self.index["entries"][entry_id]["blocks"]]

    def get_entry_context(self, entry_id, *, include=None, include_answers=True,
                          block_ids=None, limit=20, offset=0):
        _page_arguments(limit, offset)
        if type(include_answers) is not bool:
            raise QueryError("include_answers must be a boolean")
        if include is None:
            include = {"blocks", "navigation"}
        if (not isinstance(include, (set, frozenset, list, tuple))
                or any(not isinstance(value, str) for value in include)
                or not set(include) <= self.INCLUDES):
            raise QueryError("Unknown include; choose blocks, nodes, references, coverage or navigation")
        include = set(include)
        entry = self._entry(entry_id)
        result = {"entry": {**entry, "url": _entry_url(entry_id)},
                  "reading_position": self.index["entries"][entry_id]["reading_position"]}
        keys = self._block_keys(entry_id)
        if block_ids is not None:
            if (not isinstance(block_ids, (list, tuple)) or not 1 <= len(block_ids) <= 100
                    or any(not isinstance(identifier, str) or not ANCHOR.fullmatch(identifier)
                           for identifier in block_ids)):
                raise QueryError("block_ids must contain from 1 to 100 nonempty local block IDs")
            if not include.intersection({"blocks", "nodes", "references", "coverage"}):
                raise QueryError("block_ids requires blocks, nodes, references or coverage")
            requested = set(block_ids)
            unknown = requested - set(self.index["entries"][entry_id]["blocks"])
            if unknown:
                raise QueryError(f"Blocks not found in {entry_id}: {', '.join(sorted(unknown))}",
                                 status=404, code="not_found")
            keys = [key for key in keys if key.partition("#")[2] in requested]
            result["block_ids"] = [key.partition("#")[2] for key in keys]
        parsed = self._entry_text(entry_id) if include.intersection({"blocks", "nodes"}) else None
        if "blocks" in include:
            selected = []
            page_keys = keys[offset:offset + limit]
            for key in page_keys:
                prose = parsed[key.partition("#")[2]]
                links = {}
                for position, link in enumerate(prose["links"]):
                    if include_answers or not link["in_answer"]:
                        links[position] = self._context_link(link, entry_id, parsed)
                labels = {position: link["text"] for position, link in links.items()}
                block = {**self.index["blocks"][key], **self._block_summary(key, parsed),
                         "text": render_text(prose["text"], labels)}
                if include_answers:
                    block["answer_text"] = render_text(prose["answer_text"], labels)
                if links:
                    block["links"] = list(links.values())
                selected.append(block)
            result["blocks"] = {"count": len(keys), "limit": limit,
                                "offset": offset, "results": selected}
        if "nodes" in include:
            identifiers = list(dict.fromkeys(
                identifier for key in keys
                for identifier in self.index["blocks"][key]["formal_ids"] or []))
            result["nodes"] = {"count": len(identifiers), "limit": limit, "offset": offset,
                               "results": [self._node_result(identifier, expected=True)
                                           for identifier in identifiers[offset:offset + limit]]}
        if "references" in include:
            if block_ids is None:
                result["references"] = self.get_references(
                    entry_id, limit=limit, offset=offset, include_answers=include_answers)
            else:
                result["references"] = self._references_for_keys(
                    entry_id, entry_id, keys, self._reference_targets(keys),
                    direction="both", limit=limit, offset=offset, include_answers=include_answers)
        if "coverage" in include:
            result["coverage"] = self._coverage_for_keys({entry_id: keys})
        if "navigation" in include:
            try:
                ordered = read_area_entries(self.corpus)[entry["primary_area"]]
                if (not isinstance(ordered, list)
                        or any(not isinstance(identifier, str) for identifier in ordered)):
                    raise ValueError("Invalid reading order")
                position = ordered.index(entry_id)
            except (OSError, ValueError, KeyError, TypeError) as error:
                raise _outdated(f"Cannot find reading order for {entry_id}") from error

            def neighbor(index):
                if not 0 <= index < len(ordered):
                    return None
                identifier = ordered[index]
                if identifier not in self.index["entries"]:
                    raise _outdated(f"Reading-order entry {identifier} is absent from the index")
                metadata = self._entry(identifier)
                if not isinstance(metadata.get("title"), str):
                    raise _outdated(f"Reading-order entry {identifier} has no valid title")
                return {"id": identifier, "title": metadata["title"],
                        "url": _entry_url(identifier)}

            result["navigation"] = {"previous": neighbor(position - 1),
                                    "next": neighbor(position + 1)}
        return result

    def search_blocks(self, query, *, area=None, kind=None, include_answers=False,
                      limit=20, offset=0):
        _page_arguments(limit, offset)
        terms = _terms(query)
        if kind is not None and (not isinstance(kind, str) or kind not in KINDS):
            raise QueryError("Unknown block kind")
        if type(include_answers) is not bool:
            raise QueryError("include_answers must be a boolean")
        areas, taxonomy = self._resolve_areas(area)
        results = []
        count = 0
        for entry_id in sorted(self.index["entries"]):
            if areas is not None:
                metadata = self._entry(entry_id)
                if not areas.intersection(self._entry_areas(metadata, taxonomy)):
                    continue
            keys = [key for key in self._block_keys(entry_id)
                    if kind is None or kind == self.index["blocks"][key]["kind"]]
            if not keys:
                continue
            parsed = self._entry_text(entry_id)
            for key in keys:
                block = parsed[key.partition("#")[2]]
                fields = {name: render_text(block[name]) for name in
                          (["title", "text", "answer_text"] if include_answers else ["title", "text"])}
                combined = "\n".join(fields.values()).casefold()
                if not all(term in combined for term in terms):
                    continue
                count += 1
                if not offset < count <= offset + limit:
                    continue
                matches = [name for name, value in fields.items()
                           if terms and any(term in value.casefold() for term in terms)]
                single = next((name for name in matches
                               if all(term in fields[name].casefold() for term in terms)), None)
                snippet_field = single or (matches[0] if matches else "text")
                text = re.sub(r"\s+", " ", fields[snippet_field]).strip()
                positions = [text.casefold().find(term) for term in terms]
                first = min((position for position in positions if position >= 0), default=0)
                start = max(0, first - 80)
                snippet = text[start:start + 296]
                snippet = ("…" if start else "") + snippet
                if start + 296 < len(text):
                    snippet += "…"
                results.append({**self._block_summary(key, parsed), "snippet": snippet,
                                "match_in": single or ("multiple" if matches else None)})
        return {"count": count, "limit": limit, "offset": offset, "results": results}

    def find_nodes(self, query="", *, declaration=None, module=None, verified=None,
                   area=None, include_descendants=True, usage="any", fields=None,
                   queries=None, limit=20, offset=0):
        _page_arguments(limit, offset)
        selected_fields = _selected_fields(fields, self.NODE_FIELDS)
        queries = [query] if queries is None else queries
        if not isinstance(queries, (list, tuple)) or not 1 <= len(queries) <= 10:
            raise QueryError("Provide between 1 and 10 queries")
        alternatives = [_terms(value) for value in queries]
        multiple = len(alternatives) > 1
        if multiple and any(not terms for terms in alternatives):
            raise QueryError("Blank queries cannot be combined with alternatives")
        for name, value in (("declaration", declaration), ("module", module)):
            if value is not None and (not isinstance(value, str) or not value or len(value) > 500):
                raise QueryError(f"{name} must be a nonempty string of at most 500 characters")
        if verified is not None and type(verified) is not bool:
            raise QueryError("verified must be a boolean")
        if not isinstance(usage, str) or usage not in {"any", "mapped", "unmapped"}:
            raise QueryError("usage must be any, mapped or unmapped")
        areas, taxonomy = self._resolve_areas(area, include_descendants)
        candidates = None
        for value, lookup in ((declaration, "nodes_by_declaration"), (module, "module_nodes")):
            if value is not None:
                matching = set(self.index[lookup].get(value, []))
                candidates = matching if candidates is None else candidates & matching
        if areas is not None:
            matching = set()
            for entry_id in self.index["entries"]:
                metadata = self._entry(entry_id, cache=False)
                if areas.intersection(self._entry_areas(metadata, taxonomy)):
                    for key in self._block_keys(entry_id):
                        matching.update(self.index["blocks"][key]["formal_ids"] or [])
            candidates = matching if candidates is None else candidates & matching
        if usage != "any":
            mapped = set(self.index["node_consumers"])
            matching = mapped if usage == "mapped" else set(node_ids(self.corpus)) - mapped
            candidates = matching if candidates is None else candidates & matching
        identifiers = sorted(candidates) if candidates is not None else node_ids(self.corpus)

        def check_binding(identifier, node):
            if ((declaration is not None and node.get("declaration") != declaration)
                    or (module is not None and node.get("module") != module)):
                raise _outdated(f"Binding for indexed node {identifier} has changed")

        def result(identifier, matches):
            include_matches = multiple or (selected_fields is not None
                                           and "matched_queries" in selected_fields)
            return self._node_result(identifier, expected=True, fields=selected_fields,
                                     matched_queries=matches if include_matches else None)

        if not any(alternatives) and verified is None:
            rows = []
            for identifier in identifiers[offset:offset + limit]:
                node = self._node(identifier, expected=True)
                check_binding(identifier, node)
                rows.append(result(identifier, [0]))
            return {"count": len(identifiers), "limit": limit, "offset": offset, "results": rows}
        results = []
        count = 0
        for identifier in identifiers:
            # Candidate scans retain only records returned on the requested page.
            node = self._node(identifier, expected=True, cache=False)
            check_binding(identifier, node)
            if verified is not None and bool(node.get("verified", False)) != verified:
                continue
            text = "\n".join(str(node.get(field) or "") for field in
                             ("id", "description", "declaration", "module", "signature")).casefold()
            matches = [position for position, terms in enumerate(alternatives)
                       if all(term in text for term in terms)]
            if matches:
                count += 1
                if offset < count <= offset + limit:
                    self._nodes[identifier] = node
                    results.append(result(identifier, matches))
        return {"count": count, "limit": limit, "offset": offset, "results": results}

    def _reference_targets(self, keys):
        if self._anchors_by_block is None:
            self._anchors_by_block = defaultdict(list)
            for key, owner in self.index["anchors"].items():
                self._anchors_by_block[owner].append(key)
        return [target for key in keys for target in [key, *self._anchors_by_block[key]]]

    def _references_for_keys(self, target, entry_id, outgoing_keys, incoming_keys, *,
                             direction, limit, offset, include_answers):
        edge_ids = set()
        if direction in {"outgoing", "both"}:
            # A source with no indexed edges (or an empty result page) can now
            # contain new links. Validate before selecting indexed edges.
            self._entry_text(entry_id)
            for key in outgoing_keys:
                edge_ids.update(self.index["outgoing"].get(key, []))
        if direction in {"incoming", "both"}:
            for key in incoming_keys:
                edge_ids.update(self.index["incoming"].get(key, []))
        identifiers = sorted(edge_id for edge_id in edge_ids
                             if include_answers or not self.index["references"][edge_id]["in_answer"])
        rows = []
        current_entry = None
        parsed = None
        for identifier in identifiers[offset:offset + limit]:
            reference = self.index["references"][identifier]
            source_entry, _, source_block = reference["source"].partition("#")
            if source_entry != current_entry:
                parsed = self._entry_text(source_entry)
                current_entry = source_entry
            # _entry_text checked this source's complete internal-link sequence.
            link = parsed[source_block]["links"][reference["link_index"]]
            rows.append({"id": identifier, "source": reference["source"],
                         "target": reference["target"], "in_answer": reference["in_answer"],
                         "text": link["text"], "source_url": _target_url(reference["source"]),
                         "target_url": _target_url(reference["target"])})
        return {"target": target, "direction": direction, "count": len(identifiers),
                "limit": limit, "offset": offset, "results": rows}

    def get_references(self, target, *, direction="both", limit=20, offset=0,
                       include_answers=True):
        """Blocks include nested anchors; an anchor's outgoing edges use its owner."""
        _page_arguments(limit, offset)
        if not isinstance(direction, str) or direction not in {"incoming", "outgoing", "both"}:
            raise QueryError("direction must be incoming, outgoing or both")
        if type(include_answers) is not bool:
            raise QueryError("include_answers must be a boolean")
        if not isinstance(target, str) or target.count("#") > 1:
            raise QueryError("target must be an entry ID or entry#anchor")
        entry_id, separator, anchor = target.partition("#")
        if entry_id not in self.index["entries"]:
            raise QueryError("Entry not found", status=404, code="not_found")
        if separator and not anchor:
            raise QueryError("An anchor after # must be nonempty")
        if not separator:
            outgoing_keys = self._block_keys(entry_id)
            incoming_keys = [f"{entry_id}#", *self._reference_targets(outgoing_keys)]
        elif target in self.index["blocks"]:
            outgoing_keys = [target]
            incoming_keys = self._reference_targets(outgoing_keys)
        elif target in self.index["anchors"]:
            outgoing_keys = [self.index["anchors"][target]]
            incoming_keys = [target]
        else:
            raise QueryError("Anchor not found", status=404, code="not_found")
        return self._references_for_keys(
            target, entry_id, outgoing_keys, incoming_keys, direction=direction,
            limit=limit, offset=offset, include_answers=include_answers)

    def get_coverage(self, entry_ids):
        if (not isinstance(entry_ids, (list, tuple)) or not 1 <= len(entry_ids) <= 20
                or any(not isinstance(identifier, str) for identifier in entry_ids)):
            raise QueryError("Provide between 1 and 20 entry IDs")
        identifiers = list(dict.fromkeys(entry_ids))
        for identifier in identifiers:
            if identifier not in self.index["entries"]:
                raise QueryError(f"Entry not found: {identifier}", status=404, code="not_found")
        return self._coverage_for_keys({identifier: self._block_keys(identifier)
                                        for identifier in identifiers})

    def _coverage_for_keys(self, entry_keys):
        nodes = {}
        entries = []
        for identifier, keys in entry_keys.items():
            self._entry_text(identifier)
            blocks = []
            for key in keys:
                ids = self.index["blocks"][key]["formal_ids"]
                for node_id in ids or []:
                    if node_id not in nodes:
                        node = self._node(node_id, expected=True)
                        nodes[node_id] = {"module": node.get("module"),
                                          "declaration": node.get("declaration"),
                                          "verified": node.get("verified", False)}
                blocks.append({"id": key.partition("#")[2], "key": key, "formal_ids": ids,
                               "formalization": block_progress(ids, nodes)})
            entries.append({"id": identifier, "formalization": entry_progress(blocks, nodes),
                            "blocks": blocks})
        return {"verification_source": "saved", "entries": entries, "nodes": nodes}

    def get_node_consumers(self, node_id, *, limit=20, offset=0):
        _page_arguments(limit, offset)
        node = self._node(node_id)
        keys = self.index["node_consumers"].get(node_id, [])
        rows = []
        current_entry = None
        parsed = None
        for key in keys[offset:offset + limit]:
            entry_id = key.partition("#")[0]
            if entry_id != current_entry:
                parsed = self._entry_text(entry_id)
                current_entry = entry_id
            rows.append(self._block_summary(key, parsed))
        return {"node_id": node_id, "dependencies": node.get("dependencies", []),
                "dependents": self.index["hint_dependents"].get(node_id, []),
                "count": len(keys), "limit": limit, "offset": offset,
                "results": rows}
