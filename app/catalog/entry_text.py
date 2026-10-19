"""Parse entry prose on demand, retaining only a bounded, process-local cache.

The budget accounts for retained Python strings, containers and per-record cache
bookkeeping, rather than just source-file bytes. It is not a process RSS limit:
parsing an entry and serving a response require temporary memory, and each worker
has its own cache. Oversized entries are returned without being cached.
"""

from collections import Counter, OrderedDict
import os
from pathlib import Path
import re
import sys
from threading import RLock
from urllib.parse import urlsplit

from .equations import LABEL
from .sources import Element
from .validation import checked_source


DEFAULT_MAX_BYTES = 8 * 1024 * 1024
DEFAULT_MAX_ENTRIES = 128
TEXT_BOUNDARIES = {
    "p", "div", "li", "ul", "ol", "blockquote", "pre", "figure",
    "figcaption", "table", "caption", "tr", "details", "summary",
    "h2", "h3", "h4", "br", "hr", "dl", "dt", "dd",
}
# Conservatively charge each retained item for an OrderedDict slot in addition
# to the deeply sized key/record. The fixed empty-cache/lock overhead is excluded.
_LRU_ENTRY_BYTES = (sys.getsizeof(OrderedDict((("item", None),)))
                    - sys.getsizeof(OrderedDict()))


def _is_answer(node):
    return (node.tag == "details"
            and "question-answer" in node.attrs.get("class", "").split())


def _normalize_text(parts):
    """Normalize whitespace, retaining integer link slots as visible tokens."""
    result, words = [], []
    pending = ""
    started = False
    for part in parts:
        tokens = [part] if isinstance(part, int) else re.findall(r"\s+|\S+", part)
        for token in tokens:
            if isinstance(token, str) and token.isspace():
                pending = "\n" if "\n" in token or pending == "\n" else " "
                continue
            if started and pending:
                words.append(pending)
            pending = ""
            if isinstance(token, int):
                if words:
                    result.append("".join(words))
                    words = []
                result.append(token)
            else:
                words.append(token)
            started = True
    if words:
        result.append("".join(words))
    return result if any(isinstance(part, int) for part in result) else "".join(result)


def render_text(value, labels=None):
    """Resolve cached link slots without retaining expanded copies of the prose.

    With no labels, return authored text, as used by the text search. A caller
    supplying labels must use the block's original link ordinals.
    """
    if isinstance(value, str):
        return value
    labels = {} if labels is None else labels
    return _normalize_text(labels.get(part, "") if isinstance(part, int) else part
                           for part in value)


def _plain_text(nodes, *, omit_answers=False, omit_summary=False, empty_links=None):
    """Keep prose boundaries, with typed link slots instead of HTML markup."""
    parts = []

    def visit(node):
        if isinstance(node, str):
            parts.append(re.sub(r"\s+", " ", node))
            return
        if node.tag in {"script", "style"}:
            return
        if omit_answers and _is_answer(node):
            return
        if omit_summary and node.tag == "summary":
            return
        if empty_links is not None and id(node) in empty_links:
            parts.append(empty_links[id(node)])
            return
        boundary = node.tag in TEXT_BOUNDARIES
        if boundary:
            parts.append("\n")
        for child in node.children:
            visit(child)
        if node.tag in {"td", "th"}:
            parts.append(" ")
        if boundary:
            parts.append("\n")

    for node in nodes:
        visit(node)
    return _normalize_text(parts)


def _parse_entry_text(source, entry_id):
    root, *_ = checked_source(source)
    blocks = {}
    anchor_numbers = Counter()
    for section in root.children:
        if not isinstance(section, Element):
            continue
        heading = next(child for child in section.children
                       if isinstance(child, Element) and child.tag == "h2")
        block = {
            "title": heading.text().strip(), "kind": section.attrs["data-kind"],
            "formal_ids": (section.attrs["data-formal"].split()
                           if "data-formal" in section.attrs else None),
            "links": [],
        }
        answers, empty_links, anchor_labels = [], {}, {}

        def visit(node, in_answer=False):
            if not isinstance(node, Element):
                return
            is_answer = _is_answer(node)
            if is_answer and not in_answer:
                answers.append(node)
            in_answer = in_answer or is_answer
            if node.tag in {"figure", "table"}:
                anchor_numbers[node.tag] += 1
                if node.attrs.get("id"):
                    anchor_labels[node.attrs["id"]] = (
                        f"{node.tag.capitalize()} {anchor_numbers[node.tag]}")
            if (node.tag in {"div", "p"}
                    and "math-display" in node.attrs.get("class", "").split()
                    and (labels := LABEL.findall(node.text()))):
                anchor_numbers["equation"] += 1
                anchor_labels[labels[0]] = f'({anchor_numbers["equation"]})'
            if node.tag == "a":
                href = node.attrs["href"]
                url = urlsplit(href)
                kind = ("asset" if href.startswith("assets/") else
                        "external" if url.scheme or url.netloc else "internal")
                link = {"href": href, "text": _plain_text(node.children),
                        "kind": kind, "in_answer": in_answer}
                if kind == "internal":
                    link["target"] = f"{url.path or entry_id}#{url.fragment}"
                    if not node.text().strip():
                        empty_links[id(node)] = len(block["links"])
                block["links"].append(link)
            for child in node.children:
                visit(child, in_answer)

        visit(section)
        block["text"] = _plain_text(
            [child for child in section.children if child is not heading],
            omit_answers=True, empty_links=empty_links)
        answer_parts = []
        for answer in answers:
            text = _plain_text(answer.children, omit_summary=True, empty_links=empty_links)
            if text:
                answer_parts.extend(["\n", *text] if isinstance(text, list) else ["\n", text])
        block["answer_text"] = _normalize_text(answer_parts)
        if anchor_labels:
            block["anchor_labels"] = anchor_labels
        blocks[section.attrs["id"]] = block
    # The parsed HTML tree, source and raw bytes are local temporaries only.
    return blocks


def _identity(stat):
    return (stat.st_dev, stat.st_ino, stat.st_size,
            stat.st_mtime_ns, stat.st_ctime_ns)


def _deep_size(value, seen=None):
    """Account for nested retained Python objects without double-counting aliases."""
    seen = set() if seen is None else seen
    if id(value) in seen:
        return 0
    seen.add(id(value))
    size = sys.getsizeof(value)
    if isinstance(value, dict):
        size += sum(_deep_size(key, seen) + _deep_size(item, seen)
                    for key, item in value.items())
    elif isinstance(value, (list, tuple)):
        size += sum(_deep_size(item, seen) for item in value)
    return size


class LRUEntryTextCache:
    """Bounded entry text cache; returned records must be treated as read-only.

    Access and parsing are serialized so concurrent requests do not populate
    duplicate entries or evade accounting. Source identity is checked on every
    access; both in-place changes and atomic replacements invalidate old text.
    """

    def __init__(self, *, max_bytes=DEFAULT_MAX_BYTES, max_entries=DEFAULT_MAX_ENTRIES):
        self._lock = RLock()
        self._entries = OrderedDict()
        self._bytes = 0
        self._hits = self._misses = self._evictions = 0
        self.configure(max_bytes=max_bytes, max_entries=max_entries)

    def configure(self, *, max_bytes, max_entries):
        for value in (max_bytes, max_entries):
            if type(value) is not int or value < 0:
                raise ValueError("Entry text cache limits must be nonnegative integers")
        with self._lock:
            self.max_bytes, self.max_entries = max_bytes, max_entries
            self._prune()

    def _remove(self, key):
        record = self._entries.pop(key, None)
        if record is not None:
            self._bytes -= record[2]
            if not self._entries:
                self._entries.clear()

    def _prune(self):
        pruned = False
        while self._entries and (self._bytes > self.max_bytes
                                 or len(self._entries) > self.max_entries
                                 or not self.max_bytes or not self.max_entries):
            self._remove(next(iter(self._entries)))
            self._evictions += 1
            pruned = True
        if pruned:
            # Drop spare hash-table capacity after reducing configured limits.
            self._entries = OrderedDict(self._entries)

    def clear(self):
        with self._lock:
            self._entries.clear()
            self._bytes = 0
            self._hits = self._misses = self._evictions = 0

    def info(self):
        with self._lock:
            return {"bytes": self._bytes, "entries": len(self._entries),
                    "max_bytes": self.max_bytes, "max_entries": self.max_entries,
                    "hits": self._hits, "misses": self._misses,
                    "evictions": self._evictions}

    def get(self, corpus, entry_id):
        # Reject URL-supplied IDs before path resolution or opening any file.
        if not isinstance(entry_id, str) or not re.fullmatch(
                r"[A-Za-z0-9][A-Za-z0-9_-]*", entry_id):
            raise FileNotFoundError(f"Invalid corpus ID: {entry_id}")
        path = (Path(corpus).resolve() / "entries" / entry_id / "entry.html")
        key = str(path)
        with self._lock:
            try:
                observed = _identity(path.stat())
            except OSError:
                self._remove(key)
                raise
            cached = self._entries.get(key)
            if cached is not None and cached[0] == observed:
                self._entries.move_to_end(key)
                self._hits += 1
                return cached[1]
            self._remove(key)
            self._misses += 1
            for _ in range(3):
                # The path may be replaced after stat/open, or edited in place
                # while reading. Do not cache text under another file's identity.
                with path.open("rb") as stream:
                    before = _identity(os.fstat(stream.fileno()))
                    raw = stream.read()
                    after = _identity(os.fstat(stream.fileno()))
                if before != after:
                    continue
                try:
                    blocks = _parse_entry_text(raw.decode("utf-8"), entry_id)
                except ValueError:
                    if _identity(path.stat()) != before:
                        continue
                    raise
                if _identity(path.stat()) != before:
                    continue
                if not self.max_bytes or not self.max_entries:
                    return blocks
                # The final record has the same tuple layout as this temporary
                # sizing tuple, plus one integer for its recorded byte charge.
                size = (_deep_size((key, before, blocks))
                        + sys.getsizeof(0) + _LRU_ENTRY_BYTES)
                if size <= self.max_bytes:
                    self._entries[key] = (before, blocks, size)
                    self._bytes += size
                    self._prune()
                return blocks
            raise OSError(f"Entry source changed repeatedly while reading: {path}")


_cache = LRUEntryTextCache()


def get_entry_text(corpus, entry_id):
    """Read current prose fragments; use render_text to resolve any link slots."""
    from django.conf import settings

    _cache.configure(
        max_bytes=getattr(settings, "CORPUS_TEXT_CACHE_BYTES", DEFAULT_MAX_BYTES),
        max_entries=getattr(settings, "CORPUS_TEXT_CACHE_ENTRIES", DEFAULT_MAX_ENTRIES),
    )
    return _cache.get(corpus, entry_id)


def clear_text_cache():
    _cache.clear()


def text_cache_info():
    return _cache.info()
