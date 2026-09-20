"""Parse repository-owned HTML sources without executing Django templates."""

from collections import Counter
from dataclasses import dataclass, field
from html import escape
from html.parser import HTMLParser
from pathlib import PurePosixPath
import re
from urllib.parse import urlencode, urlsplit

from django.templatetags.static import static
from django.urls import reverse
from django.utils.safestring import mark_safe


class ContentError(ValueError):
    """An entry's source or metadata is inconsistent."""


@dataclass
class Element:
    tag: str
    attrs: dict = field(default_factory=dict)
    children: list = field(default_factory=list)

    def walk(self):
        yield self
        for child in self.children:
            if isinstance(child, Element):
                yield from child.walk()

    def text(self):
        return ''.join(child.text() if isinstance(child, Element) else child
                       for child in self.children)


VOID_ELEMENTS = {"img", "br", "hr", "wbr"}
KINDS = {"definition", "lemma", "theorem", "question"}
IDENTIFIER = re.compile(r"[a-zA-Z0-9][a-zA-Z0-9_-]*\Z")


class SourceParser(HTMLParser):
    """A small tree for explicitly closed HTML; this is not an upload sanitizer."""

    def __init__(self):
        super().__init__(convert_charrefs=True)
        self.root = Element("root")
        self.stack = [self.root]

    def handle_starttag(self, tag, attrs):
        if len(dict(attrs)) != len(attrs):
            raise ContentError(f"Duplicate attributes on <{tag}>")
        node = Element(tag, dict(attrs))
        self.stack[-1].children.append(node)
        if tag not in VOID_ELEMENTS:
            self.stack.append(node)

    def handle_startendtag(self, tag, attrs):
        self.handle_starttag(tag, attrs)
        if tag not in VOID_ELEMENTS:
            self.handle_endtag(tag)

    def handle_endtag(self, tag):
        if len(self.stack) == 1 or self.stack[-1].tag != tag:
            raise ContentError(f"Unbalanced closing tag </{tag}>")
        self.stack.pop()

    def handle_data(self, data):
        self.stack[-1].children.append(data)


def parse_source(source):
    parser = SourceParser()
    parser.feed(source)
    parser.close()
    if len(parser.stack) != 1:
        raise ContentError(f"Unclosed <{parser.stack[-1].tag}>")
    from .equations import prepare_equations
    prepare_equations(parser.root)
    figures = {}
    for number, figure in enumerate((node for node in parser.root.walk() if node.tag == 'figure'), 1):
        captions = [node for node in figure.children if isinstance(
            node, Element) and node.tag == 'figcaption']
        if len(captions) != 1:
            raise ContentError('Each figure needs one figcaption')
        caption = captions[0]
        label = f'Figure {number}'
        caption.children.insert(0, Element(
            'span', {'class': 'figure-label'}, [label]))
        if figure.attrs.get('id'):
            figures[figure.attrs['id']] = label
    ids = set()
    for node in parser.root.walk():
        if "id" in node.attrs:
            identifier = node.attrs["id"]
            if not identifier or not re.fullmatch(r"[A-Za-z0-9][A-Za-z0-9_.:-]*", identifier) or identifier in ids:
                raise ContentError(
                    f"Invalid or duplicate anchor: {identifier}")
            ids.add(identifier)
    counts = Counter()
    blocks = []
    for node in parser.root.children:
        if isinstance(node, str) and not node.strip():
            continue
        if not isinstance(node, Element) or node.tag != "section":
            raise ContentError(
                "Entry content must be inside top-level <section> blocks")
        block_id, kind = node.attrs.get("id"), node.attrs.get("data-kind")
        if not block_id or kind not in KINDS:
            raise ContentError(
                "Each section needs an id and a supported data-kind")
        headings = [child for child in node.children
                    if isinstance(child, Element) and child.tag == "h2"]
        if len(headings) != 1 or not headings[0].text().strip():
            raise ContentError(f"{block_id}: expected one nonempty <h2> title")
        formal_ids = None
        if 'data-formal' in node.attrs:
            value = node.attrs['data-formal']
            if value is None:
                raise ContentError(
                    'Use data-formal="" for a block with nothing to formalize')
            formal_ids = value.split()
            if any(not IDENTIFIER.fullmatch(value) for value in formal_ids):
                raise ContentError(f'{block_id}: invalid formal node ID')
            if len(formal_ids) != len(set(formal_ids)):
                raise ContentError(f'{block_id}: duplicate formal node ID')
        counts[kind] += 1
        blocks.append({"id": block_id, "kind": kind, "formal_ids": formal_ids,
                       "title": headings[0].text().strip(),
                       "label": f"{kind.capitalize()} {counts[kind]}",
                       "nodes": [child for child in node.children if child is not headings[0]]})
        heading_id = f"{block_id}-title"
        if heading_id in ids:
            raise ContentError(f"Reserved heading anchor: {heading_id}")
    if not blocks:
        raise ContentError("An entry must contain at least one block")
    return blocks, ids, counts, figures


def reference_target(href, entry_id, catalog):
    """Resolve source-relative math links; ordinary local figure links stay local."""
    url = urlsplit(href)
    if url.scheme or url.netloc:
        return None
    if url.path in ("", "entry.html"):
        target_id = entry_id
    else:
        match = re.fullmatch(r"\.\./([^/]+)/entry\.html", url.path)
        if not match:
            raise ContentError(f"Unsupported relative link: {href}")
        target_id = match[1]
    target = catalog.get(target_id)
    if url.query or not target or url.fragment not in target["anchors"]:
        raise ContentError(f"Broken source link: {href}")
    if url.fragment not in target["blocks_by_id"]:
        if target_id != entry_id:
            raise ContentError(
                f"Cross-entry references must name a mathematical block: {href}")
        return None
    return target, target["blocks_by_id"][url.fragment]


def asset_path(entry_dir, src):
    path = PurePosixPath(src)
    if not src.startswith("assets/") or ".." in path.parts or "\\" in src:
        raise ContentError(f"Assets must use entry-local assets/ paths: {src}")
    resolved = (entry_dir / src).resolve()
    if not resolved.is_relative_to((entry_dir / "assets").resolve()) or not resolved.is_file():
        raise ContentError(f"Missing or escaped asset: {src}")
    return path.relative_to("assets").as_posix()


def render_block(block, entry, catalog, expanded_answer=None):
    """Render a fresh string; cached source trees are never mutated by requests."""
    def render(node):
        if isinstance(node, str):
            return escape(node, quote=False)
        attrs = dict(node.attrs)
        children = node.children
        if node.tag == "a":
            href = attrs.get("href", "")
            link = urlsplit(href)
            if href.startswith("assets/"):
                relative = asset_path(entry["directory"], href)
                attrs["href"] = static(f"entries/{entry['id']}/{relative}")
                resolved = None
            else:
                resolved = reference_target(href, entry["id"], catalog)
            if resolved:
                target, result = resolved
                query = urlencode({"from": entry["id"], "at": block["id"]})
                url = reverse("catalog:entry", args=[target["id"]])
                url += f"?{query}#{result['id']}"
                label = result["label"]
                if target["id"] != entry["id"]:
                    label = result["title"]
                attrs.update(href=url, **{"class": "lemma-reference"},
                             title=f"{result['label']} — {result['title']} · {target['title']}")
                children = [label]
            elif not link.scheme and not link.netloc and link.fragment in entry['figures']:
                figure_id = link.fragment
                query = urlencode({"from": entry["id"], "at": block["id"]})
                attrs.update(href=reverse('catalog:entry', args=[entry['id']]) + f'?{query}#{figure_id}',
                             **{'class': 'figure-reference'})
                children = [entry['figures'][figure_id]]
        if node.tag == "img":
            relative = asset_path(entry["directory"], attrs.get("src", ""))
            attrs["src"] = static(f"entries/{entry['id']}/{relative}")
        if node.tag == "details" and "question-answer" in attrs.get("class", "").split():
            attrs.pop("open", None)
            if block["id"] == expanded_answer:
                attrs["open"] = None
        attributes = ''.join(f' {key}' if value is None else f' {key}="{escape(value, quote=True)}"'
                             for key, value in attrs.items())
        start = f"<{node.tag}{attributes}>"
        if node.tag in VOID_ELEMENTS:
            return start
        html = start + ''.join(render(child)
                               for child in children) + f"</{node.tag}>"
        if node.tag == 'table':
            caption = next((child.text() for child in children
                            if isinstance(child, Element) and child.tag == 'caption'), 'Data table')
            return f'<div class="table-scroll" role="region" tabindex="0" aria-label="{escape(caption, quote=True)}">{html}</div>'
        return html
    # Only maintainer-owned corpus files are accepted; there is no HTML upload API.
    return mark_safe(''.join(render(node) for node in block["nodes"]))
