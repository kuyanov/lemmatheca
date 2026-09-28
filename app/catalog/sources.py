"""Parse repository-owned HTML sources without executing Django templates."""

from collections import Counter
from dataclasses import dataclass, field
from html import escape
from html.parser import HTMLParser
from urllib.parse import urlencode, urlsplit

from django.templatetags.static import static
from django.urls import reverse
from django.utils.safestring import mark_safe


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


class SourceParser(HTMLParser):
    """A small tree for explicitly closed HTML; this is not an upload sanitizer."""

    def __init__(self):
        super().__init__(convert_charrefs=True)
        self.root = Element("root")
        self.stack = [self.root]

    def handle_starttag(self, tag, attrs):
        node = Element(tag, dict(attrs))
        self.stack[-1].children.append(node)
        if tag not in VOID_ELEMENTS:
            self.stack.append(node)

    def handle_startendtag(self, tag, attrs):
        self.handle_starttag(tag, attrs)
        if tag not in VOID_ELEMENTS:
            self.handle_endtag(tag)

    def handle_endtag(self, tag):
        self.stack.pop()

    def handle_data(self, data):
        self.stack[-1].children.append(data)


def parse_source(source, *, validate=False):
    if validate:
        from .validation import checked_source
        root, *_ = checked_source(source)
    else:
        parser = SourceParser()
        parser.feed(source)
        parser.close()
        root = parser.root
    from .equations import prepare_equations
    prepare_equations(root)
    captioned = {}
    for tag, caption_tag in (('figure', 'figcaption'), ('table', 'caption')):
        elements = (node for node in root.walk() if node.tag == tag)
        for number, element in enumerate(elements, 1):
            caption = next(node for node in element.children
                           if isinstance(node, Element) and node.tag == caption_tag)
            label = f'{tag.capitalize()} {number}'
            caption.children[:0] = [
                Element('span', {'class': f'{tag}-label'}, [label]), ' ']
            if element.attrs.get('id'):
                captioned[element.attrs['id']] = {'kind': tag, 'label': label}
    counts = Counter()
    blocks = []
    for node in root.children:
        if not isinstance(node, Element):
            continue
        block_id, kind = node.attrs['id'], node.attrs['data-kind']
        heading = next(child for child in node.children
                       if isinstance(child, Element) and child.tag == 'h2')
        formal_ids = node.attrs['data-formal'].split(
        ) if 'data-formal' in node.attrs else None
        counts[kind] += 1
        blocks.append({"id": block_id, "kind": kind, "formal_ids": formal_ids,
                       "title": heading.text().strip(),
                       "label": f"{kind.capitalize()} {counts[kind]}",
                       "nodes": [child for child in node.children if child is not heading]})
    return blocks, counts, captioned


def reference_target(href, entry_id, read_entry):
    """Resolve validated entry references; local non-block anchors stay unchanged."""
    url = urlsplit(href)
    if url.scheme or url.netloc:
        return None
    target = read_entry(url.path or entry_id)
    block = target["blocks_by_id"].get(url.fragment)
    return (target, block) if block else None


def render_block(block, entry, read_entry, expanded_answer=None):
    """Resolve references on demand and render without mutating source trees."""
    def render(node):
        if isinstance(node, str):
            return escape(node, quote=False)
        attrs = dict(node.attrs)
        children = node.children
        if node.tag == "a":
            href = attrs.get("href", "")
            link = urlsplit(href)
            if href.startswith("assets/"):
                relative = href.removeprefix("assets/")
                attrs["href"] = static(f"entries/{entry['id']}/{relative}")
                resolved = None
            else:
                resolved = reference_target(href, entry["id"], read_entry)
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
                if not node.text().strip():
                    children = [label]
            elif not link.scheme and not link.netloc and link.fragment in entry['captioned']:
                anchor = link.fragment
                target = entry['captioned'][anchor]
                query = urlencode({"from": entry["id"], "at": block["id"]})
                attrs.update(href=reverse('catalog:entry', args=[entry['id']]) + f'?{query}#{anchor}',
                             **{'class': f'{target["kind"]}-reference'})
                if not node.text().strip():
                    children = [target['label']]
        if node.tag == "img":
            relative = attrs["src"].removeprefix("assets/")
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
