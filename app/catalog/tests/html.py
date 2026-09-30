"""Inspect rendered behavior without depending on CSS classes or HTML formatting."""

from dataclasses import dataclass, field
from html.parser import HTMLParser


@dataclass(eq=False)
class Element:
    tag: str
    attrs: dict
    parent: "Element | None" = None
    parts: list = field(default_factory=list)

    @property
    def text(self):
        return " ".join("".join(self.parts).split())

    def ancestors(self):
        node = self.parent
        while node is not None:
            yield node
            node = node.parent


class HTML(HTMLParser):
    """A small index of tags, decoded attributes, ancestry, and normalized text."""

    void_tags = {"area", "base", "br", "col", "embed", "hr", "img", "input",
                 "link", "meta", "param", "source", "track", "wbr"}

    def __init__(self, source):
        super().__init__(convert_charrefs=True)
        self.root = Element("document", {})
        self.elements = []
        self.stack = [self.root]
        self.feed(source)
        self.close()

    @classmethod
    def from_response(cls, response):
        return cls(response.content.decode(response.charset))

    def handle_starttag(self, tag, attrs):
        element = Element(tag, dict(attrs), self.stack[-1])
        self.elements.append(element)
        if tag not in self.void_tags:
            self.stack.append(element)

    def handle_endtag(self, tag):
        for index in range(len(self.stack) - 1, 0, -1):
            if self.stack[index].tag == tag:
                del self.stack[index:]
                break

    def handle_data(self, data):
        for element in self.stack:
            element.parts.append(data)

    def find_all(self, tag=None, **attrs):
        return [element for element in self.elements
                if (tag is None or element.tag == tag)
                and all(key in element.attrs and element.attrs[key] == value
                        for key, value in attrs.items())]

    @property
    def hrefs(self):
        return {element.attrs["href"] for element in self.find_all("a")
                if "href" in element.attrs}

    @property
    def ids(self):
        return {element.attrs["id"] for element in self.elements if "id" in element.attrs}
