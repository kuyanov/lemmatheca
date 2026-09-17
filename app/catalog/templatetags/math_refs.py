"""References use IDs internally and short, contextual names for readers."""

from urllib.parse import urlencode

from django import template
from django.urls import reverse
from django.utils.html import format_html

from catalog.content import entries

register = template.Library()


@register.simple_tag(takes_context=True)
def math_ref(context, block_id, *, entry_id=None, from_block=None):
    source = context["entry"]
    target = entries()[entry_id or source["id"]]
    block = target["blocks_by_id"][block_id]
    if target["id"] == source["id"]:
        url = f"#{block_id}"
        label = block["label"]
    else:
        # Fail on broken source anchors while rendering rather than silently
        # returning a reader to the wrong part of a paper.
        source["blocks_by_id"][from_block]
        query = urlencode({"from": source["id"], "at": from_block})
        url = reverse("catalog:entry", args=[target["id"], target["slug"]])
        url += f"?{query}#{block_id}"
        label = block["title"]
    return format_html(
        '<a class="lemma-reference" href="{}" title="{} — {} · {}">{}</a>',
        url, block["label"], block["title"], target["title"], label,
    )
