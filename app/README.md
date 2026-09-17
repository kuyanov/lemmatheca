# Web app

A small, server-rendered Django site. It has 12 top-level areas, nested subareas,
breadcrumbs, and two mathematical notes with locally rendered equations and an SVG
illustration. There is no browser framework, bundler, CDN, or remote font service.
KaTeX loads only on mathematical article pages.

From the repository root, with Python 3.12–3.14 and uv installed:

```sh
uv sync --locked
uv run python app/manage.py runserver
```

Open <http://127.0.0.1:8000/>. No database setup or migrations are needed.
This is a local development server, not a production deployment configuration.

Missing HTML pages render `app/templates/404.html` with HTTP status 404 in both
development and production. `Development404Middleware` replaces Django's technical
404 when `DEBUG=True`, so you can preview the real error page locally. Debug
tracebacks for server errors remain available. Restart a server launched with
`--noreload` after changing Python code or settings.

Both examples are under **Combinatorics → Additive combinatorics → Sumsets**:

<http://127.0.0.1:8000/entries/thm-sumset-lower-bound/sumset-lower-bound/>

<http://127.0.0.1:8000/entries/thm-triple-sumset-lower-bound/triple-sumset-lower-bound/>

**Sumsets and translations** contains two definitions, two lemmas, a theorem, and
a question. **Adding three sets** contains a definition, a lemma, a theorem, and a
question. Each type is numbered independently, starting at 1 in each note.

References within a note show a local label such as **Lemma 1**. Cross-references
show names such as **Sumset lower bound** and link directly to the result's stable
anchor. A sticky return link leads back to the citing block. `from` and `at`
accept only known entry/block IDs; invalid inputs fall back to the source note
or the category. Returning to a question reopens its answer. Questions use native
HTML `details`, so answers and navigation need no JavaScript.

At the bottom of a note, **Next entry** continues through its primary subarea in
the same order as the category listing (currently the order in `entries.json`).
The button names its destination and is omitted on the last entry. It is separate
from the contextual return link used by mathematical citations.

The login and submit buttons open placeholder dialogs. They do not authenticate,
collect data, or submit proofs. The displayed lemmas, theorems, and counterexample answers have compiled Lean proofs
in `formal/Lemmatheca/Combinatorics/Additive/FiniteSumsets.lean`. The articles remain
drafts awaiting maintainer review and a full mathematical dependency audit.

## Editing

| File | Purpose |
| --- | --- |
| `examples/taxonomy.json` | Area titles, descriptions, and parent relationships |
| `examples/sumsets/entries.json` | Article metadata, ordered blocks, stable anchors, references, formal bindings |
| `app/catalog/content.py` | Seed content lookup and navigation |
| `app/catalog/views.py` | Home, area, article pages, and contextual return links |
| `app/catalog/templatetags/math_refs.py` | Contextual reference labels and anchored links |
| `app/templates/catalog/entry.html` | Shared article layout, contents, numbered block headings |
| `app/templates/catalog/blocks/` | Definitions, supporting results, and collapsible answers |
| `app/templates/catalog/proofs/sumset_lower_bound.html` | Human proof as HTML, with LaTeX delimiters |
| `app/templates/catalog/proofs/triple_sumset_lower_bound.html` | A second proof with a link to the lemma |
| `app/static/images/sumset-translation.svg` | Explanatory figure |
| `app/static/css/site.css` | Shared responsive styles and print layout |
| `app/static/js/site.js` | Placeholder dialogs |
| `app/static/js/math.js` | Math rendering configuration |
| `app/static/vendor/katex/` | Pinned KaTeX 0.18.7 scripts, fonts, and license |

Templates are trusted repository content. There is no user HTML upload or render
endpoint. Inline math uses `\(...\)` and display math uses `\[...\]`. KaTeX
generates accessible MathML alongside its visual layout. All referenced fonts
are self-hosted. Restart the server after editing the cached JSON seed data.

VS Code's workspace settings enable `html.format.templating` for its built-in
HTML formatter. Keep this enabled when using format-on-save: Django's `{% ... %}`
and `{{ ... }}` tags must remain on one line. Ordinary HTML and surrounding prose
can wrap. The template regression test catches split tags, including those that
would otherwise silently render as literal text.

The navigation uses the shared seed taxonomy; the sumset leaf contains both
example entries. Other leaves have an explicit empty state. Blocks can point to
existing mathematical JSON records or carry a formal binding inline. To cite a
block from trusted HTML, load `math_refs` and use:

```django
{% math_ref "nonempty-triple-sumset" %}
{% math_ref "sumset-lower-bound" entry_id="thm-sumset-lower-bound" from_block="triple-sumset-lower-bound" %}
```

`from_block` identifies the exact place to return to. Block IDs are stable even
when their display numbers change; preserve them when reordering content.

## Checks

```sh
uv run python app/manage.py check
uv run python app/manage.py test catalog
```

The tests check every category route and rendered navigation link, correct example
placement, citation/back navigation, entry counts, missing pages, empty leaves,
read-only placeholders, and local math assets. Lean is checked separately using
`cd formal && lake build`; the web app does not execute Lean on each request.
