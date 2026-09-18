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

<http://127.0.0.1:8000/entries/thm-sumset-lower-bound/>

<http://127.0.0.1:8000/entries/thm-triple-sumset-lower-bound/>

**Sumsets and translations** contains two definitions, two lemmas, a theorem, and
a question. **Adding three sets** contains a definition, a lemma, two theorems, and
a question. Its final integer bound has a human proof and two pending helper
statements, demonstrating partial formalization. Each type is numbered
independently, starting at 1 in each note.

References within a note show a local label such as **Lemma 1**. Cross-references
show names such as **Sumset lower bound** and link directly to the result's stable
anchor. A sticky return link leads back to the citing block. `from` and `at`
accept only known entry/block IDs; invalid inputs fall back to the source note
or the category. Returning to a question reopens its answer. Questions use native
HTML `details`, so answers and navigation need no JavaScript.

At the bottom of a note, **Next entry** continues through its primary subarea in
the same order as the category listing, recorded in `corpus/reading-order.json`.
The button names its destination and is omitted on the last entry. It is separate
from the contextual return link used by mathematical citations.

The login and submit buttons open placeholder dialogs. They do not authenticate,
collect data, or submit proofs. Complete blocks bind either to compiled local Lean declarations
or existing mathlib declarations. The articles remain drafts awaiting maintainer review.

## Editing

| File | Purpose |
| --- | --- |
| `corpus/taxonomy.json` | Area titles, descriptions, and parent relationships |
| `corpus/reading-order.json` | Ordered entry IDs within each primary area |
| `corpus/entries/<id>/entry.html` | Complete human note, with stable section IDs and LaTeX |
| `corpus/entries/<id>/entry.json` | Authors, license, status, references, and Lean bindings |
| `corpus/entries/<id>/assets/` | Entry-local images and supplementary files |
| `app/catalog/content.py` | Corpus loading, validation, cache, and navigation |
| `app/catalog/sources.py` | HTML parsing and contextual reference/asset rendering |
| `app/catalog/equations.py` | Equation labels, numbering, and references |
| `app/catalog/metadata.py` | Metadata validation and derived formalization status |
| `app/catalog/lean.py` | Lean source path validation and contextual viewer links |
| `app/templates/catalog/entry.html` | Shared article layout, contents, numbering, navigation |
| `app/templates/catalog/lean_file.html` | General Lean file viewer |
| `app/static/css/site.css` | Shared responsive styles and print layout |
| `app/static/js/math.js` | Math rendering configuration |
| `app/static/vendor/katex/` | Pinned self-hosted KaTeX scripts, fonts, and license |

The [entry authoring guide](../docs/entry-sources.md) explains the HTML and JSON
format. Entry pages display authors, a linked license, optional source credits, and
a complete/partial/not-started formalization badge derived from every block.
Question blocks use the answer’s status. There are no per-entry version fields or
global external-lemma registry. Each block's `unformalized_dependencies` lists
Lean bindings (`declaration`, `module`, `source`) for unfinished helper proofs.
Verification details link both completed declarations and pending dependencies to
the same Lean file viewer, with the selected declaration's status and a return
link to the citing block. A nonempty list prevents `complete` status. Already
formalized mathlib lemmas do not belong on this list.

Open any project Lean file at `/lean/formal/<path>.lean/`, for example
`/lean/formal/Lemmatheca.lean/`. Pinned mathlib sources use
`/lean/Mathlib/<path>.lean/`. Files need not belong to an entry. The viewer displays
escaped source text, requires no extra JavaScript, and reads saved changes on each
request. It serves only `.lean` files within these source trees; hidden paths and
paths or symlinks escaping the trees return 404. Mathlib files also link to their
pinned GitHub source. Direct visits show a neutral file view; declaration status
and contextual return navigation appear only for a matching corpus binding.

Ordinary source links identify mathematical blocks by stable entry/block
IDs; local numbers and cross-entry return links are derived during rendering.
Corpus files are trusted repository content, not executable Django templates.
Public HTML uploads and sanitization remain outside this prototype.

Saving an existing HTML, JSON, or asset file invalidates the catalog cache.
Restart the server when adding a new entry's asset directory. Only `assets/`
folders are registered as static content; `collectstatic` includes them in a
production build without copying HTML or metadata into the public static tree.

VS Code's `html.format.templating` setting is still needed for shared application
Django templates. The mathematical HTML sources contain no Django template tags.

## Checks

```sh
uv run python app/manage.py check
uv run python app/manage.py validate_corpus
uv run python app/manage.py check_formalizations
uv run python app/manage.py test catalog
```

The tests check every category route and rendered navigation link, correct example
placement, citation/back navigation, entry counts, missing pages, empty leaves,
read-only placeholders, local math assets, source-order numbering, cache refresh,
invalid corpus records, equation references, tables, metadata credits, derived
badges, and entry-local asset collection. `check_formalizations` builds Lean and
checks local/mathlib bindings and axiom dependencies, then refreshes the reports.
Pending helpers are type-checked separately with `sorry` allowed; they are never
included among complete proofs.
The web app does not execute Lean on each request.
