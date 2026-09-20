# Web app

A small, server-rendered Django site. The current reader has one top-level area,
**Logic and foundations**, its **Set theory** subarea, and one active entry.
Equations and SVG illustrations are rendered locally. There is no browser
framework, bundler, CDN, or remote font service.
KaTeX loads only on mathematical article pages.

For the current phase, the app is a reader and preview tool for AI-formalization
experiments and a growing standard-mathematics corpus. It does not run models,
measure their costs, or manage submissions. Public contribution features come
later; see the [experiment plan](../docs/formalization-experiments.md).
`DATABASES` is empty, and authentication, sessions, and admin are not installed.
Reader routes are `/`, `/areas/<path>/`, `/entries/<id>/`,
and `/formal/nodes/<id>/`. The separate formal JSON API is described below;
search and a human-corpus API are not implemented.

From the repository root, with Python 3.12–3.14 and uv installed:

```sh
uv sync --locked
uv run python app/manage.py runserver
```

Open <http://127.0.0.1:8000/>. No database setup or migrations are needed.
This is a local development server, not a production deployment configuration.

For a web-only deployment, keep the tracked `corpus/` and `formal/` directories,
including `formal/checks/` and `formal/lake-manifest.json`. Lean and the mathlib
checkout are optional for serving pages. Node readiness uses the committed
`formal/checks/nodes.json` report and current node/source/environment fingerprints.
Missing local Lemmatheca sources fail validation. If external dependencies are not
installed, their committed evidence is trusted against the pinned environment;
installed sources are checked for changes. Regenerate reports after formal edits.

`formal/.lake/` is ignored by Git, so `git pull` does not install mathlib. When a
referenced mathlib file is absent, the node page shows its pinned GitHub link
and retains the return link to the entry. To install local sources and compiled
dependencies for verification, follow the [Lean setup](../formal/README.md).
After deploying application changes, restart the web process. Run
`uv run python app/manage.py validate_corpus` to check the deployed corpus.

Missing HTML pages render `app/templates/404.html` with HTTP status 404 in both
development and production. `Development404Middleware` replaces Django's technical
404 when `DEBUG=True`, so you can preview the real error page locally. Debug
tracebacks for server errors remain available. Restart a server launched with
`--noreload` after changing Python code or settings.

The earlier sumset and Erdős–Szekeres examples are in `corpus/backup/`. They
are excluded from live entry routes and static files. The active taxonomy is in
`corpus/taxonomy.json`; `taxonomy_complete.json` is reference material only.

**Sets and maps: a first guide**, under **Logic and foundations → Set theory**,
starts with basic notation and conventions and develops set operations, maps,
images, preimages, and inverses. Its 21 blocks include four questions with
collapsible answers and an entry-local map diagram. Allow about 40 minutes to
read it. Definition 1 has a progress badge opening nine nodes. Unreviewed nodes
show **Pending review**, while approved nodes still need checked proofs and ready
dependencies. The new theorem proofs are unfinished. The other
20 blocks are **Formalization not started** for a later measured pass:

<http://127.0.0.1:8000/entries/sets-and-maps/>

The contents menu starts beside the entry header on desktop. Long outlines have
a separate, keyboard-focusable scroll area.
Its height fits the visible viewport even near the page header; scrolling inside
it does not scroll the article. On narrow screens the contents remain in page flow.

References within a note show a local label such as **Lemma 1**. Cross-references
show names such as **Sumset lower bound** and link directly to the result's stable
anchor. Both local and cross-entry references show a sticky return link to the citing block.
Figures are numbered automatically and their links provide the same return navigation. `from` and `at`
accept only known entry/block IDs; invalid inputs fall back to the source note
or the category. Returning to a question reopens its answer. Questions use native
HTML `details`, so answers and navigation need no JavaScript.
The top return bar appears only after following a reference; ordinary visits go
straight from the breadcrumbs to the entry header. Bottom back links remain.
Area breadcrumbs stay visible while scrolling an entry. When a reference return
bar is present, it shares the sticky strip beneath them. The outline and anchor
offsets follow the strip's height, including when its text wraps on a small screen.

At the bottom of a note, **Next entry** continues through its primary subarea in
the same order as the category listing, recorded in `corpus/reading-order.json`.
The button names its destination and is omitted on the last entry. It is separate
from the contextual return link used by mathematical citations.

The login and submit buttons open placeholder dialogs. They do not authenticate,
collect data, or submit proofs. Blocks can link to local or mathlib formal nodes. The articles remain drafts awaiting maintainer review.
Drafts are visible in this prototype; there is no publication gate or accepted-only
catalog. Review and inclusion are currently manual repository operations.

## Formal API

The formal layer lives in `app/formalization/` and reads `formal/nodes/<id>.json`.
It shares the Django process but does not require the human corpus to be loaded.

| Route | Purpose |
| --- | --- |
| `/api/formal/nodes/` | JSON list of node records, derived statuses, labels, and links |
| `/api/formal/nodes/<id>/` | One node as JSON; unknown IDs return 404 |
| `/formal/nodes/<id>/` | Node page with source, inferred declaration line, and dependencies |

These endpoints allow GET and HEAD only. Writes, planning workers, and autonomous
proving are later work. Models and Lean builds do not run during page requests.
Node IDs resolve from block HTML `data-formal`; no formal or reference metadata
lives in entry JSON. See [mapping rules](../corpus/README.md#block-to-node-mapping)
and the [node schema](../formal/README.md#formal-nodes).

A compact badge beside each block title shows Not started, N/A, Complete, or a
percentage. Linked badges are native `details` disclosures containing node IDs
with status labels and complete/pending icons. Nodes distinguish missing
declarations, review, verification, proof, and dependency work; see the
[node statuses](../formal/README.md#formal-nodes). The badge gives the status
without a duplicate reason paragraph. A node page can return to the referring block and
reopen its question answer. Entry badges show Not started, Partial, or Complete,
without a percentage; an entirely not-applicable entry shows N/A. Entry totals
deduplicate nodes and report unmapped blocks separately in the tooltip.
Node pages show their source and formalization status together.

## Editing

| File | Purpose |
| --- | --- |
| `corpus/taxonomy.json` | Active area titles, descriptions, and parent relationships |
| `corpus/taxonomy_complete.json`, `corpus/backup/` | Inactive reference taxonomy and archived examples |
| `corpus/reading-order.json` | Ordered entry IDs within each primary area |
| `corpus/entries/<id>/entry.html` | Complete human note, with stable section IDs and LaTeX |
| `corpus/entries/<id>/entry.json` | Based-on citations, editorial status, areas, and reading information |
| `corpus/entries/<id>/assets/` | Entry-local images and supplementary files |
| `app/catalog/content.py` | Corpus loading, validation, cache, and navigation |
| `app/catalog/sources.py` | HTML parsing and contextual reference/asset rendering |
| `app/catalog/equations.py` | Equation labels, numbering, and references |
| `app/catalog/metadata.py` | Ordinary entry metadata validation |
| `app/catalog/lean.py` | Safe Lean source path resolution |
| `app/formalization/` | Node registry, readiness, source locations, pages, and read-only API |
| `formal/nodes/<id>.json` | Declaration/module, dependencies, and statement review |
| `app/templates/catalog/entry.html` | Shared article layout, contents, numbering, navigation |
| `app/templates/catalog/_bibliography.html`, `_citation.html` | Compact source citations and additional-source disclosure |
| `app/templates/formalization/node.html` | Formal node status, dependencies, and Lean source |
| `app/static/css/site.css` | Shared responsive styles and print layout |
| `app/static/js/math.js` | Math rendering configuration |
| `app/static/vendor/katex/` | Pinned self-hosted KaTeX scripts, fonts, and license |

The [entry authoring guide](../docs/entry-sources.md) explains the HTML and JSON
format. Entry pages display the first **Based on:** citation as authors, linked
title, and year; further sources are collapsed. Full publication details remain
in JSON. Mathematical links are read and checked directly from HTML. Questions
map their answers, and empty formal mappings mean nothing needs formalization.

Read Lean source directly on `/formal/nodes/<id>/`; there is no separate file
viewer. Source text is escaped, and declaration lines are highlighted when
inferable. Hidden paths, non-Lean files, and escaped symlinks are rejected.
Missing mathlib files have a pinned GitHub fallback. Return context is validated
against the referring block's node IDs. Setting `reviewed: true` accepts a
statement without invalidating its Lean evidence. A node becomes complete only
when its evidence is current and its dependencies are ready; unfinished proofs
show **Proof pending** after review.

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

Tests use the active corpus, isolated archived human-text fixtures, and temporary
formal-node fixtures. They cover reference/back navigation, equations, figures,
tables, metadata validation, cache invalidation, progress aggregation, node API
and source pages, missing mathlib checkouts, and proof/dependency readiness.
`check_formalizations` builds registered modules and checks declarations and
transitive axioms. `sorryAx` always means pending. It currently checks Definition
1's nine nodes. An empty registry needs no Lean installation; historical reports
are left unchanged.

The test suite uses Django's test runner; no separate pytest/Ruff or CI workflow
is configured. Successful checks do not certify AI translation quality or
correspondence with the human proof strategy.
