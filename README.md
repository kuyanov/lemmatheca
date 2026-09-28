# Lemmatheca

A library of mathematical entries and formal nodes, served by a small Django app.
The corpus is stored in files; formal proofs share one Lean project.
Reviews happen on GitHub and are not tracked by the app.

## Run

With Python 3.12–3.14 and uv installed:

```sh
uv sync --locked
uv run python app/manage.py runserver
```

Open <http://127.0.0.1:8000/> and browse the area hierarchy to find entries.
The reader provides a contents sidebar, next-entry links, and contextual back links
that can reopen question answers.
Formal nodes open from entry badges at `/node/<id>/`; there is no separate
Nodes section. Node pages show verification, the mathematical description, the
Lean declaration, and a source browser with declaration line links.
There is no database, migration step, or frontend build. KaTeX is bundled locally.
The read-only node API is documented in [app/README.md](app/README.md).

## Verification

With the pinned Lean environment available:

```sh
uv run python app/manage.py build
```

The command builds the project and updates the single `verified` status flag in
every node JSON. A node is **Verified** when its Lean declaration checks without
`sorry`, including in any transitive dependency. Otherwise it is **Not verified**.
Additional axioms beyond Lean's usual logical foundations also prevent verification.
Definitions use the same check. Unbound nodes remain not verified.
Entry and block badges summarize the proportion of verified nodes.
The build also saves each entry's derived `formalization` summary in `entry.json`,
so area listings need no HTML parsing or node reads. Rerun it after changing entry
HTML or formal node bindings, and commit the updated entry metadata as well.

The single `module` field identifies the declaration's defining module and is
used for both imports and source browsing. The build refreshes it from Lean and
saves the declaration signature and source line. Build or declaration errors exit
unsuccessfully without writing node JSON or entry summaries; previous data stays intact.
Entry summaries are also validated before any results are saved.

Verification reflects the last successful build; serving a page does not check
whether Lean sources have changed. Rerun the command after changing Lean code or
bindings, then commit the updated node JSON and entry summaries with the sources.
See [formal/README.md](formal/README.md) for the verification rules.

## Layout

- [`corpus/`](corpus/README.md): entries, nodes, assets, taxonomy, and `area_entries.json`.
- [`app/`](app/README.md): Django settings, reader, templates, and local assets.
- [`formal/`](formal/README.md): the single active Lean project.
- `app/catalog/management/commands/build.py`: the Lean build command.
- [`prompts/`](prompts/README.md): reusable entry authoring, review, and proving prompts.

The backend is one Django app, `catalog`. Its `urls.py` and `views.py` serve
entries, nodes, and the node API. `entry_files.py` handles entry HTML, metadata,
navigation files, and asset checks; `node_files.py` handles node JSON, Lean source
files, and saving build results. `content.py` prepares reader data, `sources.py`
renders entry HTML, and `progress.py` computes verification summaries.

Requests read individual records through `read_entry(id)`, `read_entry_metadata(id)`,
and `read_node(id)`. `corpus/area_entries.json` lists each area's entries in reading
order and supplies navigation counts. Home and next-entry links need metadata only;
entry pages load their own nodes and directly referenced entries, while node pages
load only their node and direct dependency hints. Area pages read only the listed
entries' JSON metadata, including their precomputed badges. Repeated references
are reused within a response; there is no server-side catalog cache to invalidate.
The full node API and build command read all nodes because their output covers
the whole collection.

## Contributing

Use the [authoring workflow](prompts/README.md) to choose sources, draft an entry,
review its mathematics, prepare formal bindings, review their correspondence, and
prove the selected statements. The [corpus guide](corpus/README.md) defines HTML,
metadata, links, and block mappings; the [Lean guide](formal/README.md) covers nodes
and proofs.

Reviews and their decisions belong in GitHub pull requests. The app stores no
entry or node approvals, review hashes, or review dates. A verified Lean declaration
still needs human review of its correspondence to the prose. Keep entry and block
IDs stable, reuse existing nodes where they cover the same mathematics, and include
generated JSON changes in the pull request.

After source or binding changes, run the build before the tests so stored entry
summaries match the edited content. Inspect the rendered entry and linked node
pages as part of review. Keep experiment logs and temporary proof attempts outside
corpus metadata.

## Checks

```sh
uv run python app/manage.py test catalog
```

Tests live in `app/catalog/tests/` and require the pinned Lean environment.
They check pages, corpus links, verification badges, and result persistence.
The build command is also exercised in an isolated Lean project with completed
proofs, direct and inherited `sorry`, unsupported axioms, missing declarations,
and failed builds. To run just those build tests:

```sh
uv run python app/manage.py test catalog.tests.test_build
```

CI runs the suite, builds the corpus proofs, and checks that committed proof data
and entry summaries match.

To measure response times and corpus file reads:

```sh
uv run python app/manage.py shell -c 'from catalog.tests.benchmark_reader import benchmark; benchmark()'
```

This measures 50 responses per route after five warmup requests, with `DEBUG=False`.
It reports median and p95 milliseconds through Django's request handler, including
file reads and template rendering but excluding HTTP transport and static assets.

For deployment, set `DJANGO_DEBUG=0`, `DJANGO_SECRET_KEY`, and
`DJANGO_ALLOWED_HOSTS`, serve `config.wsgi:application` from `app/`, and serve the
output of `uv run python app/manage.py collectstatic` at `/static/`.
