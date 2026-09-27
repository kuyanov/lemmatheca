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
The reader retains the original styles, table layout, contents sidebar, next-entry
links, and contextual back links (including reopening question answers).
Formal nodes open from entry badges at `/formal/nodes/<id>/`; there is no separate
Nodes section. Node pages show verification, the mathematical description, the
Lean declaration, and a source browser with declaration line links.
There is no database, migration step, or frontend build. KaTeX is bundled locally.
The read-only `/api/formal/nodes/` endpoints remain available.

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

The single `module` field identifies the declaration's defining module and is
used for both imports and source browsing. The build refreshes it from Lean and
saves the declaration signature and source line. Build or declaration errors exit
unsuccessfully without writing any node JSON; previous verification data stays intact.

Verification reflects the last successful build. Rerun the command after changing Lean code
or node bindings, then commit the updated node JSON with the sources. The website
only reads these saved flags. See [formal/README.md](formal/README.md) for details.

## Layout

- [`corpus/`](corpus/README.md): entries, nodes, assets, taxonomy, and `area_entries.json`.
- `app/`: Django settings, reader, and templates.
- [`formal/`](formal/README.md): the single active Lean project.
- `app/catalog/management/commands/build.py`: the Lean build command.
- `old/`: archived implementation, unused by the app and build command.

The backend is one Django app, `catalog`. Its `urls.py` and `views.py` serve
entries, nodes, and the node API. `entry_files.py` handles entry HTML, metadata,
navigation files, and asset checks; `node_files.py` handles node JSON, Lean source
files, and saving build results. `content.py` prepares reader data, `sources.py`
renders entry HTML, and `progress.py` computes verification summaries.

Requests read individual records through `read_entry(id)`, `read_entry_metadata(id)`,
and `read_node(id)`. `corpus/area_entries.json` lists each area's entries in reading
order and supplies navigation counts. Home and next-entry links need metadata only;
entry pages load their own nodes and directly referenced entries, while node pages
load only their node and direct dependency hints. Area badges read the entries and
nodes listed in that area. Repeated references are reused within a response; there
is no catalog cache to invalidate. The full node API and build command still read
all nodes because their output covers the whole collection.

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

CI runs the suite, builds the corpus proofs, and checks that committed proof data matches.

To measure response times and corpus file reads:

```sh
uv run python app/manage.py shell -c 'from catalog.tests.benchmark_reader import benchmark; benchmark()'
```

This measures 50 responses per route after five warmup requests, with `DEBUG=False`.
It reports median and p95 milliseconds through Django's request handler, including
file reads and template rendering but excluding HTTP transport and static assets.

Local measurements before and after switching to direct reads (3 entries, 188 nodes):

| Response | Median before → after (ms) | Corpus reads before → after |
| --- | ---: | ---: |
| Home | 16.917 → 0.366 | 203 → 3 |
| Logic and foundations area | 16.437 → 0.362 | 206 → 2 |
| Set theory entry list | 16.291 → 16.155 | 205 → 196 |
| Sets and maps entry | 20.366 → 12.692 | 201 → 132 |
| Ordered sets entry | 18.851 → 10.061 | 201 → 8 |
| Set-subset-transitive node | 34.754 → 26.648 | 188 → 2 |
| Set-subset-transitive API | 7.922 → 0.134 | 188 → 1 |

The set-theory list currently contains every entry, so its badges still need all
their nodes. Entry and node detail costs depend on their content and direct
references, not on unrelated entries or nodes elsewhere in the corpus.

For deployment, set `DJANGO_DEBUG=0`, `DJANGO_SECRET_KEY`, and
`DJANGO_ALLOWED_HOSTS`, serve `config.wsgi:application` from `app/`, and serve the
output of `uv run python app/manage.py collectstatic` at `/static/`.
