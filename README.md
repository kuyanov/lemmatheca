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
unsuccessfully and clear previous verification, signatures, and source lines,
preserving the module binding.

Verification reflects the last build. Rerun the command after changing Lean code
or node bindings, then commit the updated node JSON with the sources. The website
only reads these saved flags. See [formal/README.md](formal/README.md) for details.

## Layout

- [`corpus/`](corpus/README.md): entries, nodes, assets, taxonomy, and reading order.
- `app/`: Django settings, reader, and templates.
- [`formal/`](formal/README.md): the single active Lean project.
- `app/catalog/management/commands/build.py`: the Lean build command.
- `old/`: archived implementation, unused by the app and build command.

The backend is one Django app, `catalog`. Its `urls.py` and `views.py` serve
entries, nodes, and the node API. `entry_files.py` handles entry HTML, metadata,
navigation files, and asset checks; `node_files.py` handles node JSON, Lean source
files, and saving build results. `content.py` prepares reader data, `sources.py`
renders entry HTML, and `progress.py` computes verification summaries.

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

For deployment, set `DJANGO_DEBUG=0`, `DJANGO_SECRET_KEY`, and
`DJANGO_ALLOWED_HOSTS`, serve `config.wsgi:application` from `app/`, and serve the
output of `uv run python app/manage.py collectstatic` at `/static/`.
