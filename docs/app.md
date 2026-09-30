# Web app

A read-only Django reader with server-rendered templates, plain CSS and JavaScript,
and bundled KaTeX. Repository files are the storage layer; there is no database,
migration step, frontend build, or review system in the app.

## Development

Run from the repository root using the Python version range in
[pyproject.toml](../pyproject.toml):

```sh
uv sync --locked
uv run python app/manage.py validate_corpus
uv run python app/manage.py build
uv run python app/manage.py test catalog
uv run python app/manage.py runserver
```

The build assumes the pinned Lean environment is installed. It updates node
verification and precomputes entry-list badges. Run it after editing entry HTML,
node bindings, or Lean code, and include the generated JSON in the change.
See the [corpus guide](corpus.md) and [Lean guide](formal.md).

Open <http://127.0.0.1:8000/>. Existing content files are read on each request;
there is no persistent catalog cache. Restart the server when adding an entry's
asset directory, since Django registers those directories at startup. Python edits
also require a restart when running with `--noreload`.

## Code layout and reads

The backend is a single Django app, `catalog`. Paths in this table are relative
to `app/`:

| File | Responsibility |
| --- | --- |
| `catalog/urls.py`, `catalog/views.py` | Entry, area, node, and API requests |
| `catalog/entry_files.py` | Direct entry and metadata reads, navigation files, local assets, summary writes |
| `catalog/node_files.py` | Direct node reads, installed Lean sources, proof-result preparation and writes |
| `catalog/files.py` | Shared JSON reading, request ID guards, atomic replacement of individual JSON files |
| `catalog/content.py` | Reader data, navigation, and block badges |
| `catalog/sources.py`, `catalog/equations.py` | Trusted HTML parsing, references, equation labels, and rendering |
| `catalog/progress.py` | Shared entry/block verification summaries |
| `catalog/proofs.py` | Lean build, declaration checks, and entry-summary generation |
| `catalog/statistics.py` | Build-time corpus totals and contributor count; direct snapshot read for the home page |
| `catalog/validation.py` | Offline metadata, HTML, reference, and hierarchy validation |
| `catalog/management/commands/` | Independent `validate_corpus` and Lean `build` commands |
| `catalog/tests/` | Reader, locality, summary, and Lean-build checks |

`app/config/` contains settings, URL inclusion, middleware, and the WSGI entry point.
`app/templates/` and `app/static/` contain presentation and
[local vendor assets](vendor.md).

Requests use `read_entry(id)`, `read_entry_metadata(id)`, and `read_node(id)`.
Home reads only taxonomy, reading order, and `corpus/statistics.json`. Area listings
and next-entry navigation use JSON metadata. In particular,
area pages use the saved `formalization` summary: they open neither entry HTML nor
node JSON. The small taxonomy and `area_entries.json` index provide area navigation
and reading order.

An entry page parses its own HTML and loads its linked nodes. It resolves referenced
entries only as needed for headings, anchors, and contextual return links, reusing
them within that request. Node pages load the requested node, its direct dependency
hints, and the defining source file. The single-node API reads only that node.
The full node API and build command enumerate nodes because they cover the collection.
Page requests never launch Lean or write corpus data. They trust corpus structure
validated offline; metadata ID matching, HTML consistency, reference existence, and
asset filesystem checks do not run in the reader. Checks on user-supplied record IDs
and area URLs still protect filesystem access and return 404 for invalid routes.

## Routes

| Route | Purpose |
| --- | --- |
| `/` | Area browsing, corpus counts, and entry/node verification totals |
| `/areas/<path>/` | Subareas and entries listed for the area |
| `/entries/<id>/` | Mathematical entry, references, questions, and block badges |
| `/node/<id>/` | Description, verification, Lean signature, dependencies, and source |
| `/api/node/` | All node records as JSON |
| `/api/node/<id>/` | One node record as JSON |

Reader and API routes accept GET and HEAD. There is no separate nodes index page.
The API adds reader URLs and source paths to the saved node fields. Verification
comes from the saved `verified` flag, not a live proof check or GitHub review state.

Node pages render plain-text descriptions with math, escape the Lean source, and
link declaration lines into the local source browser. The server is expected to
have project, dependency, and pinned toolchain sources installed; there is no
upstream-source fallback. Login is a presentation placeholder; the contribution
dialog links to the GitHub repository and explains how to get involved.

### Home-page statistics

`build` saves `corpus/statistics.json` after all proof checks and summary preparation
succeed. It records entry and node totals, verified totals, and the contributor
count. The home page counts all areas in the taxonomy, including subareas.
The statistics grid uses decorative icons for entries, nodes, areas, and
contributors, with verification totals shown as text.

Contributors are distinct author names from `git shortlog --summary HEAD`, which
respects `.mailmap`. They are repository commit authors, not the authors of cited
sources. Refresh the build after a new contributor's first commit; uncommitted
work is not part of Git history. CI checks out full history for this calculation.
Shallow checkouts and source archives retain the previous count, or display an
unknown count if no snapshot exists. Serving pages needs neither Git nor network
access. Before the first build, unavailable statistics display a dash.

## Checks

Run `uv run python app/manage.py validate_corpus` while editing. It is independent
of the build and permits missing or stale generated results. The optional
`--check-sources` checks installed source files without invoking Lean.

The [CI workflow](../.github/workflows/ci.yml) validates the corpus before installing
Lean, checks installed sources, runs the tests and `app/manage.py build`, and rejects
changes to committed node data or entry summaries. Build tests exercise a separate
temporary Lean project. Locality tests prevent area and detail views from loading
unrelated content.

To run only the isolated Lean-build tests:

```sh
uv run python app/manage.py test catalog.tests.test_build
```

### Response benchmark

To measure response times and corpus file reads:

```sh
uv run python app/manage.py shell -c 'from catalog.tests.benchmark_reader import benchmark; benchmark()'
```

This measures 50 responses per route after five warmup requests, with `DEBUG=False`.
It reports median and p95 milliseconds through Django's request handler, including
file reads and template rendering but excluding HTTP transport and static assets.

## Deployment

Validate the deployed corpus with `validate_corpus --check-sources` before serving it.
For deployment, set `DJANGO_DEBUG=0`, `DJANGO_SECRET_KEY`, and explicit
`DJANGO_ALLOWED_HOSTS`. Serve `config.wsgi:application` from `app/` with a production
WSGI server and run `uv run python app/manage.py collectstatic` to collect assets.
Serve the collected `staticfiles/` directory at `/static/`. Keep the corpus and
installed Lean sources available to the server. Entry source HTML and JSON are
read as content, not published as static files; only entry `assets/` directories
are registered for static serving.

## Scaling

Validation takes O(B + R) time, where B is the input byte count and R is the number
of references. Each entry JSON, entry HTML, and node JSON is opened once. It keeps
one HTML tree/record at a time, plus compact area parents, entry block IDs,
cross-entry links, and node hint edges. Memory therefore grows with these indexes
and the largest record, rather than all prose, signatures, or HTML trees. Graph
checks use iterative traversal, including for long chains and shared dependencies.
Optional source checks add the bytes of each distinct bound source file.

This removes validation from response time and keeps corpus checks suitable for a
growing collection. It does not make every other pipeline stage independent of
corpus size:

- Navigation reloads the taxonomy and area index. Subtree counts currently walk
  ancestor chains; a deep taxonomy can make this quadratic in the number of areas.
- Area pages load all listed metadata without pagination. Entry pages parse their
  HTML and directly referenced entries, and load their bound nodes. Node pages
  load direct hints and render the entire defining Lean source file.
- The full node API returns every record. Large consumers will need pagination.
- The build holds the registry, results, and pending summaries in memory and
  checks all declarations. Per-file writes are atomic, but publication of the
  entire corpus is not a single atomic operation.
- Static asset directories are scanned at process startup. Lean builds and the
  Python-version CI matrix remain more expensive than corpus validation.

The next steps at larger scale are precomputed reference/navigation indexes,
paginated listings/API results, and staged build output published as one snapshot.
Reader tests use representative pages; exhaustive corpus checks do not render the
whole collection. Keep the corpus immutable while validating and publishing it,
since validation is a check of the files it reads, not a persistent runtime cache.
