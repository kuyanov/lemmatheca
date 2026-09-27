# Web app

A read-only Django reader with server-rendered templates, plain CSS and JavaScript,
and bundled KaTeX. Repository files are the storage layer; there is no database,
migration step, frontend build, or review system in the app.

## Development

Run from the repository root using the Python version range in
[pyproject.toml](../pyproject.toml):

```sh
uv sync --locked
uv run python app/manage.py build
uv run python app/manage.py test catalog
uv run python app/manage.py runserver
```

The build assumes the pinned Lean environment is installed. It updates node
verification and precomputes entry-list badges. Run it after editing entry HTML,
node bindings, or Lean code, and include the generated JSON in the change.
See the [corpus guide](../corpus/README.md) and [Lean guide](../formal/README.md).

Open <http://127.0.0.1:8000/>. Existing content files are read on each request;
there is no persistent catalog cache. Restart the server when adding an entry's
asset directory, since Django registers those directories at startup. Python edits
also require a restart when running with `--noreload`.

## Code layout and reads

The backend is a single Django app, `catalog`:

| File | Responsibility |
| --- | --- |
| `catalog/urls.py`, `catalog/views.py` | Entry, area, node, and API requests |
| `catalog/entry_files.py` | Direct entry and metadata reads, navigation files, local assets, summary writes |
| `catalog/node_files.py` | Direct node reads, installed Lean sources, proof-result preparation and writes |
| `catalog/files.py` | Shared JSON reading, record IDs, atomic replacement of individual JSON files |
| `catalog/content.py` | Reader data, navigation, and block badges |
| `catalog/sources.py`, `catalog/equations.py` | Trusted HTML parsing, references, equation labels, and rendering |
| `catalog/progress.py` | Shared entry/block verification summaries |
| `catalog/proofs.py` | Lean build, declaration checks, and entry-summary generation |
| `catalog/management/commands/build.py` | Django build command |
| `catalog/tests/` | Reader, locality, summary, and Lean-build checks |

`config/` contains settings, URL inclusion, middleware, and the WSGI entry point.
`templates/` and `static/` contain presentation and local vendor assets.

Requests use `read_entry(id)`, `read_entry_metadata(id)`, and `read_node(id)`.
Home, area listings, and next-entry navigation use JSON metadata. In particular,
area pages use the saved `formalization` summary: they open neither entry HTML nor
node JSON. The small taxonomy and `area_entries.json` index provide area navigation
and reading order.

An entry page parses its own HTML and loads its linked nodes. It resolves referenced
entries only as needed for headings, anchors, and contextual return links, reusing
them within that request. Node pages load the requested node, its direct dependency
hints, and the defining source file. The single-node API reads only that node.
The full node API and build command enumerate nodes because they cover the collection.
Page requests never launch Lean or write corpus data.

## Routes

| Route | Purpose |
| --- | --- |
| `/` | Area browsing and a featured entry |
| `/areas/<path>/` | Subareas and entries listed for the area |
| `/entries/<id>/` | Mathematical entry, references, questions, and block badges |
| `/formal/nodes/<id>/` | Description, verification, Lean signature, dependencies, and source |
| `/api/formal/nodes/` | All node records as JSON |
| `/api/formal/nodes/<id>/` | One node record as JSON |

Reader and API routes accept GET and HEAD. There is no separate nodes index page.
The API adds reader URLs and source paths to the saved node fields. Verification
comes from the saved `verified` flag, not a live proof check or GitHub review state.

Node pages render plain-text descriptions with math, escape the Lean source, and
link declaration lines into the local source browser. The server is expected to
have project, dependency, and pinned toolchain sources installed; there is no
upstream-source fallback. Login and contribution controls are presentation placeholders.

## Checks and deployment

The [CI workflow](../.github/workflows/ci.yml) installs the pinned Lean environment,
runs the tests, runs `app/manage.py build`, and rejects changes to committed node
data or entry summaries. Build tests exercise a separate temporary Lean project.
Locality tests prevent area and detail views from loading unrelated content.

The [root README](../README.md#checks) documents the optional response benchmark.

For deployment, set `DJANGO_DEBUG=0`, `DJANGO_SECRET_KEY`, and explicit
`DJANGO_ALLOWED_HOSTS`. Serve `config.wsgi:application` from `app/` with a production
WSGI server and run `uv run python app/manage.py collectstatic` to collect assets.
Serve the collected `staticfiles/` directory at `/static/`. Keep the corpus and
installed Lean sources available to the server. Entry source HTML and JSON are
read as content, not published as static files; only entry `assets/` directories
are registered for static serving.
