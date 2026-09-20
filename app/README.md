# Web app

A read-only Django reader with server-rendered templates, plain CSS/JavaScript,
and local KaTeX. Mathematical content lives in repository files; no database is
needed. Login and contribution buttons are placeholders.

## Development

Run from the repository root:

```sh
uv sync --locked
uv run python app/manage.py runserver
uv run python app/manage.py validate_corpus
uv run python app/manage.py test catalog
```

Tests use small isolated fixtures and one smoke test of the current corpus.
Lean command tests mock Lean output; run `check_formalizations` to check
actual proofs.

Open <http://127.0.0.1:8000/>. For another device on your local network, set
`DJANGO_ALLOWED_HOSTS` to include the host address and run the development server
with `0.0.0.0:8000`. Production requires `DJANGO_DEBUG=0`, a `DJANGO_SECRET_KEY`,
explicit allowed hosts, static-file serving, and a production WSGI server.

The website can run without Lean installed. Keep the tracked `corpus/` and
`formal/` files, including verification reports and the Lake manifest. See
[Lean setup](../formal/README.md) when you need to run formal checks.

## Code layout

- `catalog/`: corpus loading, validation, rendering, reader views, and tests.
- `formalization/`: formal node storage, statuses, source locations, and API/views.
- `config/`: Django settings, routing, and development error handling.
- `templates/` and `static/`: shared presentation and self-hosted KaTeX.

Reader routes are `/`, `/areas/<path>/`, and `/entries/<id>/`. File changes are
picked up on the next request. Restart the server when adding an entry's asset
directory, or after Python changes when using `--noreload`.

## Formal API

| Route | Purpose |
| --- | --- |
| `/api/formal/nodes/` | Node records with derived statuses |
| `/api/formal/nodes/<id>/` | One node as JSON |
| `/formal/nodes/<id>/` | Node status, dependencies, and Lean source |

These endpoints allow GET and HEAD and work independently of the human corpus.
They never run Lean. The [formal-node contract](../formal/README.md#formal-nodes)
and [content model](../docs/content-model.md) define statuses and progress.
