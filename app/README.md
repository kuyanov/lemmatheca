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

After reviewing formal declarations, record approval with
`uv run python app/manage.py review --accept --node <id>` or
`uv run python app/manage.py review --accept --entry <id>`.
Add `--dry-run` to preview node-record changes. The command refreshes Lean checks
when necessary and stores hashes of the reviewed targets; it does not complete
unfinished proofs or publish the entry.
Replace `--accept` with `--retract` to clear existing approvals. Retraction supports
the same selectors and `--dry-run`, preserves verification evidence, and never runs Lean.

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
| `/formal/nodes/<id>/` | Mathematical description, checked statement, proof prerequisites, and source |

These endpoints allow GET and HEAD and work independently of the human corpus.
They never run Lean. The [formal-node contract](../formal/README.md#formal-nodes)
and [content model](../docs/content-model.md) define statuses and progress.

Every node includes a required plain-text `description`, also returned by both
API endpoints. Node pages render its mathematical notation using the local KaTeX
assets and escape HTML. The description precedes the checked signature; review and
verification dates remain visible. Proof dependencies expand to a compact list of
node links with adjacent statuses; each linked page shows its description. Full
source also expands on demand. Line links open the source browser, including direct
`#L<number>` links. Descriptions and dependency links wrap on narrow screens.

Description edits are editorial changes: they refresh page content without
invalidating Lean evidence or accepting/retracting a declaration review. The
checked signature remains separate and appears only with current verification.
