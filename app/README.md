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

The [CI workflow](../.github/workflows/ci.yml) runs the catalog tests and corpus
validation on pushes, pull requests, and manual runs across Python 3.12–3.14.
It installs dependencies from `uv.lock` and uses committed verification evidence,
so the jobs do not need a Lean installation.

After reviewing node descriptions against their Lean declarations, record approval
with
`uv run python app/manage.py review --accept --node <id>` or
`uv run python app/manage.py review --accept --entry <id>`.
Add `--dry-run` to preview node-record changes. The command refreshes Lean checks
for the selected nodes' modules when necessary and stores hashes of the reviewed
targets; it does not complete unfinished proofs or publish the entry.
Whole-entry acceptance records the linked nodes' approvals; entry text and mapping
coverage still need separate Git review.
Replace `--accept` with `--retract` to clear existing approvals. Retraction supports
the same selectors and `--dry-run`, preserves verification evidence, and never runs Lean.

Tests use small isolated fixtures and one smoke test of the current corpus.
Lean command tests mock Lean output; run `check_formalizations` to check
actual proofs in stale modules, or add `--force` to recheck every registered module.
Module evidence includes transitive local source imports and a shared revision hash
for installed mathlib/Lake packages. Those packages are assumed immutable, so
freshness checks read revisions without hashing their sources. Rechecking a stale
module still traverses its imports, builds it, and runs Lean declaration probes.
Unrelated modules retain their evidence and
check dates after local edits or failures elsewhere; environment-pin and installed
package-revision changes invalidate checks using that environment.
The report uses direct path-to-hash maps, with separate project-module records and
one Mathlib audit record. `--module Mathlib` selects that audit; every direct library
binding is still checked through its specified import.

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
source also expands on demand. For installed sources, line links open the source
browser, including direct `#L<number>` links. When a Lean or mathlib source is not
installed, the line number is plain text and the pinned upstream link opens that
line. Descriptions and dependency links wrap on narrow screens.

The evidence panel uses two states per item: green **Reviewed on …** or amber
**Under review** for declaration approval, and green **Verified on …** or amber
**Not verified** for Lean verification. Verification requires valid evidence of a
complete proof, independently of review approval; merely running a check does not
mark a proof with `sorry` as verified. Stale evidence shows **Not verified**, while
an approval matching the last checked statement retains **Reviewed on …**.
This historical comparison does not make the API's
`review_current` true or expose a current target hash. The overall node badge and
API status still identify the specific next step.

Description edits invalidate correspondence approval immediately while retaining
Lean evidence. Manual proof-dependency edits retain both, and a listed prerequisite's
status does not affect the node's completion. Node ID renames, module moves, and environment
changes require Lean rechecking, then retain approval if the target hash is unchanged.
The checked signature remains separate and appears only with current verification.
The reader computes review targets from
current descriptions and checked semantic declaration hashes, without running Lean.
