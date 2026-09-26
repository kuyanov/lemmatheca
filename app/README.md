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
These jobs install dependencies from `uv.lock` and use committed verification
evidence without installing Lean. A separate job installs the pinned Lean
environment, builds the project, and runs `check_formalizations --force` for all
registered declarations.

After reviewing node descriptions against their Lean declarations, record approval
with
`uv run python app/manage.py review --accept --node <id>` or
`uv run python app/manage.py review --accept --nodes-from-entry <id>`.
Add `--dry-run` to preview node-record changes. The command refreshes Lean checks
for the selected nodes' modules when necessary and stores hashes of the reviewed
targets; it does not complete unfinished proofs or publish the entry.
`--nodes-from-entry` reviews each distinct linked node and leaves the entry's
editorial status unchanged.
Replace `--accept` with `--retract` to clear existing approvals. Retraction supports
the same selectors and `--dry-run`, preserves verification evidence, and never runs Lean.

For a separate entry review, use
`uv run python app/manage.py review --accept --entry <id>` after checking the
mathematics, rendered page, and complete block-to-node coverage. This validates the
corpus, requires every block to have a mapping and every linked node to have a
declaration, then records a review hash and timestamp. Empty mappings are allowed.
The Draft badge disappears from the entry page and area listing, together with the
entry's review note. Unfinished proofs and unapproved nodes are allowed; node
approvals and verification evidence stay unchanged, and Lean is never run.
`review --retract --entry <id>` restores draft status, even if the entry's HTML is
currently invalid or mappings are unfinished. Both actions support `--dry-run`.
Entry status is derived: a matching approval is `final`; otherwise it is `draft`.
The hash covers entry metadata, HTML (including node IDs), assets, and linked node
descriptions. It excludes the review record, declarations, other node fields, and
Lean evidence. Entry or linked-description edits restore the
Draft badge automatically. New entries use `review: null`, with no stored `status`.
See the [review workflow](../README.md#recording-reviews).

Tests use small isolated fixtures and one smoke test of the current corpus.
Lean command tests mock Lean output; run `check_formalizations` to check
actual proofs in stale modules, or add `--force` to recheck every registered module.
Module evidence includes transitive local source imports and a shared revision hash
for installed mathlib/Lake packages. They must be clean Git checkouts: freshness
checks read revisions and Git status, without hashing package sources in Python.
Dirty checkouts and source archives invalidate affected evidence and block checks,
including cached reuse. Ignored build output is allowed; uncommitted project
proofs are checked normally. Rechecking a stale
module still traverses its imports, builds it, and runs Lean declaration probes.
Unrelated modules retain their evidence and
check dates after local edits or failures elsewhere; environment-pin and installed
package-revision changes invalidate checks using that environment.
The report uses direct path-to-hash maps, with a separate record for every project
or Mathlib import module. `--module Mathlib.Data.Setoid.Basic` selects just that
module; `--module Mathlib` selects all registered Mathlib imports, each checked
independently. Binding errors leave unrelated modules' evidence and dates intact.
Format-7 shared audits migrate to format 8 with their original snapshots, input
hashes, dates, and any failure history; migration does not accept node reviews.

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

`catalog/reviews.py` hashes entry content and linked descriptions and guards entry
approval writes against concurrent edits to those inputs. Entry review checks
text-to-description correspondence; node review checks descriptions against Lean.

The formalization layer separates registry validation and progress (`nodes.py`),
verification reports and freshness (`verification.py`), Lean sources and environment
inspection (`lean.py`), and correspondence hashes (`reviews.py`). Registry-only
callers use `read_registry`; page/API callers use `load_nodes` to attach derived
review and verification state. Proof dependencies are validated independently of
those states.

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
Failed checks also retain that historical review label: the report saves the last
successful snapshots and their original input hashes separately from the latest
failure. Failed groups remain unverified and are retried by the next check.
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
