# Project architecture

This document describes the implementation in this checkout. The immediate work
is AI formalization evaluation and corpus construction; public submissions and
research-agent infrastructure are later stages. See the
[experiment and corpus plan](formalization-experiments.md) for that sequence.

## Current tools

| Layer | Implementation |
| --- | --- |
| Python environment | Python 3.12–3.14, uv, committed `uv.lock` |
| Web application | Django 5.2 series, server-rendered templates; only `catalog` and staticfiles installed |
| Persistent mathematical source | Git-tracked HTML, JSON, images, and Lean files |
| Browser | Plain CSS, small local JavaScript, pinned self-hosted KaTeX and fonts |
| Formal environment | Lean 4.34.0, Lake, mathlib pinned by `lakefile.toml` and `lake-manifest.json` |
| Validation and verification | Django management commands; Lean builds run locally on demand |
| Tests | Django's test runner, plus manual browser checks |

`DATABASES` is empty. Accounts, sessions, Django admin, PostgreSQL, task queues,
AI model integrations, search services, and a human-corpus API are not implemented.
The separate read-only formal-node API is available in the same Django process.
There is no configured Ruff/pytest or CI pipeline. Dependency pins already exist;
upgrade Lean and mathlib together deliberately rather than during an experiment.

## Existing folder layout

```text
lemmatheca/
├── README.md
├── docs/                           # Architecture, authoring, experiments, verification
├── app/
│   ├── manage.py
│   ├── config/                     # Settings, root URLs, WSGI, development 404 middleware
│   ├── catalog/                    # File loader, validators, rendering, views, tests
│   │   └── management/commands/    # validate_corpus, check_formalizations, review
│   ├── formalization/              # Node registry, readiness, source locations, API/views
│   ├── templates/                  # Shared Django layout and reader pages
│   └── static/                     # CSS, small JS, self-hosted vendor/katex
├── corpus/
│   ├── taxonomy.json              # Working subjects only
│   ├── taxonomy_complete.json     # Broader taxonomy, not loaded by the reader
│   ├── backup/<entry-id>/          # Archived examples, not served as entries
│   ├── reading-order.json
│   └── entries/<entry-id>/
│       ├── entry.json              # Identity, bibliography, areas, editorial/reading metadata
│       ├── entry.html              # Human mathematical sections, without Django tags
│       └── assets/                 # Optional entry-local illustrations/supplements
├── formal/
│   ├── lean-toolchain
│   ├── lakefile.toml
│   ├── lake-manifest.json
│   ├── Lemmatheca.lean
│   ├── Lemmatheca/
│   │   ├── ReviewChecks.lean       # Review snapshots and declaration locations
│   │   ├── SetTheory.lean          # Reusable set/map library
│   │   ├── Entry/
│   │   │   ├── SetsAndMaps.lean    # Imports this entry's examples
│   │   │   └── SetsAndMaps/        # Namespace Lemmatheca.Entry.SetsAndMaps
│   │   │       ├── SetsAndElements.lean
│   │   │       ├── SetOperations.lean
│   │   │       └── Maps.lean
│   │   └── Combinatorics/Additive/
│   │       ├── Sumsets.lean
│   │       ├── FiniteSumsets.lean
│   │       └── Pending/            # Explicit unfinished helper statements
│   ├── nodes/<id>.json             # Formal declarations, dependencies, review
│   └── checks/                    # nodes.json when checked; historical sumsets.json
├── .vscode/settings.json           # Lean and HTML editing configuration
├── pyproject.toml
└── uv.lock
```

Local environments and build outputs (`.venv/`, `formal/.lake/`, `staticfiles/`,
`artifacts/`) are ignored. KaTeX's vendored assets are tracked. There are no
`workers/`, `schemas/`, `infra/`, corpus release manifests, or foundation-lemma
allowlists in this implementation.

Corpus entry folders use stable IDs, not category paths. Local Lean modules are
organized for mathematical reuse: a module can support several entries, and an
entry can bind declarations from several modules or directly from mathlib. Moving
an entry between subjects does not require moving either its folder or its proofs.

## Source and rendering flow

1. `catalog.content` reads taxonomy, reading order, and each entry's HTML/JSON.
   It validates metadata, assets, mathematical references, and formal node IDs.
2. The HTML parser derives block kinds, titles, order, local numbering, and equation
   labels, figure/table numbers, links, and `data-formal` mappings. Metadata supplies
   citations and reading information. `formalization.nodes` resolves formal links
   and derives readiness. There is one editable source for each item.
3. Views render the parsed content through shared Django templates. KaTeX runs in
   the browser on entry pages; no AI or Lean process runs during a page request.
4. Editing an active entry, taxonomy, reading order, node, report, or checked source
   invalidates the catalog cache. Entry assets are registered
   with Django staticfiles at startup; adding a new asset directory needs a restart.

Reader views load the catalog once per request. Area listings derive their counts
from that snapshot; breadcrumb links do not load the corpus. The homepage features
the first entry in reading order. Formal node pages likewise load one registry
snapshot. Source path validation and declaration locations live together in
`formalization.lean`.

The reader lists entries under `corpus/entries/`, including drafts. It currently
contains **Sets and maps: a first guide** followed by **Equivalence relations,
partitions, and quotients**, under **Logic and foundations → Set theory**. The
second entry is a human draft with formalization not started.
`corpus/backup/` and `taxonomy_complete.json` are not live inputs;
regression tests use temporary copies of archived human text with old JSON block
metadata removed. Node tests use isolated fixtures. Primary areas determine listings
and “Next entry” order. Additional areas are stored but do not currently create
extra listings. Editorial status is descriptive metadata, not a permission gate.
The parser accepts trusted repository content; it is not a public-upload sanitizer.

The schema and HTML conventions are documented in [entry authoring](entry-sources.md).
Entry JSON has no slug, revision, top-level author/license/source fields, or global
external-lemma registry. `based_on` holds bibliography; mathematical links live
only in HTML. There are no JSON `blocks` or `references`. Git supplies history.

## Routes and interface

| Route | Current behavior |
| --- | --- |
| `/` | Top-level subject links and an example entry |
| `/areas/<path>/` | Breadcrumbs, child subjects, entries in this primary area |
| `/entries/<id>/` | Human note, contents, mathematical blocks, badges, source links |
| `/formal/nodes/<id>/` | Node status, declaration, dependencies, and source with inferred line |
| `/api/formal/nodes/` | Read-only JSON node list |
| `/api/formal/nodes/<id>/` | Read-only JSON node details |

There are no submission, account, review, search, or write API endpoints. Login and
submission buttons open placeholder dialogs. Missing HTML routes use the custom
404 page in both development and production.

The header shows authors, linked title, and year for the first **Based on:**
citation, with further sources in a native HTML disclosure. Direct entry visits
have no top back button. Local and cross-entry block references, and local figure/table
references, include the source entry and block
so a sticky return bar can go back precisely, reopening a question answer when
needed. Bottom back links and same-area “Next entry” links remain available.
Questions and verification details use native HTML disclosures. There is no
browser application framework or build step. Entry breadcrumbs and the optional
reference return bar share a sticky strip. Its measured height keeps anchor targets
and the desktop outline clear of it. The outline starts alongside the entry header
and wraps a separate scroll area whose height tracks the visible viewport.
On narrow screens the outline stays in the normal page flow below the header.

## Formal verification and its limits

A missing `data-formal` attribute means not started; an empty attribute means
not applicable. Otherwise the block badge counts ready nodes and displays a
percentage until complete. The badge sits beside the title and opens a list of
node links. Entry totals deduplicate shared nodes and keep unplanned blocks from
claiming full coverage. Questions map their answers.

Nodes live in `formal/nodes/<id>.json`, with a required mathematical description,
declaration/module, proof dependencies, and statement review. Nodes can exist
without an entry. Source paths initially follow
the import module; current checked locations identify the actual defining module,
including sources bundled with the pinned Lean toolchain. The formal API and node pages use `app/formalization/`; the reader
calls the same Python layer without making an HTTP request to itself.

`check_formalizations` builds registered modules, checks declarations and their
transitive axioms, and writes `formal/checks/nodes.json`. `sorryAx` means pending;
only `propext`, `Classical.choice`, and `Quot.sound` are allowed for complete proofs.
A ready node additionally needs statement review and ready declared dependencies.
The reader checks current fingerprints without compiling. Node/source/environment
changes invalidate affected evidence, except for editorial `description` text and
`review` records. Descriptions are reviewed through Git; review records update
approval without discarding Lean evidence. Target hashes exclude theorem proofs
and include referenced definitions; changed targets require renewed review.
Node pages show descriptions with KaTeX, checked signatures, review/check dates,
and expandable proof dependencies with compact node links and adjacent statuses.
An expandable source browser preserves line anchors; source-line links open it and
scroll to their target.
HTML in descriptions and source is escaped. Source is shown directly on node pages;
there is no separate file-viewer route. The registry currently contains 189 nodes.
The 127 nodes for sets-and-maps have passing Lean verification, with no `sorry`
placeholders; its notation-and-conventions block has an empty mapping.
Equivalence-relations reuses ten nodes and adds 62 unreviewed targets, including
21 statements with pending proofs. The [mathlib binding audit](mathlib-binding-audit.md) records
direct library bindings and the replacement of bundled nodes with separate claims.
Changed bindings and dependency lists require renewed review. Pending
dependencies can also prevent approved nodes from being complete. With an empty registry,
the checker skips Lean. Historical reports are untouched.

Reusable set theory lives in `Lemmatheca/SetTheory/Basic.lean` and
`Lemmatheca/SetTheory/EquivalenceRelations.lean`, under `Lemmatheca.SetTheory`.
`Lemmatheca/SetTheory.lean` imports both. Each entry has a single module under
`Lemmatheca/Entry/`: `SetsAndMaps.lean` and `EquivalenceRelations.lean`, with
corresponding `Lemmatheca.Entry.*` namespaces. The sets-and-maps module groups
its examples into sections and imports the basic theory and mathlib prerequisites.
The equivalence-relations examples reuse that module's diagram definitions.
Node IDs and declaration names are independent of source layout. Moving a node's
import module refreshes its source path after verification and changes its review
hash, so retained approval records become outdated until explicitly reviewed.

Committing reviewed HTML mappings records coverage approval. The `review --accept`
command records statement approval for selected nodes or an entry's linked nodes,
binding it to hashes of elaborated targets, referenced declarations, node metadata,
and the pinned environment. `review --retract` clears selected approvals without
running Lean or discarding its verification evidence. The checker detects changed targets but does not
prove correspondence with human text. It fingerprints ordinary source imports, not arbitrary metaprogram
inputs. Full proof-graph extraction and model runners remain future work. See
[verification and review](verification-and-review.md) for the exact boundaries.

Read-only deployments retain tracked `corpus/` and `formal/` files. The ignored
mathlib checkout is optional: when a referenced file is missing, the viewer offers
the exact pinned GitHub source. Missing local Lean sources still fail validation.

## Near-term additions

The next useful addition is a small, local, budgeted experiment runner and its run
records. Start with files, pinned inputs, a Lean process, and manual inspection.
Keep model attempts and cost measurements separate from publication metadata and
from `formal/checks/` verification reports. The experiment plan specifies the
measurements; the runner and log format are not implemented yet.

Continue improving the reader when real corpus material exposes a problem. Build
connected groups of notes from books and mathlib rather than a separate page for
every implementation lemma. Reuse checked declarations and invest human effort in
statement alignment, proof explanations, and the failures found by experiments.

## Deferred public system

When there is useful corpus coverage and actual contribution demand, add accounts,
submission previews, selected maintainer roles, review history, and publication
controls. PostgreSQL may then hold operational records; the Git corpus should
remain the authoritative mathematical source. Search projections, a human-corpus API,
release manifests, object storage, and job queues can be introduced as needed.
These are options for later work, not prerequisites for the current experiment.

Untrusted submissions will require HTML sanitization and isolated Lean/AI workers
with resource limits. The current trusted local checker is not that service.
Formal verification, editorial review, and publication remain separate decisions.
Research agents may propose new results, but adding them to the corpus remains a
manual, maintainer-reviewed action. Community participation can grow alongside
paper formalization; the schedule should not depend on it arriving automatically.
