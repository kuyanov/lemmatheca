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
AI model integrations, search services, and a public API are not implemented.
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
│   │   └── management/commands/    # validate_corpus and check_formalizations
│   ├── templates/                  # Shared Django layout and reader pages
│   └── static/                     # CSS, small JS, self-hosted vendor/katex
├── corpus/
│   ├── taxonomy.json              # Working subjects only
│   ├── taxonomy_complete.json     # Broader taxonomy, not loaded by the reader
│   ├── backup/<entry-id>/          # Archived examples, not served as entries
│   ├── reading-order.json
│   └── entries/<entry-id>/
│       ├── entry.json              # Identity, bibliography, areas, blocks and bindings
│       ├── entry.html              # Human mathematical sections, without Django tags
│       └── assets/                 # Optional entry-local illustrations/supplements
├── formal/
│   ├── lean-toolchain
│   ├── lakefile.toml
│   ├── lake-manifest.json
│   ├── Lemmatheca.lean
│   ├── Lemmatheca/
│   │   ├── AxiomChecks.lean
│   │   └── Combinatorics/Additive/
│   │       ├── Sumsets.lean
│   │       ├── FiniteSumsets.lean
│   │       └── Pending/            # Explicit unfinished helper statements
│   └── checks/sumsets.json         # Generated verification record
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
   It validates metadata, assets, mathematical references, and formal bindings.
2. The HTML parser derives block kinds, titles, order, local numbering, and equation
   labels, plus figure numbers and links. Metadata supplies citations, reading information, references, and
   formalization records. There is one editable source for each item.
3. Views render the parsed content through shared Django templates. KaTeX runs in
   the browser on entry pages; no AI or Lean process runs during a page request.
4. Editing an active entry, taxonomy, or reading-order file invalidates the catalog cache. Entry assets are registered
   with Django staticfiles at startup; adding a new asset directory needs a restart.

The reader lists entries under `corpus/entries/`, including drafts. It currently
contains only **Sets and maps: a first guide**, under **Logic and foundations →
Set theory**. `corpus/backup/` and `taxonomy_complete.json` are not live inputs;
regression tests use temporary copies of the archived examples. Primary areas determine listings
and “Next entry” order. Additional areas are stored but do not currently create
extra listings. Editorial status is descriptive metadata, not a permission gate.
The parser accepts trusted repository content; it is not a public-upload sanitizer.

The schema and HTML conventions are documented in [entry authoring](entry-sources.md).
Entry JSON has no slug, revision, top-level author/license/source fields, or global
external-lemma registry. `based_on` holds bibliography; block `references` hold
mathematical links. Git supplies history. Agents can already read these files
without waiting for an API.

## Routes and interface

| Route | Current behavior |
| --- | --- |
| `/` | Top-level subject links and an example entry |
| `/areas/<path>/` | Breadcrumbs, child subjects, entries in this primary area |
| `/entries/<id>/` | Human note, contents, mathematical blocks, badges, source links |
| `/lean/<source>/` | Escaped Lean source from the allowed local or mathlib trees |

There are no submission, account, review, search, or API endpoints. Login and
submission buttons open placeholder dialogs. Missing HTML routes use the custom
404 page in both development and production.

The header shows authors, linked title, and year for the first **Based on:**
citation, with further sources in a native HTML disclosure. Direct entry visits
have no top back button. Local and cross-entry block references, and local figure
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

Each block has `not_started`, `partial`, or `complete` formalization status.
A question uses its answer's status. The entry badge aggregates every block.
Bindings point to local `Lemmatheca.*` or pinned `Mathlib.*` declarations.
Unproved helper statements are explicit local Lean bindings under
`unformalized_dependencies`; a nonempty list prevents complete status.

`check_formalizations` validates the corpus, builds the main library and bound
modules, and checks complete declarations and their transitive axiom dependencies.
Archived entries are excluded. With the current unformalized entry there is nothing
to check, so the command does not launch Lean or overwrite old reports.
Only `propext`, `Classical.choice`, and `Quot.sound` are allowed for complete proofs.
Pending helper statements are checked separately and may use `sorryAx`. Reports
record bindings, hashes, axiom lists, and environment pins. The command does not
write proofs or automatically promote statuses. It is not an AI experiment runner.

The reader checks membership in a passing report and, for mathlib bindings, that
the source was recorded. It does not recompile or compare every recorded hash
against current files on each request. Regenerate reports after relevant changes.
A passing report does not certify the human/formal correspondence, proof strategy,
novelty, or complete mathematical dependency graph.

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
remain the authoritative mathematical source. Search projections, a read-only API,
release manifests, object storage, and job queues can be introduced as needed.
These are options for later work, not prerequisites for the current experiment.

Untrusted submissions will require HTML sanitization and isolated Lean/AI workers
with resource limits. The current trusted local checker is not that service.
Formal verification, editorial review, and publication remain separate decisions.
Research agents may propose new results, but adding them to the corpus remains a
manual, maintainer-reviewed action. Community participation can grow alongside
paper formalization; the schedule should not depend on it arriving automatically.
