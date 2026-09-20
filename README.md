# Lemmatheca

A mathematical library for people to read, Lean to check, and AI agents to explore.
The immediate goal is to measure how reliably and economically AI can formalize
human mathematics, then build a useful standard-mathematics corpus in a few areas.
Public contribution machinery comes after the corpus and workflow are useful.

## Direction

1. **Measure formalization.** Start with a small, fixed collection of human proofs.
   Measure statement accuracy, faithful proof translation, Lean verification,
   model cost, and human correction time. Keep unsuccessful attempts in the results.
2. **Draft standard mathematics.** Work through selected book sections alongside
   the corresponding pinned mathlib modules. Reuse existing declarations, write
   connected HTML notes, and have humans review mathematical correspondence and
   improve exposition. Expand coherent topics before expanding the taxonomy.
3. **Tackle advanced papers.** Start with short papers whose prerequisites are
   largely covered. Separate document extraction, statement translation, missing
   library development, and proof formalization so their costs remain visible.
4. **Explore new results.** Let research agents propose conjectures and proofs
   against a reproducible corpus snapshot. Check correctness, significance, and
   novelty separately; new results are still added manually after human review.
5. **Support a contributor community.** Add accounts, submissions, review queues,
   background jobs, and publication controls when corpus use and contributor
   activity justify them. These can grow alongside advanced-paper work.

Corpus construction and proof-translation experiments have different success
criteria. A correct mathlib binding is useful corpus work, but does not demonstrate
that an AI formalized the displayed human proof. Existing formalizations reduce
proof work; matching hypotheses, finding declarations, and reviewing explanations
still take effort. Low cost is a hypothesis to measure, not an assumed property.
See the [experiment and corpus plan](docs/formalization-experiments.md).

## Submission and formalization pipeline

Human mathematics comes first; a submission does not need a formalization.

1. **Submit human text.** Supply `entry.html`, `entry.json`, and optional assets.
   Formalization starts as **not started** and does not determine editorial status.
2. **Plan the formal content.** AI proposes definitions, theorem statements,
   assumptions, and dependencies as reusable nodes under `formal/`. Blocks in the
   HTML link to their nodes through `data-formal="node_id1 node_id2 ..."`.
   A human reviews both the proposed statements and whether they cover the human
   text, including blocks marked as needing no formalization.
3. **Prove approved statements.** AI works autonomously against the reviewed
   targets, reusing checked nodes and mathlib declarations. Changes to a target's
   assumptions or conclusion require another human review. Lean checks the
   resulting proofs; maintainers retain the final decision to include results.

Formal nodes, dependencies, and verification evidence have a separate read-only API.
The human entry keeps its text, ordinary metadata, and node links; prompts,
attempts, and costs belong in separate experiment records. Planning coverage and
proof completion are tracked separately, so proving every linked node cannot
hide mathematical content that has not yet been mapped.

The file contract, node pages, progress badges, and read-only formal API are
implemented. AI planning, autonomous proving, run records, and public submissions
come later. Statement writing and theorem proving will be measured separately.
Definition 1 of sets-and-maps now has nine proposed nodes for review, with new
theorem proofs left pending. See the
[block mapping](corpus/README.md#block-to-node-mapping),
[formal nodes](formal/README.md#formal-nodes), and
[reader integration](app/README.md#formal-api).

## What exists today

The project is a file-backed corpus, a read-only Django reader, and a local Lean
verification command. There is no operational database, AI runner, cost tracker,
human-corpus API, authentication, submission service, or publication workflow yet.
The login and submit buttons are placeholders. Draft entries are visible in the
reader; formalization status is separate from editorial status.

| Component | Current implementation |
| --- | --- |
| Mathematical source | `corpus/entries/<id>/entry.html`, `entry.json`, optional `assets/` |
| Browsing | `corpus/taxonomy.json` and explicit `corpus/reading-order.json` |
| Reader | Django templates, plain CSS, small JavaScript, self-hosted KaTeX |
| Formal mathematics | Stable records in `formal/nodes/`; reusable Lean modules in `formal/Lemmatheca/` and pinned mathlib |
| Verification | `check_formalizations` checks nodes independently of entries; evidence in `formal/checks/nodes.json` |
| Formal access | `/api/formal/nodes/`, `/api/formal/nodes/<id>/`, and `/formal/nodes/<id>/` |
| History | Git commits; no per-entry revisions or duplicate database source |

Entry folders use stable IDs, independently of the subject hierarchy. Each entry
contains numbered definitions, lemmas, theorems, and collapsible question answers.
References target individual blocks and retain a return link to the citing block.
The header shows a compact **Based on:** citation, with further sources collapsed.
Compact badges sit beside block titles; partial progress shows the percentage of
linked nodes ready. Clicking a badge expands node links with status labels for
review, verification, proof, and dependency work. Node pages show escaped Lean
source, with a declaration line when inferred.
The entry badge counts shared nodes once and keeps unmapped blocks visible.
Equations, equation references, tables, and entry-local images are supported.
Figures are numbered 1, 2, … in source order and can be referenced by stable anchors.
Same-entry block and figure references also provide a sticky return bar.

The active corpus currently contains **Sets and maps: a first guide**, under
**Logic and foundations → Set theory**, based on Open Logic. Definition 1 has
nine formal nodes; the other 20 blocks remain `not_started` for a
measured formalization pass.

The three earlier examples are preserved in `corpus/backup/` and are not listed
or served as entries. Their Lean sources and historical verification report remain
in `formal/`. `corpus/taxonomy.json` contains the working areas;
`corpus/taxonomy_complete.json` preserves the broader taxonomy for later use.

The active entry is an editorial draft. Lean checks formal proofs; humans still
check that those proofs express the intended mathematics. AI recommendations never
replace a maintainer's decision to include a result.

## Run and check

From the repository root:

```sh
uv sync --locked
uv run python app/manage.py runserver
```

Open <http://127.0.0.1:8000/>. No database setup is needed. The development server
is not a production deployment configuration.

```sh
uv run python app/manage.py check
uv run python app/manage.py validate_corpus
uv run python app/manage.py test catalog
```

When formal nodes have declarations, refresh verification with the
[Lean environment](formal/README.md) installed:

```sh
uv run python app/manage.py check_formalizations
```

The checker currently checks Definition 1's nine nodes, including four theorem
statements with `sorry`. Archived JSON bindings are historical material and are
not checked.

A web-only checkout needs the tracked corpus, local Lean sources, reports, and
Lake manifest, but does not need Lean or mathlib installed. If the ignored
`formal/.lake/` checkout is absent, referenced mathlib files link to their pinned
GitHub source. Page requests never run Lean. Declaration, module, dependency,
source, or environment changes invalidate affected evidence; rerun the checker
after these changes. Toggling `reviewed` applies immediately without a Lean rerun.
HTML mappings are reviewed manually when committed, including empty mappings.

## Documentation

| Document | Purpose |
| --- | --- |
| [Experiment and corpus plan](docs/formalization-experiments.md) | Evaluation tasks, cost measurement, corpus growth, and later research |
| [Architecture](docs/architecture.md) | Actual folders, data flow, routes, limitations, and deferred components |
| [Entry authoring](docs/entry-sources.md) | HTML, citations, assets, references, metadata, and formal node links |
| [Content model](docs/content-model.md) | Stable identities, block statuses, and machine access |
| [Verification and review](docs/verification-and-review.md) | Current checks, their limits, and human review |
| [Mathematical baseline](docs/baseline.md) | Candidate arguments and proof strategies for a small evaluation set |
| [Corpus](corpus/README.md) | Current entries, block-to-node mapping, and corpus growth |
| [Lean project](formal/README.md) | Toolchain setup, existing checks, and formal nodes |
| [Web app](app/README.md) | Running the reader, editing its presentation, and formal API |
