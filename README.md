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

## What exists today

The project is a file-backed corpus, a read-only Django reader, and a local Lean
verification command. There is no operational database, AI runner, cost tracker,
public API, authentication, submission service, or publication workflow yet.
The login and submit buttons are placeholders. Draft entries are visible in the
reader; formalization status is separate from editorial status.

| Component | Current implementation |
| --- | --- |
| Mathematical source | `corpus/entries/<id>/entry.html`, `entry.json`, optional `assets/` |
| Browsing | `corpus/taxonomy.json` and explicit `corpus/reading-order.json` |
| Reader | Django templates, plain CSS, small JavaScript, self-hosted KaTeX |
| Formal mathematics | Lean 4.34.0 and pinned mathlib; reusable modules in `formal/Lemmatheca/` |
| Verification | `check_formalizations` builds and audits bound declarations; reports in `formal/checks/` |
| History | Git commits; no per-entry revisions or duplicate database source |

Entry folders use stable IDs, independently of the subject hierarchy. Each entry
contains numbered definitions, lemmas, theorems, and collapsible question answers.
References target individual blocks and retain a return link to the citing block.
The header shows a compact **Based on:** citation, with further sources collapsed.
Formalization badges are derived from all blocks; source links open a Lean viewer.
Equations, equation references, tables, and entry-local images are supported.
Figures are numbered 1, 2, … in source order and can be referenced by stable anchors.
Same-entry block and figure references also provide a sticky return bar.

The active corpus currently contains **Sets and maps: a first guide**, under
**Logic and foundations → Set theory**, based on Open Logic. Its 21 blocks remain
`not_started` for a measured formalization pass.

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

When active entries have formal bindings, refresh verification with the
[Lean environment](formal/README.md) installed:

```sh
uv run python app/manage.py check_formalizations
```

With the current unformalized entry, this command has no bindings to check and
does not launch Lean. It excludes archived entries.

A web-only checkout needs the tracked corpus, local Lean sources, reports, and
Lake manifest, but does not need Lean or mathlib installed. If the ignored
`formal/.lake/` checkout is absent, referenced mathlib files link to their pinned
GitHub source. Page requests never run Lean. Reports are local check records;
regenerate them after changes to mathematical content, bindings, or the environment.

## Documentation

| Document | Purpose |
| --- | --- |
| [Experiment and corpus plan](docs/formalization-experiments.md) | Evaluation tasks, cost measurement, corpus growth, and later research |
| [Architecture](docs/architecture.md) | Actual folders, data flow, routes, limitations, and deferred components |
| [Entry authoring](docs/entry-sources.md) | HTML, citations, assets, references, metadata, and Lean bindings |
| [Content model](docs/content-model.md) | Stable identities, block statuses, and machine access |
| [Verification and review](docs/verification-and-review.md) | Current checks, their limits, and human review |
| [Mathematical baseline](docs/baseline.md) | Candidate arguments and proof strategies for a small evaluation set |
| [Corpus](corpus/README.md) | Current examples and how to grow the collection |
| [Lean project](formal/README.md) | Toolchain setup, existing proofs, and axiom checks |
| [Web app](app/README.md) | Running the reader and editing its presentation |
