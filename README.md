# Lemmatheca

A mathematical library for people to read, Lean to check, and AI agents to explore.
The first goal is to measure AI formalization, then build connected standard
mathematics from books and mathlib. Advanced papers, autonomous research, and
public contributions come later.

## Submission and formalization pipeline

Correspondence review protects against proving the wrong statement: Lean can
verify a declaration even when it does not express the human claim. Approval
binds a node's description to its Lean declaration; entry text and block coverage
also need human review. Node IDs, proof-planning dependencies, module locations, and
environment pins do not enter the review hash. See
[verification and review](docs/verification-and-review.md).

Copy the corresponding [AI prompt](prompts/add-entry/) into a new task and replace
its `<...>` placeholders. Use them in order; the review prompts produce findings
for the maintainer. For a measured experiment, retain the filled prompts and
responses with the run logs, outside entry metadata. These are reusable queries,
not an automated runner.

1. **[Choose sources](prompts/add-entry/01-choose-sources.txt).** Specify books,
   notes, or papers, including relevant chapters or pages, and record the selected
   citations in `based_on` when drafting.
2. **[Draft the human entry](prompts/add-entry/02-draft-human-entry.txt).** Ask AI
   to prepare concise, original `entry.html` and `entry.json`,
   without formalization.
3. **[Review the human draft](prompts/add-entry/03-review-human-entry.txt).** Check
   the mathematics, explanations, and presentation; remove redundant wording.
   Keep it a draft until the later coverage review is complete.
4. **[Prepare formal nodes](prompts/add-entry/04-prepare-formal-nodes.txt).**
   Reuse existing nodes and prefer built-in Lean/mathlib declarations over local
   wrappers. Add missing definitions and statements, linking blocks through
   `data-formal`. Give each node a concise mathematical description: the theorem
   statement or the object being defined, with its assumptions. Check that new
   Lean declarations compile; leave new theorem proofs as `sorry`.
5. **[Review correspondence](prompts/add-entry/05-review-correspondence.txt).**
   Independently check the declarations and their collective coverage of each
   block, including examples and question answers. Compare node descriptions with
   the actual declarations, too. Record approval with
   `review --accept --node <id>` or `review --accept --nodes-from-entry <id>`; the command saves
   hashes of the reviewed targets. Use `--retract` to withdraw approval.
   AI findings do not themselves accept reviews. Several nodes may cover one
   block, and one node may serve several blocks; avoid both redundant nodes and
   uncovered claims. Once the text, rendering, and coverage have been checked,
   record a separate entry review as described below.
6. **[Prove the nodes](prompts/add-entry/06-prove-reviewed-nodes.txt).** Later,
   use AI to work through the dependency DAG, following the human proofs.
   Run `check_formalizations` and review whether the formal
   arguments follow the intended reasoning. Changes to approved descriptions or
   statements require another review; proof-only changes keep statement approval
   after rechecking.

Nodes are independent of entries. Agents can find human explanations by following
`data-formal` mappings in reverse; a dedicated lookup API is planned. For each
proof attempt, record the selected entry ID, block ID, and Git revision alongside
the experiment logs, rather than assigning a single entry to the node. Confirm
that the selected block contains a proof before treating the task as translation.

Proof work may reveal a need for new helper nodes or revised prerequisites.
Manual dependencies guide proof work; a reviewed node with a verified proof is
complete regardless of the statuses of its planned prerequisites.
Maintainers decide what enters the library; AI supplies proposals and recommendations.

Measure statement writing and proof translation separately. Binding an existing
mathlib result is useful corpus work, but does not show that a human argument was
translated. See the [experiment plan](docs/formalization-experiments.md).

## Recording reviews

Run these commands from the repository root after making the corresponding
maintainer decision:

```sh
uv run python app/manage.py review --accept --node <node-id> [<node-id> ...]
uv run python app/manage.py review --accept --nodes-from-entry <entry-id>
uv run python app/manage.py review --accept --entry <entry-id>
```

The first two approve node descriptions against Lean declarations. The second
selects every distinct node linked from the entry, leaving its editorial status
unchanged. The third records an **entry review**: check that the mathematics and
explanations contain no errors, that the rendered text, formulas, figures, tables,
links, and answers display correctly, and that nodes collectively cover every
block without redundant nodes or uncovered statements.

Entry acceptance validates the corpus and requires a mapping on every block and
a declaration for each linked node. Use an explicit empty `data-formal=""` where
nothing needs formalizing. The command records the human decision; it cannot judge
mathematical correctness, visual rendering, or semantic coverage automatically.
It changes `entry.json` from `draft` to `final`, removing the Draft badge and review
note. It neither runs Lean nor changes node approvals or verification evidence.
Unfinished proofs and unapproved nodes are allowed; formal progress stays visible
and independent of editorial approval.

Use `--retract` with the same selector to withdraw that review; for `--entry`, this
returns the entry to `draft`. All selectors support `--dry-run`, and repeated
actions leave unchanged records intact. Node acceptance may refresh Lean evidence
even during a dry run. Entry status is a manual decision, without a content hash:
after substantive changes to text, assets, mappings, or linked statements, retract
and repeat the entry review. Commit review changes alongside the reviewed work.

## Current implementation

A file-backed corpus, a Django reader, and a local Lean checker. The frontend uses
plain HTML/CSS/JavaScript and self-hosted KaTeX. There is no database or frontend
build step. Accounts, submissions, and autonomous AI workflows are not implemented.

The corpus has three entries. *Sets and maps* and *Equivalence relations* have complete
formal verification and current node approvals; *Ordered sets* is a human draft
awaiting formalization. All three retain draft editorial status.

Node pages put a mathematical description above the checked Lean statement, with
review/check dates, expandable proof prerequisites, and a source browser with line
links. Editing a description invalidates its correspondence approval immediately,
while preserving Lean evidence. Node IDs, proof dependencies, module locations, and
environment pins do not enter the review hash. Node renames, source moves, and
environment changes need a verification refresh; approval is retained if the
description and declaration hash stay unchanged.

Lean verification is tracked per import module and its transitive local source imports.
Editing a proof invalidates its module and any importers; unrelated modules retain
their evidence and check dates. The checker reuses current modules and saves
successful checks even when another module fails.
Mathlib and its companion Lake packages share one revision fingerprint. Installed
libraries are treated as immutable; source trees are not scanned for local edits.
Environment-pin or installed-revision changes invalidate checks using them. Direct Mathlib bindings share
one verification record; local modules retain separate records. Each record stores
its input hashes directly.

| Folder | Purpose |
| --- | --- |
| [`corpus/`](corpus/README.md) | Entry sources, assets, taxonomy, and reading order |
| [`formal/`](formal/README.md) | Formal nodes, Lean modules, and verification reports |
| [`app/`](app/README.md) | Reader, node pages, and read-only formal API |
| [`docs/`](docs/architecture.md) | Architecture, authoring, and experiment design |

## Run and check

From the repository root, with Python 3.12–3.14 and uv:

```sh
uv sync --locked
uv run python app/manage.py runserver
```

Open <http://127.0.0.1:8000/>. To validate changes:

```sh
uv run python app/manage.py validate_corpus
uv run python app/manage.py test catalog
```

[GitHub Actions](.github/workflows/ci.yml) runs these checks on every push and pull
request using Python 3.12, 3.13, and 3.14 and the locked dependencies. It also supports
manual runs. CI uses the committed formal evidence; Lean verification remains a
separate local check.

With the [Lean environment](formal/README.md) installed:

```sh
uv run python app/manage.py check_formalizations
```

Serving the website does not require Lean or mathlib installed. Keep the tracked
corpus, Lean sources, reports, and Lake manifest; missing mathlib sources link to
the pinned upstream version. Page requests never run Lean.

## Further reading

- [Architecture](docs/architecture.md) and [content model](docs/content-model.md)
- [Entry authoring](docs/entry-sources.md) and [verification and review](docs/verification-and-review.md)
- [Experiment plan](docs/formalization-experiments.md) and [mathematical baseline](docs/baseline.md)
