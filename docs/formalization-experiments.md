# Formalization experiments and corpus growth

This is the proposed workflow, not a description of an existing AI service.
The current project supplies a file-backed reader, example content, and local Lean
checks. The next step is to measure AI formalization before committing to broad
corpus generation or building public contribution infrastructure.

## Separate the tasks being measured

| Task | Input and result | What success establishes |
| --- | --- | --- |
| Existing-result curation | A book passage or mathlib topic → readable note and checked declaration bindings | Useful corpus coverage and correct correspondence |
| Statement translation | Human definitions and statement → Lean definitions and proposition | The intended hypotheses and conclusion have been captured |
| Proof translation | Human argument and reviewed target → Lean proof following that argument | The supplied reasoning has been formalized |
| New proof search | Reviewed target and allowed prerequisites → a proof by any permitted method | A proposition has been proved, possibly by a different strategy |

Keep separate scores and costs for these tasks. Retrieving a theorem that proves
the goal can be excellent corpus curation without being a proof translation.
Similarly, a compiling proof of an accidentally weakened proposition is not a
successful statement translation. Review definitions, domains, hypotheses,
quantifiers, and conclusions before evaluating proof completion.

Reuse existing formalizations for corpus production. Reserve reconstruction of
particular human arguments for experiments or cases where their explanation is a
valuable part of the entry. Do not pay to reprove every elementary mathlib helper.

## First pilot

Use the examples in `corpus/backup/` to test the mechanics, then choose roughly 20–40 proof
tasks from two or three connected topics. This is a starting pilot size, not a
coverage target or a sufficient basis for broad capability claims. Include direct
library matches, representation changes, multi-step proofs, and a few deliberate
missing-lemma cases. Count definitions and prerequisites as work too.

Freeze the human inputs and divide development tasks from held-out evaluation
tasks before tuning prompts. Split by related section or theorem family, not just
random blocks in the same note. Public textbook and mathlib examples may already
be familiar to a model; describe this as practical workflow evaluation, not evidence
of novelty or uncontaminated generalization. A later unfamiliar-paper set can
probe transfer separately.

**Sets and maps: a first guide** is the active human-text baseline. Its original
nine-node declaration pilot has been extended with 112 proposed nodes covering
the remaining mathematical blocks, including examples and question answers. The
notation-and-conventions block has nothing to formalize. All 121 nodes now have
accepted reviews and passing verification. Two proof passes completed 31 and 55
theorem proofs while preserving their review hashes, leaving no `sorry` placeholders
in these modules. These declaration and proof passes are not held-out or
cost-measured runs. The archived **Finding a monotone
subsequence** is another reserved candidate: keep its four blocks
`not_started` until a measured attempt is explicitly launched. Its short human
proof is not a promise that the required Lean infrastructure will be short.

For each task, specify whether existing target proofs may be retrieved. Allow
ordinary prerequisites, but in proof-translation mode do not count calling the
target theorem, an alias, or a stronger pre-existing result as translating the
argument. Preserve important intermediate steps for review. Record imported
modules, retrieved declarations, and how shortcuts were checked. The current
axiom audit does not enforce these experimental restrictions or extract the full
mathematical dependency graph.

## Measure complete attempts

Before each batch, choose the model, a monetary/token limit, a wall-clock limit,
and a repair-attempt limit. Hold the limits constant for comparisons, and record
all attempts, including timeouts and abandoned tasks. If a task needs human help,
record the intervention and continue under a separately labelled assisted result.

A minimal run record should include:

- Task ID, experiment type, exact input text or hash, corpus commit, and Lean/mathlib pins.
- Model identifier and settings, prompts, provided context, retrieval policy, and tool calls.
- Every generated statement/proof, compiler feedback, repair count, and stopping reason.
- Input/output token usage, actual model charges where available, execution time,
  and compute costs; distinguish measured amounts from estimates.
- Human minutes spent on mathematics, Lean repair, and presentation editing separately.
- Independent outcomes: correct statement, successful Lean check, proof-strategy
  agreement, acceptable exposition, and remaining dependencies.

Compare first-attempt and budget-bounded success, and report both unaided and
human-assisted outcomes. For each task type, divide total batch spending,
including failures, by the number of human-reviewed successes; also report human
minutes and the expensive tail. If there are no successes, report that directly.
Token cost alone does not measure the cost of producing a usable entry.

Keep complete logs separately from entry JSON and verification reports. A future
local runner can write bulky outputs under the already-ignored `artifacts/` tree;
retain reproducible task definitions and compact result summaries in Git. Ignored
logs need deliberate retention if experiments are to be reproducible. No runner,
run schema, model integration, or automated costing exists yet.

Advance to larger batches when repeated runs show acceptable mathematical accuracy
and an affordable combined model/review workload. Set those thresholds from the
pilot and available budget; do not infer them from a few attractive successes.

## Build the standard corpus efficiently

Choose a small number of connected book sections and inspect their matching
mathlib modules first. A source map can associate each definition/result with a
book location and candidate declaration, exposing mismatched assumptions and gaps
before generating pages. This map is working material, not a new required entry field.
Not every textbook statement has an exact mathlib counterpart: notation, generality,
and representations can differ, and some background may still be missing. Estimate
that gap before committing to a chapter or assuming its proofs are already covered.

Use books to organize the explanation and pinned Lean declarations to check the
formal meaning. Write original prose with precise `based_on` citations. Prefer
sources suitable for the intended reuse; do not bulk-copy book text or figures.
A declaration-by-declaration dump is not the desired reader experience: group
results into coherent notes and reuse links to definitions and lemmas.

Generate content inside the existing HTML section conventions. The shared reader
already handles numbering, layout, citations, equations, and navigation. Run
`validate_corpus`, inspect representative pages, and ask editors to improve the
mathematical explanation and figures rather than repeatedly rebuilding page layout.
Stable block IDs should survive those edits.

Add existing mathlib bindings directly when they express the intended content.
Use local Lean for missing results or a proof strategy worth preserving. Refresh
verification reports, inspect the formal/human match, and keep unfinished blocks
explicitly partial or not started. There is no need to recreate mathlib's complete
foundation graph inside the human corpus.

Reuse dependency context, templates, and successful retrievals across related
tasks, while recording what was supplied during evaluation. Compare a simple
retrieval-and-check workflow with a more expensive repair/search loop before
adding orchestration. Pilot costs, especially review time, determine how quickly
to grow; availability of literature alone does not establish low cost.

## Advanced papers, research, and contributors

Start paper work with one short result whose prerequisites already have usable
formal representations. Where available, use structured source alongside the PDF,
then verify extracted formulae and assumptions. Track extraction errors, missing
background theory, statement translation, and proof repair separately. Introduce
longer papers only after small end-to-end cases work within the chosen budget.

Research agents should initially work in separate workspaces against a pinned
corpus, with explicit time/cost limits. Keep conjectures, failed approaches, and
checked results distinguishable. Lean checks a formal proof; literature comparison
and expert review establish whether the statement is new, meaningful, and worth
including. All new results still enter the corpus manually.

A useful corpus and visible, reproducible results give prospective contributors
something concrete to improve. Invite a few mathematical readers/editors during
the pilot; broad public machinery can wait. Community growth is an objective,
not an assumed consequence of autonomous research. Add accounts, review screens,
and durable workers when actual contributor activity warrants them.

## Related work informing the plan

[Herald](https://arxiv.org/abs/2410.10878) develops natural-language annotations
from mathlib and a statement autoformalizer. It provides a precedent for reusing
formal mathematics to bootstrap human/formal pairs; its reported benchmark
results do not establish this project's cost or faithful proof-translation rate.

[Reliable Evaluation and Benchmarks for Statement Autoformalization](https://arxiv.org/abs/2406.07222)
treats evaluation of formal statement correspondence as a distinct problem and
introduces corrected and research-level benchmarks. This supports measuring
statement accuracy independently of compilation and proof success.

[Mathlib's documentation](https://leanprover-community.github.io/documentation.html)
and [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/C01_Introduction.html)
provide starting points for finding formal concepts and examples. Use this
repository's pinned checkout as the compilation reference; online documentation
may describe a different version.
