# Contributing to Lemmatheca

Contributions can improve exposition, add a topic, prepare formal bindings, prove
existing nodes, or improve the reader. Follow the [setup instructions](README.md#setup)
first. The contracts for [corpus content](docs/corpus.md),
[formal nodes and proofs](docs/formal.md), and the [app](docs/app.md) live in `docs/`.

## The six-step entry pipeline

Each step has an executable Markdown prompt in `prompts/`. A contribution may
complete one step or several. Start from the current files and supplied scope;
there is no need to repeat finished steps when, for example, proving existing
nodes. Entry review findings and decisions belong in GitHub pull requests.
Confirmed mathematical defects in external publications also belong in the
permanent [source-error register](corpus/source-errors.md), following the
[maintenance contract](docs/corpus.md#source-errors).

| Step | Input | Output | Changes repository content? |
| --- | --- | --- | --- |
| [1. Choose sources](prompts/01-choose-sources.md) | Topic, audience, scope, source constraints | Source-backed outline, citations, prerequisites, placement, source-error records | Source-error register only |
| [2. Draft the entry](prompts/02-draft-human-entry.md) | Source plan and intended entry ID | Original HTML, metadata, assets, reading-order placement | Yes |
| [3. Review the entry](prompts/03-review-human-entry.md) | Current entry and its sources | Mathematical, editorial, presentation, and source-error findings | Source-error register only |
| [4. Prepare formal nodes](prompts/04-prepare-formal-nodes.md) | Entry and relevant review findings | Node records, block mappings, missing definitions and theorem statements | Yes |
| [5. Review correspondence](prompts/05-review-correspondence.md) | Entry, nodes, and Lean declarations | Coverage audit and concrete binding corrections | Source-error register only |
| [6. Prove nodes](prompts/06-prove-nodes.md) | Selected nodes and agreed statements | Checked proofs and refreshed verification data | Yes |

### 1. Choose sources and scope

Inspect sources that support the proposed material and record precise chapter,
section, or page locations. Choose a coherent reading unit, its audience,
prerequisites, primary area, and position in the reading order. Identify existing
entries and formal nodes to reuse. The result is a source-to-outline map and
proposed `based_on` citations, with unavailable sources and open questions made
explicit. This step produces a plan; it does not create entries, nodes, or proofs.

Check the mathematical rigor of the source passages used, not just their relevance
or reputation. Inspect hypotheses, arguments, examples, nontrivial omissions, and
cited prerequisites. Report identified errors or gaps with precise source locations,
affected claims, consequences, and proposed repairs for use in step 2.
Distinguish genuine gaps from valid compressed arguments
and from uncertainty in the check; mark unavailable or unchecked material explicitly.
Prioritize serious mathematical defects over missing explanations. Consult and
update [Source errors](corpus/source-errors.md) with confirmed defects and the
actual reviewed scope before handing off the plan.

### 2. Draft the human entry

Before drafting, check the needed source passages for mathematical rigor. Use an
available step-1 assessment where it applies; check the passages yourself if the
assessment is missing or the scope or sources changed. Report errors, gaps, and
unchecked arguments before drafting, and establish a checked repair or supporting
argument before using an affected claim. Report unresolved affected work and
continue independent work where possible. Later steps review the current entry
and Lean declarations without requiring this assessment.
Save new confirmed source defects and checked repairs in
[Source errors](corpus/source-errors.md); update its coverage rows for cited
publications even when no defect is found in the checked passages.

Write original exposition in `corpus/entries/<id>/entry.html`, its metadata in
`entry.json`, and any figures in `assets/`. Include definitions, arguments,
examples, questions and answers, and useful boundary cases. Add the entry once
under its primary area in `corpus/area_entries.json`.

Follow the corpus HTML contract so headings, numbering, references, and navigation
are generated correctly. Leave new blocks' `data-formal` attributes absent until
bindings are planned. Check the rendered page and refresh the generated entry
summary with the build. Human-only entries are supported throughout the pipeline.

### 3. Review the human mathematics and presentation

Read the full entry, including hidden answers. Consult cited material as needed
to check attribution or resolve ambiguities. Check statements,
proofs, examples, prerequisites, notation, citations, references, and the rendered
layout. Return findings with precise locations, consequences, and suggested
corrections. Separate errors from optional editorial improvements and state any
checks that could not be performed.

This is a read-only audit of the entry, with source-error register maintenance
as its only permitted file edit. Address entry findings in a drafting revision and pass
relevant remaining questions to formalization. Running a writing build is not
part of the review, and a reviewer does not set any approval state in the corpus.

### 4. Prepare formal nodes and block bindings

Inventory the mathematical claims in each block, including examples and answers.
Reuse existing nodes and suitable Lean/mathlib declarations. For missing results,
implement the required definitions and write theorem statements with `by sorry`
(the explicit Lean placeholder for an unfinished proof). Preserve existing proofs;
proving new theorems belongs to step 6.

Put reusable mathematics in the general theory layer, currently
`formal/Lemmatheca/SetTheory/`, even when it originates in a single entry.
Reserve `Entry/` for particular illustrative examples and counterexamples with
no wider use, and their example-specific helpers. General theory must not import
entry modules; examples import the theory they illustrate.

Create node records and link them from blocks with `data-formal`. Several nodes
can cover one block, and one node can serve many entries.
An empty mapping means there is nothing to formalize; it must not hide unfinished
work. Record representation choices and specializations for the next reviewer.
Build to check that bindings exist and generate signatures, source lines, and
verification data. Unfinished theorems compile but remain Not verified.

### 5. Review correspondence and coverage

Independently compare the prose, node descriptions, and actual Lean declarations.
Check hypotheses, quantifiers, types, conclusions, witnesses, edge cases, and any
representation changes. Inspect definitions and elaborated signatures, including
which relation or typeclass instance Lean selected. A plausible declaration name
or successful proof is not evidence of a correct binding.

Return a block-by-block coverage table and findings about incorrect bindings,
missing claims, unexplained translations, and redundant nodes. This audit is
read-only for entries, nodes, and proofs; source-error register maintenance is
its only permitted file edit. Apply corrections in a preparation revision; substantive later changes
to statements or representations need renewed correspondence review.

### 6. Prove the selected nodes

Complete the selected unfinished proofs in the shared `formal/` project. Preserve
the intended statements, definitions, and node targets; explain any necessary
correction and identify the correspondence review it requires. Reuse library
results and unregistered helpers where appropriate. JSON `dependencies` are
proof-planning hints; verification checks actual Lean dependencies instead.

The default is ordinary corpus proving. When explicitly translating a human proof,
preserve its important reasoning and distinguish that from using an existing
library theorem. Measured experiments require an explicit run specification;
keep attempts, budgets, and measurements outside corpus metadata.

Finish with the build and inspect the selected nodes' saved verification flags.
A successful compilation alone is insufficient because Lean accepts `sorry`, and
a complete proof may use an unsupported custom axiom.
Inspect Lean and Lake warnings as well. Fix causes in project-owned sources without
weakening the mathematics or suppressing diagnostics through local or global linter
settings, then rerun the full build and inspect its diagnostics. Intentionally
unused parameters may be named with a leading underscore, preserving their
hypotheses. Distinguish unavoidable pinned-dependency warnings
and expected warnings from unrelated, deliberately unfinished declarations; see
the [build-warning guidance](docs/formal.md#build-warnings).
Return proved IDs, checks, warning cleanup and remaining diagnostics, any statement
changes, and concrete remaining work.

## Prerequisites and scope

Before proposing or drafting an entry, check which definitions and results its
arguments actually need against the current corpus. Record existing prerequisites
by stable entry and block IDs, including those in other areas. Distinguish human
coverage from formal readiness: a library theorem or verified node does not supply
an explanation for the reader, and a drafted entry may still have unfinished nodes.

Familiar background may be used without an entry reference. This includes elementary
arithmetic, ordinary classical reasoning, and standard real-number facts used in
examples or short supporting arguments. A missing corpus reference for such a fact
is not itself a mathematical gap or a drafting blocker.

The authoritative [Reference backlog and planning](corpus/reference-planning.md)
document collects reference work in one place. Its
[Upcoming references](corpus/reference-planning.md#upcoming-references) section
contains exactly one four-column table of references from current entries to
future mathematical areas. Each row records the future area, proposed reference
coverage, current consuming entry/block IDs, and the precise fact or context to
reference. Include useful broader treatments of facts developed locally as well
as accepted background. Group repeated uses and preserve stable IDs independently
of reading order or area membership. Proposed titles are suggestions; do not
invent target block IDs or link to nonexistent entries.

During every step-2 draft or revision, audit all entry blocks and update this table
before returning the draft. Report the rows added, changed, or removed, or state
that the audit found no changes needed. When suitable target blocks become
available, check their facts and assumptions, add the entry links, and remove only
the fulfilled consuming locations; keep remaining locations in the row. A related
title or an available Lean declaration alone does not establish human coverage.
Step 3 must audit the table and return concrete proposed corrections or an explicit
no-change finding. Planning and review do not edit reference planning: put proposed changes in
the handoff rather than editing the document during those steps.

Keep existing-target integration notes, plans for future consuming entries,
cross-area correspondence still to prove, and deferred extensions in separate
planning sections of the same document or in the handoff. Keep maintenance rules
here and in the prompts. The document is separate from corpus metadata and is
neither an approval system nor a record of readiness.

Entries should have no major dependencies on substantial theory missing from the
corpus. Judge the scope and role of a prerequisite, not just whether its subject is
familiar: using real-number order or a geometric-series estimate is different from
assuming a substantial analysis theorem or an entire theory. Accepted background
must still be correct, with compatible assumptions. Recording a future reference
does not permit deferring essential justification or missing major theory.

A short supporting lemma can be developed within the proposed entry when it fits
its central subject. If a substantial prerequisite theory is missing, recommend
the area and specific entry titles to start, explain which claims need them, and
choose a narrower useful scope or defer the dependent material. Do not overload an
entry with another area's foundations or create prerequisite entries unless the
task authorizes them. Return this assessment in the planning or drafting handoff;
do not add readiness or approval fields to corpus metadata.

Check assumptions as well as topics. A result proved using full Choice cannot be
reused as a ZF-only result without a suitable argument. Distinguish mathematical
implications from claims of non-implication, independence, or relative consistency;
the latter require their own logical framework and model arguments. Likewise,
closure properties of a set do not by themselves establish that it is a model of
an axiom system.

Formal verification uses classical Lean and mathlib with Choice permitted by
default. It does not certify derivability from first-order ZF or weaker choice
principles. Preserve the human arguments' stated assumptions, assess such claims
separately, and report any limits on formal coverage. See the
[verification rules](docs/formal.md#build-and-verification).

## Reading order

Choose and review the reading order using these criteria:

- Introduce each definition before using or referring to it, either locally or in
  an earlier prerequisite entry. Check the order of blocks within entries as well
  as the order of entries. Familiar background follows the scope policy above.
- Progress from easier, well-known topics to less familiar, more advanced ones.
- Group closely related topics together where prerequisites allow it.
- Prefer a sequence in which each entry builds on the preceding one, while naming
  and linking its actual prerequisites by stable IDs.
- Make each summary and abstract understandable before reading the entry, using
  preceding material and familiar background. Briefly explain any new terms;
  neither should require definitions introduced only in the entry or later.
  Ground an abstract's motivation in the cited sources' explanations and examples,
  write original prose, and check it against the entry's scope. Give a concrete
  reason to follow the rigorous arguments, using familiar vocabulary and a few
  connected central results.

Prerequisite order takes priority when these preferences conflict. Recheck it when
adding, expanding, reordering, or moving entries into subareas. Keep entry prose
independent of its position: refer to named topics and stable links rather than
"the previous entry" or "the next entry."

## Running one step with an AI agent

Give the agent the prompt path and the inputs listed in that file. For example:

```text
Execute prompts/04-prepare-formal-nodes.md for entry ordered-sets.
Use the current entry and the attached human-review findings.
Complete step 4 and return its coverage map and check results.
```

Each prompt specifies its own context, work, checks, and deliverable. Paths in
commands and inline file references are relative to the repository root; Markdown
links resolve relative to the document. A fresh agent should inspect the actual
files rather than assume access to another conversation. Supply earlier reports
as text, local file paths, or accessible GitHub references when they matter.

Agents should carry out the requested step through its checks, using reasonable
local decisions within the supplied scope. Infer optional inputs from the current
entry and explain material assumptions. Ask only when essential scope or source
material cannot be recovered; continue independent work where possible. Preserve
unrelated changes and environment pins. Report unavailable checks honestly.
Complete only the requested stages; do not automatically move from a review to
rewriting or proving, or post, approve, or merge on GitHub without instructions.

End each step with a handoff that another agent can use: entry ID and scope,
changed files or findings, source locations and representation decisions, checks
performed, and unresolved work. Keep these reports in the task discussion or pull
request, or in an explicitly requested report file. They are not corpus metadata.
Save confirmed external-source defects and checked coverage in
[Source errors](corpus/source-errors.md) before returning any step that discovers
them. Valid compressed arguments and missing explanation do not qualify.

## Validation and submission

Choose checks that match the changes. After editing corpus files in drafting or formal-node preparation, or changing
node records, bindings, or entry structure while proving, run this read-only check
from the repository root:

```sh
uv run python app/manage.py validate_corpus
```

It needs no Lean installation or prior build, permits unplanned blocks and unbound
nodes, and checks the shape rather than freshness of generated data. Once Lean
sources are installed, add `--check-sources` to check source availability.

After changing Lean declarations, bindings, or proofs, or adding an entry or
changing its block inventory, refresh generated data with:

```sh
uv run python app/manage.py build
```

The build owns node verification, signatures, declaration lines, defining modules,
and entry `formalization` summaries. Include these generated JSON changes with the
sources. Leave `corpus/statistics.json` to the
[statistics workflow](.github/workflows/statistics.yml), which refreshes it after
pushes to `main` and includes newly merged contributors.
Failed compilation or declaration checks write no new results; old flags
do not establish that the edited sources are verified. Review-only steps inspect
saved data and report missing or stale results without running the writing build.
Inspect the full Lean build output for warnings and rerun the full command after
fixing their causes. A successful build alone does not certify clean diagnostics;
apply the [warning guidance](docs/formal.md#build-warnings) while preserving supported
unfinished and unbound states.

For reader or build-tooling code changes, run the relevant tests (for example,
`uv run python app/manage.py test catalog`) and inspect affected pages. Catalog
tests can also help investigate rendering or integration failures; routine
content and proof edits do not require them. Documentation
changes need link and command checks, not a proof rebuild. Inspect mathematical
layout, references, hidden answers, and figures when changing reader content.
[CI](.github/workflows/ci.yml) validates the corpus before installing Lean, checks
installed sources, runs tests and the proof build, and checks that generated node
data and entry summaries match the committed files.

Describe the contribution's scope, source credit, review findings addressed,
checks performed, and any remaining gaps in the pull request. Keep stable entry,
block, and node IDs, reuse existing mathematical coverage, and avoid manually
editing generated results. Exposition quality, correspondence, and Lean proof
verification remain separate responsibilities.
