# Contributing to Lemmatheca

Contributions can improve exposition, add a topic, prepare formal bindings, prove
existing nodes, or improve the reader. Follow the [setup instructions](README.md#setup)
first. The contracts for [corpus content](docs/corpus.md),
[formal nodes and proofs](docs/formal.md), and the [app](docs/app.md) live in `docs/`.

## The six-step entry pipeline

Each step has an executable Markdown prompt in `prompts/`. A contribution may
complete one step or several. Start from the current files and supplied scope;
there is no need to repeat finished steps when, for example, proving existing
nodes. Review findings and decisions belong in GitHub pull requests. The app
stores no approval flags, review hashes, or review dates.

| Step | Input | Output | Changes repository content? |
| --- | --- | --- | --- |
| [1. Choose sources](prompts/01-choose-sources.md) | Topic, audience, scope, source constraints | Source-backed outline, citations, prerequisites, and placement | No |
| [2. Draft the entry](prompts/02-draft-human-entry.md) | Source plan and intended entry ID | Original HTML, metadata, assets, reading-order placement | Yes |
| [3. Review the entry](prompts/03-review-human-entry.md) | Current entry and its sources | Mathematical, editorial, and presentation findings | No |
| [4. Prepare formal nodes](prompts/04-prepare-formal-nodes.md) | Entry and relevant review findings | Node records, block mappings, missing definitions and theorem statements | Yes |
| [5. Review correspondence](prompts/05-review-correspondence.md) | Entry, nodes, and Lean declarations | Coverage audit and concrete binding corrections | No |
| [6. Prove nodes](prompts/06-prove-nodes.md) | Selected nodes and agreed statements | Checked proofs and refreshed verification data | Yes |

### 1. Choose sources and scope

Inspect sources that support the proposed material and record precise chapter,
section, or page locations. Choose a coherent reading unit, its audience,
prerequisites, primary area, and position in the reading order. Identify existing
entries and formal nodes to reuse. The result is a source-to-outline map and
proposed `based_on` citations, with unavailable sources and open questions made
explicit. This step produces a plan; it does not create content or proofs.

### 2. Draft the human entry

Write original exposition in `corpus/entries/<id>/entry.html`, its metadata in
`entry.json`, and any figures in `assets/`. Include definitions, arguments,
examples, questions and answers, and useful boundary cases. Add the entry once
under its primary area in `corpus/area_entries.json`.

Follow the corpus HTML contract so headings, numbering, references, and navigation
are generated correctly. Leave new blocks' `data-formal` attributes absent until
bindings are planned. Check the rendered page and refresh the generated entry
summary with the build. Human-only entries are supported throughout the pipeline.

### 3. Review the human mathematics and presentation

Read the full entry, including hidden answers and cited material. Check statements,
proofs, examples, prerequisites, notation, citations, references, and the rendered
layout. Return findings with precise locations, consequences, and suggested
corrections. Separate errors from optional editorial improvements and state any
checks that could not be performed.

This is a read-only audit. Address its findings in a drafting revision and pass
relevant remaining questions to formalization. Running a writing build is not
part of the review, and a reviewer does not set any approval state in the corpus.

### 4. Prepare formal nodes and block bindings

Inventory the mathematical claims in each block, including examples and answers.
Reuse existing nodes and suitable Lean/mathlib declarations. For missing results,
implement the required definitions and write theorem statements with `by sorry`
(the explicit Lean placeholder for an unfinished proof). Preserve existing proofs;
proving new theorems belongs to step 6.

Create node records and link them from blocks with `data-formal`. Coverage can be
collective: several nodes can cover one block, and one node can serve many entries.
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
read-only. Apply corrections in a preparation revision; substantive later changes
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
A successful compilation alone is insufficient because Lean accepts `sorry`.
Return proved IDs, checks, any statement changes, and concrete remaining work.

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

## Validation and submission

At any stage, run this read-only check from the repository root:

```sh
uv run python app/manage.py validate_corpus
```

It needs no Lean installation or prior build, permits unplanned blocks and unbound
nodes, and checks the shape rather than freshness of generated data. Once Lean
sources are installed, add `--check-sources` to check source availability.

After changing entry HTML, bindings, or proofs, run:

```sh
uv run python app/manage.py build
uv run python app/manage.py test catalog
```

The build owns node verification, signatures, declaration lines, defining modules,
and entry `formalization` summaries. Include these generated JSON changes with the
sources. Leave `corpus/statistics.json` to the
[statistics workflow](.github/workflows/statistics.yml), which refreshes it after
pushes to `main` and includes newly merged contributors.
Failed compilation or declaration checks write no new results; old flags
do not establish that the edited sources are verified. Review-only steps inspect
saved data and report missing or stale results without running the writing build.

For app changes, run the relevant tests and inspect affected pages. Documentation
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
