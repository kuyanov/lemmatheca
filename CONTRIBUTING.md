# Contributing to Lemmatheca

Contributions can improve exposition, add a topic, prepare formal bindings, prove
existing nodes, or improve the reader. Follow the [setup instructions](README.md#setup)
first. The contracts for [corpus content](docs/corpus.md),
[formal nodes and proofs](docs/formal.md), and the [app](docs/app.md) live in `docs/`.

## The six-step entry pipeline

Each stage has an executable prompt in `prompts/`. A task may request one stage
or a sequence. Use current artifacts and applicable handoffs; carry completed
work forward rather than repeating it. Content contracts live in
[docs/corpus.md](docs/corpus.md) and [docs/formal.md](docs/formal.md).

## Stage responsibilities

| Step | Owns | Required checks |
| --- | --- | --- |
| [1. Choose sources](prompts/01-choose-sources.md) | Sources, mathematical support, scope, prerequisites, outline and placement | Source passages and relevant existing prerequisite coverage |
| [2. Draft](prompts/02-draft-human-entry.md) | Human entry, metadata, assets, reading order, reference integration | Finish with a writing corpus build and inspect affected rendered pages |
| [3. Review the entry](prompts/03-review-human-entry.md) | Independent human mathematics and presentation review | Read the requested arguments and answers; inspect presentation and relevant references |
| [4. Prepare formal nodes](prompts/04-prepare-formal-nodes.md) | Definitions, target statements, node descriptions and mappings | Compile/elaborate targets, finish with a writing corpus build, render new/edited descriptions |
| [5. Review correspondence](prompts/05-review-correspondence.md) | Independent claim-to-declaration coverage and fidelity review | Inspect current types, definition bodies, representations and witnesses |
| [6. Prove](prompts/06-prove-nodes.md) | Proof bodies and necessary proof helpers | Compile proofs, run the integrated verification build, inspect axioms and warnings |

Steps 1, 3 and 5 leave authored entry content, node bindings and proofs unchanged.
Their only writing exception is [source-register maintenance](docs/corpus.md#source-errors)
and the derived refresh it requires through `build --no-lean`.
Step 4 implements definitions and states missing theorems, including
representation bridges, with unfinished proofs. Step 5 reviews those statements;
step 6 proves them. An intentional `sorry` at preparation is not by itself a
correspondence defect.

Author self-checks and independent reviews have different purposes: applying the
content contract while drafting does not replace step 3, and preparing faithful
targets does not replace step 5. Reviews independently inspect their own subject;
they do not repeat source discovery, unrelated library searches, or global
reference-planning sweeps. Stage 6 does not repeat either independent review when
only proof bodies change.

Revisit earlier work only where an input or result changes:

- New sources or changed mathematical scope need the affected step-1 work.
- Human claims or arguments need a drafting revision and focused step-3 review.
- Formal definitions, statements, bindings, coverage, representations, or the
  mathematical content of node descriptions need a preparation revision and
  focused step-5 review. Proof bodies and internal helpers for unchanged targets
  remain step-6 work.
- Wording, layout, or description-formatting changes need the corresponding
  validation/rendering checks, not another full mathematical or source audit.

For a requested multi-stage task, perform these affected revisions within its
scope. For an isolated stage, report work belonging to another stage and continue
unaffected work; do not silently expand the request. These are responsibility
boundaries, not approval flags or requirements for permission.

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

### Reference integration

The authoritative [reference-planning registry](corpus/reference-planning/index.json)
collects reference work in focused JSON records. Its `upcoming-reference` kind
is the single collection of references from current entries to future mathematical
areas. Each record identifies the future area, proposed reference
coverage, current consuming entry/block IDs, and the precise fact or context to
reference. Include useful broader treatments of facts developed locally as well
as accepted background. Group repeated uses and preserve stable IDs independently
of reading order or area membership. Proposed titles are suggestions; do not
invent target block IDs or link to nonexistent entries.

For a new entry or changed mathematical coverage, step 2 audits the relevant
entry blocks and owns integration: add useful outgoing links, search existing
entries across areas for consumers of the new coverage, add their incoming links,
and update the affected planning records. Check exact target statements and
assumptions. Preserve locally explained background and distinguish optional
explanatory links from required prerequisites. Remove only fulfilled consuming
locations and retain outstanding facts.

A wording, typo, or layout revision checks affected links; it does not require a
new source assessment, corpus-wide consumer search, or unrelated planning cleanup.
Step 1 may identify known integration candidates. Step 3 checks the entry's
references and the relevant integration changes, returning concrete corrections
without repeating the broad discovery search. Steps 4–6 do not own this audit.
Planning and review leave reference planning unchanged; step 2 saves its edits
rather than leaving required integration solely as suggestions in a handoff.

Keep existing-target integration notes, plans for future consuming entries,
cross-area correspondence still to prove, and deferred extensions in separate
record kinds in the same registry or in the handoff. Keep maintenance rules
here and in the prompts. The registry is separate from entry metadata and is
neither an approval system nor a record of readiness.
Each planning record tracks outstanding work only. Remove fulfilled integration
tasks, completed roadmap rows and drafting outlines, and completion narratives;
do not move them into another planning section. For partial coverage, retain only
the unfulfilled facts and consuming locations. Existing entries may still appear
as prerequisites of a specific future task, and source research may remain when
needed by planned work. Source-review history belongs in `corpus/source-errors/`.
Use the [targeted lookup workflow](docs/corpus.md#navigating-source-and-planning-records),
edit only affected records, and refresh derived data under the
[shared build rules](#validation-and-submission).

### Missing prerequisites and assumptions

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

Each prompt specifies only its stage-specific work and handoff. Read the linked
contracts relevant to that work; there is no need to reread every README or replay
earlier stages. Paths in commands are relative to the repository root; Markdown
links resolve relative to their document. Supply earlier reports as text, local
paths, or accessible GitHub references where useful. Reports are inputs, not a
mandatory approval record or persistent corpus metadata.

Use the [API retrieval workflow](#using-the-authoring-api) for the queries named
in each stage's prompt. Keep retrieval within that stage's responsibility.

If a handoff is absent or no longer applies, recover only the information needed
for the current stage. For example, check uncovered source passages before using
them in a draft; identify ambiguous human claims when preparing targets; report
missing mappings during correspondence review rather than inventing them. A
missing report does not by itself require restarting or block clear independent
work. Ask only when essential information cannot be recovered.

Complete the requested stages with reasonable local decisions. Preserve unrelated
changes and environment pins, and report unavailable checks honestly. Do not
advance automatically from review to rewriting/proving, or post, approve, or merge
on GitHub without instructions.

End with a concise handoff: scope, changed artifacts or findings, material
representation decisions, checks and unresolved work. Do not repeat unchanged
upstream reports or require a no-change statement for every possible audit.
Keep reports in the task discussion or pull request unless a report file was
requested. Whenever a stage actually inspects additional source material or finds
a confirmed defect, maintain [Source errors](docs/corpus.md#source-errors) for that
scope before the handoff. Reusing an applicable assessment does not require another
source audit or duplicate coverage record.

### Using the authoring API

Use the [authoring API](docs/app.md#authoring-api) for supported discovery and
retrieval when a supplied reader URL or an already running local reader is
available. Follow the stage-specific guidance in the prompt. If the server or
index is unavailable, use the canonical corpus files and continue; read-only
stages do not require server setup or index generation.
Use returned text and metadata directly for reading; open canonical inputs for
edits, omitted markup or assets, and stale or ambiguous results.

- Narrow retrieval with area and exact binding filters. Use `fields` on entry
  listing and node search to collect compact records, then fetch shortlisted
  nodes and their consumers as needed. Start node reuse searches with nonempty
  `q` queries for the entry's key concepts and related terms; repeated node `q`
  parameters search alternative formulations in one pass. An empty node query
  lists the selected pool; use a broad inventory only when targeted searches are
  insufficient.
  Block search accepts one `q`, so issue separate searches for its alternatives.
- When block IDs are known, use entry context with `block_ids=id-a,id-b` and only
  the needed `include` components. This filters blocks, mapped nodes, coverage
  and references before pagination; `include=nodes,coverage` need not return
  prose. Metadata and navigation remain entry-wide. Share retrieved responses
  across agents and reuse them while the relevant files and index are unchanged.
- Follow `limit`/`offset` until every requested result is read. Entry context
  paginates blocks, nodes and references independently; check each component's
  count. When all selected matches are needed, a larger `limit` (up to 100) can
  reduce pagination calls. Read hidden answers when their claims are in scope:
  context includes them by default, while block search needs `include_answers=true`.
- Node area membership comes from consuming entries, including additional and
  descendant areas. Shared nodes can appear in several areas. Unmapped nodes
  have no inferred area; `usage=unmapped` needs a search without an area filter.
- Treat indexed mappings, consumers and references as snapshot relationships.
  `revision` can pin a multi-request retrieval to one index, but does not certify
  current files or proofs. On `index_outdated`, use current files or refresh the
  index when the requested mutating stage permits it. A successful response can
  still miss new relationships from unvisited sources; check exact target claims
  and assumptions before using a proposed match or reference.
- Query source reviews and findings by publication URL or entry, and planning by
  entry, area, or kind, using the [registry endpoints](docs/app.md#source-and-planning-api).
  Read full records only after selecting relevant IDs. Without a running server,
  filter the compact JSON catalogs and open the selected paths directly.
- Inspect current Lean types, definition bodies, instances and axioms locally
  under the formal contract. API signatures and verification flags are saved
  results. Inspect external publications directly; registry lookups do not replace
  reading the selected source passages. No API performs live Lean inspection.

Use the API to retrieve evidence; mathematical review, rendering, file edits and
required checks remain the responsibility of their existing stages. Do not add
another corpus-wide audit just because a query is available.

## Validation and submission

`uv run python app/manage.py build` is the single corpus validation and generation
command. The [build guide](docs/build.md) explains its stages, outputs, flags,
and command combinations. `--no-lean` reuses saved proof results; `--check`
prevents publication. Together they provide a structural check without Lean or
requiring current generated data.

| Change or task | Required checks |
| --- | --- |
| Any authored change under `corpus/`, except `statistics.json` | Finish with the writing `build --no-lean` (or full `build` when required below); commit changed generated files, including `corpus/index.json` |
| Prose, formulas, figures, or node descriptions | Apply the writing-build and index-commit rule above, including prose-only or whitespace-only edits; inspect affected rendered content under the corpus/formal contracts |
| Formal definitions or targets | Compile affected modules and inspect their actual signatures |
| Bindings, declarations or proofs | Finish with `build` and inspect proof results, transitive axioms and warnings |
| Read-only review | Focused checks only to resolve a concrete concern; no routine writing build |
| Reader or build tooling | Relevant catalog tests and affected page checks |
| Documentation only | Check links, instructions and command examples; no corpus or proof build |

Run batch checks once after the relevant edits. A full build also satisfies
structural validation and compilation for the modules it builds. During a
multi-stage batch, defer the writing build until the final mutating stage; step 4
still elaborates targets before correspondence review. Do not repeat a successful
build without subsequent relevant changes or unresolved diagnostics.

`build --no-lean --check` is a read-only structural check, not a substitute for
the final writing build. The index revision hashes raw entry HTML, entry metadata,
and node-file bytes, so even a whitespace-only edit to those files changes it.
Registry records and assets are not hashed into the main index, so edits confined
to them may leave its regenerated contents byte-identical. Registry-only edits
still need catalog regeneration. Commit generated files that actually changed.

Saved results are not evidence that edited sources or bindings are verified.
`--no-lean` reuses them; it makes no new proof-checking claim. Include generated
node/entry JSON, authoring catalogs, and `corpus/index.json` with their inputs.
Full `build --check` requires the selected index to exist and match regeneration,
including its revision. See the [formal verification rules](docs/formal.md#build-and-verification)
for proof-completion requirements and the [build guide](docs/build.md#failures-and-scope)
for publication guarantees and tasks maintained separately.
Statistics-only updates belong to the statistics workflow and do not require an
index rebuild.

Describe the contribution's scope, source credit, review findings addressed,
checks performed, and any remaining gaps in the pull request. Keep stable entry,
block, and node IDs, reuse existing mathematical coverage, and avoid manually
editing generated results. Exposition quality, correspondence, and Lean proof
verification remain separate responsibilities.
