# Step 4: Prepare formal nodes

Follow the [shared execution rules](../CONTRIBUTING.md#running-one-step-with-an-ai-agent).
Own formal definitions, target statements, node records, and block mappings.
Do not prove new theorems.

In the [area pipeline](../CONTRIBUTING.md#running-an-area-pipeline), prepare only
the assigned entry's targets and owned files. Send shared imports, reused-node
changes or scope conflicts to root unless exclusive file ownership was assigned.

## Inputs

- Entry ID or entry selection.
- Optional human-review findings and agreed mathematical revisions.

## Context

Read the current human entry and relevant findings. Use the
[mapping contract](../docs/corpus.md#block-to-node-mapping) and
[formalization guide](../docs/formal.md), especially bindings, representation
fidelity, node descriptions, module placement, and verification. Inspect existing
nodes and the pinned Lean sources. Do not repeat human review or source selection;
report mathematical ambiguities affecting the targets.
When retrieving the entry's claim inventory and existing mappings, use entry
context with `include=blocks,coverage`; select `block_ids` for a narrower task.
In an area batch, request a root checkpoint if dependent API work needs a current
snapshot; use canonical files until root announces the revision, without running
a writing build yourself.

## Work

1. Inventory the definitions and claims in each block, including examples,
   answers, and explicit witnesses. Make a collective block-to-claims-to-nodes map.
   Cover definitions stated in prose too. Routine proof steps and implementation
   helpers need not each have a block binding.
2. Use the [authoring API](../CONTRIBUTING.md#using-the-authoring-api) to find
   reusable nodes with `area`, `fields=id,description`, and nonempty `q` queries
   drawn from the entry's key concepts, definitions, claims, and related
   prerequisite terms. Include synonyms and alternative names or notation through
   repeated `q` parameters: terms within one query must all match; separate queries
   are alternatives. Use exact `module`/`declaration` filters when bindings are
   known. Refine or broaden the searches as needed, including other areas or
   global search; use `usage=unmapped` without an area to find nodes without block
   mappings. Reserve an unfiltered area inventory for cases where targeted searches
   are insufficient, rather than collecting the whole area by default.
   Load shortlisted node records and their consumers. Inspect actual signatures,
   relevant definition bodies, and library declarations in the pinned Lean sources;
   prefer suitable direct bindings over duplicate wrappers. Explain specializations
   and representation differences using the
   [binding and proof-planning contract](../docs/formal.md#bindings-and-proof-planning).
3. Implement missing definition bodies and state missing theorems with `by sorry`.
   Include the necessary translation, preservation, and admissibility statements
   when representations or proof calculi differ. Final targets must concern the
   actual shared-language theory/definition and the specified witnesses or maps.
   Bridge proofs belong to step 6, not this preparation stage. Preserve existing
   proofs and follow the general-theory versus illustrative-example module split.
   Report substantive constructions or intermediate arguments that preparation
   exposes but the prose leaves unexplained, under the
   [exposition and formalization rule](../docs/corpus.md#exposition-and-formalization).
4. Create or update node records and `data-formal` mappings. Write descriptions
   under the [node contract](../docs/formal.md#formal-nodes), set direct
   proof-planning hints, and keep genuinely unplanned coverage distinguishable
   from blocks with nothing to formalize. Leave logical-strength claims unbound
   when their intended logical setting is not encoded; explain the limitation.
   Do not fabricate verification results or generated summaries.

## Checks

- Ensure the affected modules compile and inspect elaborated target signatures.
  A required full build can supply the compilation check; use focused compilation
  when that build is deferred. Unfinished theorem proofs are expected at this
  stage; missing declarations or invalid definitions are not.
- For a standalone task, finish every corpus edit, including description-only,
  formatting, or mapping changes, with a writing build and commit changed
  generated JSON, including `corpus/index.json`. Use `build --no-lean`, or full `build` when
  required by the [shared build rules](../CONTRIBUTING.md#validation-and-submission).
  The read-only `build --no-lean --check` does not refresh the index and cannot
  replace this step. Statistics-only updates are exempt. For an ongoing batch,
  defer the writing build to its final mutating stage and record the requirement
  in the handoff; do not add a no-Lean build if a full build will satisfy it.
  In an area batch, root owns coordinated index checkpoints and the final full
  build; use focused compilation and do not publish generated data yourself.
- Read and render new or edited node descriptions to check notation, intended
  symbols, delimiters, and KaTeX output. Do not redo the human-entry layout audit.

## Deliverable

Return the coverage map, new/reused/rebound/retired nodes, prepared targets and
unproved bridges, representation decisions, checks, and unresolved correspondence
questions. Include generated-data changes when refreshed, or identify a deferred
root refresh and required shared-file edits within an area batch. Passing
compilation is not correspondence review or proof completion. In an area batch,
request step-5 review from root, apply target corrections through step 4, and
request focused rereview from root before continuing to step 6.
Root alone assigns or spawns those reviewers.
