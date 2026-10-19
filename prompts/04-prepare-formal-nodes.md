# Step 4: Prepare formal nodes

Follow the [shared execution rules](../CONTRIBUTING.md#running-one-step-with-an-ai-agent).
Own formal definitions, target statements, node records, and block mappings.
Do not prove new theorems.

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

## Work

1. Inventory the definitions and claims in each block, including examples,
   answers, and explicit witnesses. Make a collective block-to-claims-to-nodes map.
   Cover definitions stated in prose too. Routine proof steps and implementation
   helpers need not each have a block binding.
2. Use the [authoring API](../CONTRIBUTING.md#using-the-authoring-api) to collect
   reusable nodes from the entry's area: node search with `area`,
   `fields=id,description`, and no `q`. Search alternative phrases with repeated
   `q`, or use exact `module`/`declaration` filters. Widen to other areas or global
   search when useful; use `usage=unmapped` without an area to find nodes without
   block mappings.
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
- Run corpus validation after the preparation batch. Apply the
  [shared build rules](../CONTRIBUTING.md#validation-and-submission) to refresh
  generated data for a standalone handoff or at the end of an ongoing batch.
- Read and render new or edited node descriptions to check notation, intended
  symbols, delimiters, and KaTeX output. Do not redo the human-entry layout audit.

## Deliverable

Return the coverage map, new/reused/rebound/retired nodes, prepared targets and
unproved bridges, representation decisions, checks, and unresolved correspondence
questions. Include generated-data changes when refreshed, or identify a deferred
refresh within an ongoing batch. Passing compilation is not correspondence review
or proof completion; those belong to steps 5 and 6.
