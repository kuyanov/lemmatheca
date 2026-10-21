# Step 4: Prepare formal nodes

Own formal definitions, target statements, node records and block mappings.
Do not prove new theorems. Follow the
[shared execution rules](../CONTRIBUTING.md#running-one-step-with-an-ai-agent) and
[area-pipeline protocol](../CONTRIBUTING.md#running-an-area-pipeline).

## Inputs

- Entry ID or entry selection and the current human entry.
- Optional human-review findings and agreed mathematical revisions.

## Context

Read the human claims and relevant findings. Apply the
[mapping contract](../docs/corpus.md#block-to-node-mapping),
[binding and representation contract](../docs/formal.md#bindings-and-proof-planning),
[node-description contract](../docs/formal.md#formal-nodes), and
[module-layout rules](../docs/formal.md#module-layout).
Do not repeat human review or source selection; report ambiguities affecting targets.

Use the [authoring API](../CONTRIBUTING.md#using-the-authoring-api) entry context
with `include=blocks,coverage`; select `block_ids` for a narrower task. Search
reusable nodes with `area`, `fields=id,description` and nonempty `q` queries for
key concepts, claims and related prerequisite terms. Use repeated `q` values for
alternatives and exact `module`/`declaration` filters for known bindings. Broaden
to other areas or global search only as needed; find unmapped nodes with
`usage=unmapped` and no area filter. Load shortlisted records and their consumers,
then inspect actual pinned Lean sources rather than saved signatures.

## Work

1. Map each block's definitions and claims to nodes, including examples, hidden
   answers and explicit witnesses. Cover definitions stated in prose too;
   routine proof steps and implementation helpers need no individual binding.
2. Select suitable existing nodes and direct library bindings. Check actual types,
   relevant definition bodies, instances and specializations. Avoid duplicate
   wrappers, and record representation differences requiring bridges.
3. Implement missing definitions and state missing theorems with `by sorry`,
   preserving existing proofs. Include translation, preservation and syntactic
   admissibility targets whenever representations or calculi differ. The complete
   target set must establish the actual shared-language claim, including its
   specified witnesses or maps. Put declarations with their appropriate
   expository owner under the module-layout rules. Bridge proofs belong to step 6.
4. Create or update node records, mathematical descriptions, direct proof-planning
   hints and `data-formal` mappings. Distinguish unmapped blocks from blocks
   with nothing to formalize. Leave logical-strength claims unbound if their
   intended setting is not encoded, explaining the limitation. Do not fabricate
   `verified`, `signature` or `declaration_line` fields in node JSON, or edit
   generated index results; the build produces them.

## Checks

Compile affected modules and inspect elaborated target signatures, even when
publication is deferred. Unfinished theorem proofs are expected; missing
declarations and invalid definitions are not. Read and render new or edited node
descriptions to check notation and KaTeX output; do not redo the human layout audit.
Apply the [shared build rules](../CONTRIBUTING.md#validation-and-submission) for
publication, with root coordinating area-batch builds.

## Deliverable

Return the coverage map, new/reused/rebound/retired nodes, prepared targets and
unproved bridges, representation decisions, checks and correspondence questions.
Identify newly exposed exposition gaps under the shared change-routing rules.
Request step-5 review under the area protocol; compilation does not establish
correspondence or proof completion.
