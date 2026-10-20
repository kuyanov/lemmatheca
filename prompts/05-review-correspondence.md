# Step 5: Review correspondence

Follow the [shared execution rules](../CONTRIBUTING.md#running-one-step-with-an-ai-agent).
Independently compare the human mathematics with its formal targets and coverage.
Entries, nodes, Lean sources, and generated proof results remain read-only.

## Inputs

- Entry ID or entry selection, with current node mappings and declarations.
- Optional preparation handoff and relevant review findings.

## Context

Read the human claims, node descriptions, actual Lean declarations, and relevant
representation definitions. Use the [mapping contract](../docs/corpus.md#block-to-node-mapping)
and [binding contract](../docs/formal.md#bindings-and-proof-planning).
Inspect current types and definitions rather than trusting names, saved signatures,
or verification flags. Use the
[authoring API](../CONTRIBUTING.md#using-the-authoring-api) entry context with
`include=blocks,nodes,coverage` to organize the requested claims and mappings.
For a block-specific review, select those known IDs with `block_ids`.
Intended `sorry` theorem bodies are unfinished proof work; they are not by
themselves a correspondence defect.

## Work

1. Independently build a block-by-block coverage table. Include definitions,
   examples, hidden answers, and explicit constructions/witnesses. Distinguish
   missing coverage, intentionally unbound targets, and empty/unplanned mappings.
2. Compare each claim and description with the actual declaration type and
   definition bodies. Apply the binding contract to hypotheses, quantifier order,
   witness dependencies, specified-map identities, domains, instances, conventions,
   and foundation limits. Check specializations rather than relying on a plausible
   name or a successful compilation.
3. Inspect representation bridges and their target statements. Translation
   definitions must connect the relevant syntaxes, scopes, and theories; derived
   proof rules need syntactic admissibility/translation targets. Check that the
   complete set of prepared statements would establish the human claim, including
   its consequences. Missing bridge statements are coverage gaps; proving correct
   prepared statements belongs to step 6.
4. Identify redundant bindings, duplicate targets, inappropriate module placement,
   and misleading dependency hints within the reviewed scope. Retain distinct
   claims and specified witnesses. Use node consumers to inspect reuse and affected
   blocks. For suspected duplicate bindings, search with exact `declaration` and
   `fields=id,description,module,declaration`, without an area filter so bindings
   used elsewhere remain visible. Use exact `module` when the check is confined
   to that module.
   Do not repeat the preparation-stage global reuse search or reorganize unrelated
   code.

## Checks

Use focused, read-only Lean checks only for unresolved signatures, instances, or
representation questions. Investigate description rendering only when notation is
ambiguous or a concrete presentation defect is suspected. Run corpus validation
only for a structural/binding-reference concern. No writing build, proof completion,
source re-audit, reference-planning sweep, or general presentation review is required.

## Deliverable

Return prioritized findings with block/node/declaration references, consequences,
proposed corrections, the independent coverage table, and checks performed.
Separate incorrect targets, missing coverage, unproved work, representation gaps,
and optional simplifications. Route corrections to step 4; report any human error
for steps 2/3. Record new external-source findings only if source consultation
actually required it. Do not change bindings or proofs or set approval fields.
If source records changed, rebuild their catalogs and validate those records and
links under the [registry contract](../docs/corpus.md#navigating-source-and-planning-records).
