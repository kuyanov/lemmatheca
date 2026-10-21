# Step 5: Review correspondence

Follow the [shared execution rules](../CONTRIBUTING.md#running-one-step-with-an-ai-agent).
Independently compare the human mathematics with its formal targets and coverage.
Authored entry content, node bindings and Lean sources remain read-only;
source-register maintenance follows the shared exception.

In the [area pipeline](../CONTRIBUTING.md#running-an-area-pipeline), the entry
driver requests review and root alone assigns or spawns the reviewer: root, a new
agent or another entry owner. As reviewer, you must not have authored the reviewed
text or targets. Return findings to the entry owner. If delegated, also send them
to root and leave reviewer assignment to root.

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
   Check whether the entry's formal development exposes substantive constructions
   or arguments compressed or missing in the human text; this does not require
   auditing all transitive library code. A large excess of formal code is a
   warning under the
   [exposition and formalization rule](../docs/corpus.md#exposition-and-formalization).
   Route necessary expansion and splitting to steps 2/3 and root's scope/order
   coordination rather than accepting unexplained mathematics as implementation detail.
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
ambiguous or a concrete presentation defect is suspected. Use `build --no-lean --check`
only for a structural/binding-reference concern. No routine writing build is
required; source-register edits still need the refresh described below. No proof
completion, source re-audit, reference-planning sweep, or general presentation
review is required.

## Deliverable

Return prioritized findings with block/node/declaration references, consequences,
proposed corrections, the independent coverage table, and checks performed.
Separate incorrect targets, missing coverage, unproved work, representation gaps,
and optional simplifications. Route corrections to step 4; report any human error
for steps 2/3. Record new external-source findings only if source consultation
actually required it. Do not change bindings or proofs or set approval fields.
Source-record edits follow the [shared build rules](../CONTRIBUTING.md#validation-and-submission)
for catalog regeneration and record validation. In an area batch, if you are a
delegated reviewer, send shared-record changes to root unless exclusive ownership
was assigned, and leave publication to root. If you are root, apply those changes
and refresh the catalogs at a coordinated checkpoint or the final build.
The entry driver applies corrections through step 4 and requests
focused step-5 rereview from root before proving; root assigns it. Human
corrections return through steps 2/3.
