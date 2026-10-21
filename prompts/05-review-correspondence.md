# Step 5: Review correspondence

Independently compare human claims with formal targets and coverage. Follow the
[shared execution rules](../CONTRIBUTING.md#running-one-step-with-an-ai-agent) and
[review-assignment protocol](../CONTRIBUTING.md#running-an-area-pipeline).
Authored entry content, node bindings and Lean sources remain read-only.

## Inputs

- Entry ID or entry selection, with current mappings and declarations.
- Optional preparation coverage map, representation decisions and review findings.

## Context

Read the human claims, node descriptions, actual Lean types and relevant
definition bodies. Apply the
[mapping contract](../docs/corpus.md#block-to-node-mapping) and
[binding and representation contract](../docs/formal.md#bindings-and-proof-planning).
Names, saved signatures and verification flags are not evidence of correspondence.
Intentional `sorry` bodies are unfinished proof work, not by themselves a defect
in the prepared statements.

Use the [authoring API](../CONTRIBUTING.md#using-the-authoring-api) entry context
with `include=blocks,nodes,coverage`; select `block_ids` for a narrower task.
For suspected duplicate bindings, use exact `declaration` and
`fields=id,description,module,declaration` without an area filter; add `module`
when the concern is confined to that module. Inspect consumers where reuse affects
coverage. Do not repeat step 4's general reuse search.

## Work

1. Independently check every human definition and claim against its mapping,
   including examples, hidden answers and specified constructions or witnesses.
   Do not assume the preparation map is complete. Distinguish missing coverage,
   intentionally unbound claims and empty/unplanned mappings.
2. Compare each claim and node description with actual types and definitions:
   hypotheses, quantifier order, witness dependencies, specified-map identities,
   domains, instances, conventions and foundation limits. Detect vacuous or weaker
   substitutes and unjustified specializations.
3. Check that representation bridges connect the relevant syntaxes, scopes and
   theories, and that derived proof rules have syntactic admissibility targets.
   The complete prepared target set must imply the human claim and its stated
   consequences. Missing bridge statements are coverage defects; proving faithful
   prepared statements belongs to step 6.
4. Identify redundant bindings, duplicate targets, misplaced modules and misleading
   dependency hints within scope. Report newly exposed substantive arguments
   missing from the human text under the shared change-routing rules; do not
   audit all transitive library code or reorganize unrelated modules.

## Checks and deliverable

Use focused read-only Lean checks only to resolve type, instance or representation
questions. Inspect description rendering only for an ambiguous notation or concrete
presentation concern, and use `build --no-lean --check` only for a structural or
binding-reference concern. No routine writing build, proof completion, source
re-audit, reference-integration sweep or general presentation review belongs here.

Return prioritized block/node/declaration findings, consequences and proposed
corrections, plus the independently checked coverage map or corrections to the
supplied one. Separate incorrect targets, missing coverage, representation gaps,
unproved work and optional simplifications. Route formal corrections to step 4
and human corrections to steps 2/3; do not make those edits during review.
