# Step 3: Review the human entry

Independently review human mathematics and presentation. Follow the
[shared execution rules](../CONTRIBUTING.md#running-one-step-with-an-ai-agent) and
[review-assignment protocol](../CONTRIBUTING.md#running-an-area-pipeline).
Authored entry content remains read-only.

## Inputs

- Entry ID or entry selection and optional narrower review scope.
- Drafting handoff, agreed plan and relevant source assessments when available.
- The actual applied integration files/blocks, identified by root in an area batch.

## Context

Read every claim, proof, example and hidden answer within scope, plus entry
metadata and the relevant applied integration changes. Use the
[corpus contract](../docs/corpus.md); a drafting self-check does not establish
correctness. Reuse source assessments unless a concrete question needs investigation.

Use the [authoring API](../CONTRIBUTING.md#using-the-authoring-api) entry context
with `include=blocks,references,navigation` and `include_answers=true`.
Use `block_ids` only for an explicitly narrower review; a full review covers every
block. Inspect assigned placement through compact area listings and retrieve only
related planning records or source records needed for an investigation.

## Work

1. Check the claims and proofs: hypotheses, quantifiers, domains, conclusions,
   equivalence directions, witnesses, boundary cases and circular reasoning.
   Assess axiom-strength claims under their stated assumptions and whether the
   explanations supply the important steps at the intended level.
2. Check definitions, notation, local prerequisites, citations and linked results.
   Investigate sources where correctness or attribution is uncertain; do not
   repeat source discovery or unchanged publication audits.
3. Assess readability, the standalone abstract, plain-text title, main-result
   emphasis, figures and realistic reading time. Inspect desktop and relevant
   narrow layouts, including hidden answers, against the
   [display-layout contract](../docs/corpus.md#mathematics-figures-and-assets).
   Flag violations and propose corrections; do not edit them. For a requested
   line-break audit, enumerate every explicit break.
4. Check fidelity to the assigned scope, area-specific perspective and placement.
   Judge deliberate overlap by its value to readers; shared subject matter alone
   is not a defect. Report newly exposed dependency or global-order conflicts to
   root rather than replanning the area.
5. Review the entry's references and the relevant applied integration changes.
   Identify missing, stale or incorrect links and fulfilled planning items left
   behind. Do not treat proposed edits as applied; do not repeat step 2's broad
   consumer search or unrelated planning cleanup.

## Checks and deliverable

The independent reading and rendering review above is this step's check. Use
`build --no-lean --check` only to investigate a concrete structural/reference
concern. No routine writing build, Lean inspection or formal-binding audit belongs
here; newly inspected external sources follow the shared register rules.

Return prioritized findings with block/file references, consequences and proposed
corrections. Distinguish errors from optional improvements, state the reviewed
scope and unavailable checks, and route human corrections to step 2. Do not rewrite
the entry, reference planning, mappings or proofs.
