# Step 6: Prove nodes

Own proof completion for the selected targets, preserving their mathematics.
Follow the [shared execution rules](../CONTRIBUTING.md#running-one-step-with-an-ai-agent)
and [area-pipeline protocol](../CONTRIBUTING.md#running-an-area-pipeline).

## Inputs

- Entry ID or explicit node selection. Without a narrower selection, complete the
  entry's remaining unfinished or unsupported proofs.
- Optional correspondence findings, proof-translation constraints or measured
  experiment specification. Default to ordinary corpus proving.

## Context

Inspect the selected statements, definitions, human arguments, proof-planning hints
and actual Lean sources. Use the [formalization guide](../docs/formal.md) for
module ownership, permitted axioms and diagnostics. Reuse earlier handoffs rather
than repeating human or correspondence review.

Use the [authoring API](../CONTRIBUTING.md#using-the-authoring-api) entry context
with `include=nodes,coverage`, selecting `block_ids` where known. For multiple
entries, `/api/coverage/?entry_ids=id-a,id-b` can shortlist mapped targets before
fetching their records and supporting blocks. Saved `verified=false` is only a
candidate filter; inspect current proofs, dependencies and axioms locally. Use
targeted searches for supporting lemmas, not a fresh whole-area inventory.

## Work

1. Prove the selected targets and necessary bridge/admissibility dependencies.
   Preserve statements, definitions, representations and specified maps. Do not
   weaken targets or add unsupported axioms, `sorry`, `admit` or unchecked shortcuts.
2. Follow the human argument where supplied and reuse suitable library results.
   Keep routine proof helpers unregistered and follow the
   [module-layout rules](../docs/formal.md#module-layout). Honor explicit
   proof-translation or measurement constraints; distinguish library reuse from
   translating an argument, keep requested logs outside corpus metadata and never
   invent measurements.
3. Route necessary statement, definition, binding or representation changes
   through steps 4/5 under the
   [change rules](../CONTRIBUTING.md#stage-responsibilities). Report newly exposed
   exposition gaps by the same rules. Do not rewrite targets or prose for an
   easier proof; an unchanged target with a new proof needs no new correspondence
   audit by itself.
4. Inspect Lean/Lake diagnostics and fix warning causes in affected project code
   under the [warning contract](../docs/formal.md#build-warnings). Preserve the
   mathematics and environment pins; do not suppress diagnostics or complete
   unrelated proofs merely to quiet their reports.

## Checks

Use focused compilation while editing. Confirm completed targets have no direct
or inherited unfinished proofs or unsupported axioms, using kernel-axiom reports
where needed. Finish under the
[shared check matrix](../CONTRIBUTING.md#validation-and-submission): a standalone
proof task requires the full writing build; an area worker supplies focused proof
and axiom evidence for root's final integrated build. Inspect verification results
and full diagnostics before claiming completion; successful compilation alone is
insufficient. Proof-only work needs no reference-planning or presentation audit.

## Deliverable

Return proved node IDs, proof/axiom evidence, diagnostics, deviations from the human
argument and concrete remaining selected work. Distinguish project warnings from
dependency or unrelated unfinished-proof warnings. Identify required earlier-stage
revisions and pending shared edits/publication. Claim only the selected coverage
actually verified under the shared build rules.
