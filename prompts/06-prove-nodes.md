# Step 6: Prove nodes

Follow the [shared execution rules](../CONTRIBUTING.md#running-one-step-with-an-ai-agent).
Own proof completion for the selected formal targets, preserving their mathematics.

## Inputs

- Entry ID or explicit node selection. Without a narrower selection, work on the
  entry's remaining unfinished or unsupported proofs.
- Optional constraints, correspondence findings, and proof-translation or measured
  experiment specification. Default to ordinary corpus proving.

## Context

Inspect the selected statements, definition bodies, relevant human arguments,
proof-planning hints, and actual Lean sources. Use the
[formalization guide](../docs/formal.md) for library organization, permitted axioms,
and build warnings. Saved verification flags describe the last successful build;
check actual unfinished dependencies where needed. Reuse applicable earlier
handoffs; do not repeat the full human or correspondence review.

## Work

1. Replace the selected unfinished proofs, including necessary bridge and
   admissibility dependencies. Preserve the intended statements, definitions,
   representations, and specified maps. Do not weaken targets, add unsupported
   axioms, `sorry`, `admit`, or unchecked shortcuts to bypass failures.
2. Follow the human argument where given and reuse suitable library results.
   Keep routine helpers unregistered and reusable mathematics in general theory.
   In explicit proof-translation mode, preserve the argument's important reasoning
   and distinguish translation from calling an existing target or stronger theorem.
   In measured mode, follow the supplied retrieval/attempt rules and keep logs
   outside corpus metadata; do not invent measurements.
3. If a statement, definition, binding, or representation must change, identify
   the affected step-4 revision and step-5 review using the
   [change rules](../CONTRIBUTING.md#stage-responsibilities). Do not alter exposition
   or targets merely to fit an easier proof. A new proof of an unchanged target
   does not itself require another correspondence audit.
4. Inspect Lean/Lake diagnostics and fix warning causes in affected project code
   under the [warning contract](../docs/formal.md#build-warnings). Preserve the
   mathematics and environment pins; do not suppress diagnostics or complete
   unrelated proofs solely to quiet their reports.

## Checks

- Use focused compilation as needed while editing. At completion, run the writing
  build required by the [shared check matrix](../CONTRIBUTING.md#validation-and-submission).
  Inspect the full output and the selected nodes' refreshed verification results.
- Confirm completed targets have no direct/inherited unfinished proofs or
  unsupported axioms. Use focused kernel-axiom reports to diagnose failures.
  A successful build alone is not a completion claim.
- Run other checks only for corresponding changes: corpus validation for changed
  node records/mappings/entry structure, rendering for edited prose/descriptions,
  and catalog tests for reader/build-tooling changes or an integration failure.
  Proof-only work requires no reference-planning or presentation audit.

## Deliverable

Return proved node IDs, refreshed generated files, checks and diagnostics,
deviations from the human argument, and concrete remaining selected work.
Distinguish project warnings from dependency or unrelated unfinished-proof warnings.
Report necessary target changes and their review scope; do not claim whole-entry
coverage merely because the selected proofs are verified.
