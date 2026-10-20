# Step 6: Prove nodes

Follow the [shared execution rules](../CONTRIBUTING.md#running-one-step-with-an-ai-agent).
Own proof completion for the selected formal targets, preserving their mathematics.

In the [area pipeline](../CONTRIBUTING.md#running-an-area-pipeline), finish the
assigned entry after its independent reviews. Keep shared-file changes with root
unless exclusive ownership was assigned; report scope or prerequisite gaps rather
than replanning the area.

## Inputs

- Entry ID or explicit node selection. Without a narrower selection, work on the
  entry's remaining unfinished or unsupported proofs.
- Optional constraints, correspondence findings, and proof-translation or measured
  experiment specification. Default to ordinary corpus proving.

## Context

Inspect the selected statements, definition bodies, relevant human arguments,
proof-planning hints, and actual Lean sources. Use the
[formalization guide](../docs/formal.md) for library organization, permitted axioms,
and build warnings. Saved verification flags may be reused from an earlier Lean
run; they do not certify current sources or bindings. Check actual unfinished
dependencies where needed. Reuse applicable earlier
handoffs; do not repeat the full human or correspondence review. Use the
[authoring API](../CONTRIBUTING.md#using-the-authoring-api) entry context with
`include=nodes,coverage` to select mapped targets; treat saved `verified=false`
only as a candidate filter. Use `block_ids` when the proof scope is known blocks.
For a multi-entry batch, `/api/coverage/?entry_ids=id-a,id-b` can select targets
using compact mappings and saved bindings first; then retrieve only the selected
node records and supporting blocks rather than every entry's full node context.
Use selected node records, consumers, and dependency
hints to scope the work, with targeted node searches for reusable helpers. Inspect
actual dependencies and kernel axioms in Lean locally. Do not collect the whole
area's node inventory for each proof task.

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
   If proof development produces much more formal code than human text, apply the
   [exposition and formalization rule](../docs/corpus.md#exposition-and-formalization).
   Report substantive arguments needing fuller explanation or a split to steps
   2/3 and root; proof completion alone does not close that exposition gap.
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

- Use focused compilation as needed while editing. For a standalone task, run full
  `build` with Lean under the
  [shared check matrix](../CONTRIBUTING.md#validation-and-submission).
  Inspect the full output and the selected nodes' refreshed verification results,
  and commit changed generated JSON, including `corpus/index.json`.
  In an area batch, report focused compilation and axiom evidence, then freeze
  owned files for root's final integration audit and full build. Root may also
  run coordinated no-Lean index checkpoints during the batch; these do not verify
  current proofs. Do not run writing builds or claim refreshed Lean verification
  before root's final full build.
- Confirm completed targets have no direct/inherited unfinished proofs or
  unsupported axioms. Use focused kernel-axiom reports to diagnose failures.
  A successful build alone is not a completion claim.
- The full build includes structural validation. Run other checks only for
  corresponding changes: rendering for edited prose/descriptions and catalog
  tests for reader/build-tooling changes or an integration failure.
  Proof-only work requires no reference-planning or presentation audit.

## Deliverable

Return proved node IDs, refreshed generated files, checks and diagnostics,
deviations from the human argument, and concrete remaining selected work.
Distinguish project warnings from dependency or unrelated unfinished-proof warnings.
Report necessary target changes and their review scope; do not claim whole-entry
coverage merely because the selected proofs are verified.
For an area batch, include independent-review dispositions, required shared-file
edits, and the pending root build instead of refreshed generated files.
