# Step 6: Prove nodes

Follow the [single-step execution instructions](../CONTRIBUTING.md#running-one-step-with-an-ai-agent).
Complete this step using the supplied inputs and current repository files;
return its deliverable without starting the next stage.

Prove the selected formal nodes for a Lemmatheca entry.

## Inputs

- Entry ID or explicit node selection (required): identify the requested targets.
  For an entry with no narrower selection, work on its remaining unverified nodes,
  including proofs that depend on unsupported axioms.
- Constraints and GitHub review findings (optional): use the supplied scope and
  mathematical decisions; inspect the actual sources before relying on saved flags.
- Mode (optional): default to corpus proving. Use human-proof translation or a
  measured experiment only when requested, with the relevant proof or run
  specification supplied.

## Context

Read the [project overview](../README.md), [corpus guide](../docs/corpus.md),
[formalization guide](../docs/formal.md), and [contribution workflow](../CONTRIBUTING.md).
Inspect the human entry, selected node descriptions and declarations, proof-planning
hints, and Lean sources. Preserve unrelated work and the pinned environment.
Consult [Source errors](../corpus/source-errors.md) before following an external
source argument. Save new confirmed source defects, checked repairs, and extensions
of reviewed coverage using the [maintenance contract](../docs/corpus.md#source-errors).
Prioritize false statements, invalid constructions, and failed deductions; valid
compression and missing explanation are not errors. A proof-search difficulty or
an incorrect corpus binding alone is not evidence of a source defect. Report any
saved register changes and distinguish the corpus repair from upstream correction.

## Work

1. Establish which selected nodes have unfinished proofs or unsupported axioms
   from the actual sources and relevant checks. The verified flag records the last successful build, not a
   live source audit. There is no in-app approval state or hash to consult; take
   scope from the request and agreed mathematical statements. Resolve relevant
   correspondence findings before changing the affected target, while continuing
   independent proof work where possible.
2. Preserve intended descriptions, theorem statements, definition bodies, and node
   targets. Replace unfinished proofs without weakening the mathematics. Use local
   have statements or unregistered helpers for routine steps. If a target or
   representation must change, explain why and identify the correspondence review
   it needs. Do not silently rebind nodes or edit exposition to fit an easier proof.
3. Use dependencies as proof-planning hints, working through useful prerequisites
   first. They are not reading order or a complete extracted dependency graph.
   An unfinished hint does not automatically make this node unverified, but actual
   transitive use of sorry does. Keep any proof-plan edits direct and explain them.
   Choice is permitted by default. Follow the
   [assumption guidance](../CONTRIBUTING.md#prerequisites-and-scope) for claims about
   weaker axiom systems; report any strength the encoding cannot express. Use
   [kernel-axiom reports](../docs/formal.md#inspecting-kernel-axioms) when needed to
   diagnose verification failures.
4. In corpus-proving mode, follow the human proof where given and reuse Lean/mathlib
   results rather than rebuilding library foundations. If a library declaration
   already covers the whole target, report a possible direct binding; using it is
   library reuse, not evidence of translating the displayed human argument.
5. In proof-translation mode, identify the actual human proof and preserve its
   important intermediate reasoning. Calling the target, an alias, or a stronger
   existing theorem does not translate that argument. If no human proof is present,
   label the work as proof search. In measured mode, follow the supplied retrieval
   rules, budgets, and attempt limits. Keep attempts, feedback, interventions, and
   measurements in separate logs, not corpus metadata. Do not invent measurements.
6. Check proofs with Lean. Do not bypass failures by adding unsupported axioms, sorry, admit,
   or unchecked shortcuts. Use the single formal/ project and keep module organization
   compact. Put reusable lemmas in the general theory layer, currently
   `Lemmatheca.SetTheory`, even if they have only one current caller. `Entry/` is
   reserved for particular illustrative examples and counterexamples with no
   wider use, and their example-specific helpers. General theory must not import
   entry modules. Update imports and module bindings when a permitted source move
   requires it.
7. Inspect Lean and Lake warnings, including those exposed by the full build.
   Fix causes in project-owned Lean sources while preserving the agreed mathematics;
   do not weaken statements, add proof shortcuts, suppress diagnostics through local
   or global linter settings, or change the pinned environment to quiet diagnostics.
   Naming intentionally unused parameters with a leading underscore is legitimate
   cleanup that preserves their hypotheses. Follow the
   [build-warning guidance](../docs/formal.md#build-warnings) for deliberately
   unfinished declarations and external dependency warnings.

## Checks

Check edited proofs with Lean while working. After proof changes, run from the
repository root:

```sh
uv run python app/manage.py build
```

The build checks the whole registry, including transitive axioms, and regenerates
node verification/signatures/source lines and entry-list summaries. Commit generated
`corpus/nodes/*.json` and `corpus/entries/*/entry.json` changes with the proofs.
Leave `corpus/statistics.json` unchanged; automation refreshes it on `main` after
merging. A plain
`lake build` is useful while working but does not update this JSON.
Inspect the full build output, not just its exit status. After warning fixes, rerun
the full command above and inspect its diagnostics again before reporting the
warnings resolved. Distinguish remaining diagnostics from project sources and
pinned dependencies, giving their locations and reasons. Existing deliberately
unfinished declarations outside the selected work may retain `sorry` warnings;
report them without claiming those proofs complete. Unbound nodes and Not verified
results do not require artificial bindings or proofs merely to quiet build output.
Run `uv run python app/manage.py validate_corpus` if node records, bindings, or
entry structure also changed. Run relevant catalog tests only if reader or
build-tooling code changes, or when investigating an integration failure.

Failed compilation or declaration checks leave previous results intact. Treat that
as a failed refresh, not proof of the current source state. Fix failures in scope
and report unrelated blockers without discarding saved data or changing unrelated
statements. After a successful build, confirm completed nodes have `verified: true`,
no direct or inherited sorry, and no unsupported axioms.
Unfinished proofs and unsupported axioms can compile while remaining Not
verified; the build still checks all other nodes. A successful build is not by
itself a completion claim. Compare any changed proof with the human text; repair
a clear mathematical error in the text when authorized, explain the correction,
and identify any renewed correspondence review needed.

## Deliverable

Return proved node IDs, checks performed, any statement/binding changes needing
GitHub review, deviations from the human argument, warning causes fixed, and any
remaining diagnostics with their project or dependency origin. List remaining
selected work with concrete reasons. Do not claim complete entry coverage merely because
the selected proofs are verified when blocks remain unplanned or claims uncovered.
