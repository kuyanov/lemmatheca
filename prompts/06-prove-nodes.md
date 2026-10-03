# Step 6: Prove nodes

Follow the [single-step execution instructions](../CONTRIBUTING.md#running-one-step-with-an-ai-agent).
Complete this step using the supplied inputs and current repository files;
return its deliverable without starting the next stage.

Prove the selected formal nodes for a Lemmatheca entry.

## Inputs

- Entry ID or explicit node selection (required): identify the requested targets.
  For an entry with no narrower selection, work on its remaining unfinished nodes.
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

## Work

Check the source-rigor findings and their resolutions for the selected claims,
especially when following or translating a human proof. If an applicable assessment
is missing, inspect the relevant source arguments and report errors, gaps, and
unchecked material before changing affected formalizations. Give precise source
locations and consequences, and establish a checked repair before relying on a
defective argument. Continue independent proof work where possible. Distinguish
proving a result by another route from repairing or translating its source proof;
a successful Lean proof does not retroactively validate the source argument.

1. Establish which selected proofs are unfinished from the actual sources and
   relevant checks. The verified flag records the last successful build, not a
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
6. Check proofs with Lean. Do not bypass failures by adding axioms, sorry, admit,
   or unchecked shortcuts. Use the single formal/ project and keep module organization
   compact. Update imports and module bindings when a permitted source move requires it.

## Checks

Run from the repository root:

```sh
uv run python app/manage.py validate_corpus
uv run python app/manage.py build
uv run python app/manage.py test catalog
```

Validation can also run during authoring without Lean or generated results.
The build checks the whole registry, including transitive axioms, and regenerates
node verification/signatures/source lines and entry-list summaries. Commit generated
`corpus/nodes/*.json` and `corpus/entries/*/entry.json` changes with the proofs.
Leave `corpus/statistics.json` unchanged; automation refreshes it on `main` after
merging. A plain
`lake build` is useful while working but does not update this JSON.

Failed compilation or declaration checks leave previous results intact. Treat that
as a failed refresh, not proof of the current source state. Fix failures in scope
and report unrelated blockers without discarding saved data or changing unrelated
statements. After a successful build, confirm completed nodes have `verified: true`
and no direct or inherited sorry. Unfinished proofs can compile while remaining
Not verified, so a successful build is not by itself a completion claim.

## Deliverable

Return proved node IDs, checks performed, any statement/binding changes needing
GitHub review, and deviations from the human argument. List remaining selected
work with concrete reasons. Do not claim complete entry coverage merely because
the selected proofs are verified when blocks remain unplanned or claims uncovered.
Include source gaps reported before the proof work, checked repairs, and remaining
source-rigor concerns.
