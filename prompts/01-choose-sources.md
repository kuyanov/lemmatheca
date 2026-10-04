# Step 1: Choose sources and scope

Follow the [single-step execution instructions](../CONTRIBUTING.md#running-one-step-with-an-ai-agent).
Complete this step using the supplied inputs and current repository files;
return its deliverable without starting the next stage.

Choose the sources and scope for a new Lemmatheca entry.

## Inputs

- Topic (required): the mathematics the entry should develop.
- Intended entry ID (optional): otherwise propose a stable descriptive ID.
- Reader, prerequisites, scope, and exclusions (optional): infer a coherent unit
  from nearby entries when unspecified and state the proposed boundaries.
- Sources or selection criteria (optional): inspect supplied books, notes, papers,
  or URLs; otherwise find suitable sources and explain the choice.

## Context

Read the [project overview](../README.md), [corpus guide](../docs/corpus.md),
[formalization guide](../docs/formal.md), and [contribution workflow](../CONTRIBUTING.md).
Inspect nearby entries, `corpus/taxonomy.json`, and `corpus/area_entries.json`.
Respect repository instructions and preserve unrelated work.

## Work

1. Inspect the actual sources. Identify the chapters, sections, or pages supporting
   the proposed definitions, results, examples, and proofs. Verify bibliographic
   details. Distinguish inspected sources from inaccessible suggestions; never
   invent citations or claim to have read unavailable material.
   Check the mathematical rigor of the passages being used, including definitions,
   hypotheses, proof steps, examples, and cited prerequisites. Trace nontrivial
   omissions and appeals to other results; a source's reputation alone does not
   establish correctness. Distinguish a valid compressed argument from a genuine
   gap, and distinguish source defects from uncertainty in your own checking.
   Report every identified error or gap with its source location, affected claim,
   consequence, and a proposed repair or supplementary source. Mark unavailable
   or unchecked arguments explicitly. Return this assessment for use in step 2,
   before drafting the entry.
2. Propose a coherent reading unit with clear prerequisites and boundaries. Link
   existing entries where useful rather than repeating whole explanations, while
   keeping enough context to understand the new entry. Do not expand its scope
   merely to match available Lean lemmas.
   Treat reading-order placement and area membership as provisional: entries may
   be reordered or moved into separate subareas. Identify prerequisites by stable
   entry and block IDs, independently of adjacency or a shared area. Plan named
   links rather than references to "the previous entry" or "the next entries."
3. Inspect `corpus/nodes/` and the pinned Lean/mathlib sources for likely reusable
   bindings. Read signatures and relevant definitions, not just names. Flag
   representation differences and missing results without starting formalization.
4. Plan original exposition and record precise source credit. Identify any figure
   reuse requirements; do not copy substantial passages or figures without a basis
   for doing so. Keep technical formalization details out of the planned human prose.

## Checks

Verify the proposed entry ID and reading-order placement against the current
corpus, and check each citation against an inspected source. Planning changes no
corpus files, so it requires no validator, build, or catalog test run. If Lean
sources are unavailable, record which reuse candidates could not be checked and
complete the source plan.

## Deliverable

Return the proposed ID, scope, outline, entry links, primary area and reading-order
placement, and a source-to-outline map with precise locations. Include proposed
`based_on` citation objects following the [corpus guide](../docs/corpus.md).
Include the source-rigor assessment: findings with precise locations, proposed
repairs, and any unchecked material. State explicitly if no gaps were found in the
inspected passages, without claiming more than was checked. List checks performed
and unresolved questions for the drafting step.
Do not create entries, nodes, proofs, or generated summaries at this stage.
