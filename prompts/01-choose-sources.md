# Step 1: Choose sources and scope

Follow the [shared execution rules](../CONTRIBUTING.md#running-one-step-with-an-ai-agent).
Own source selection and mathematical scope; return a plan, not an entry or formal bindings.

## Inputs

- Topic.
- Optional intended audience, entry ID, scope, source preferences, and existing
  planning material. Infer a coherent level from nearby entries when unspecified.

## Context

Inspect nearby entries, `corpus/area_entries.json`, and relevant
[planning records](../corpus/reference-planning/index.json). Use the
[scope](../CONTRIBUTING.md#prerequisites-and-scope),
[reading-order](../CONTRIBUTING.md#reading-order), and
[citation](../docs/corpus.md#entry-metadata) contracts.

Use the [authoring API](../docs/app.md#authoring-api) under the
[shared usage rules](../CONTRIBUTING.md#using-the-authoring-api) to list entries
with `area` and `fields=id,title,reading_position` for placement. Add `summary`
when titles do not establish scope. Search blocks with topic-specific `q` and
`include_answers=true` for human prerequisites, starting in the relevant area and
widening when needed. Retrieve shortlisted prerequisite blocks with `block_ids`
and `include=blocks,references`; add `navigation` when assessing placement.
Look up source records by publication URL or consuming entry, then read their
relevant findings, prioritizing `severity=serious`. Query planning by the proposed
entry ID or area and relevant kind. Use the
[registry lookup workflow](../docs/corpus.md#navigating-source-and-planning-records);
do not read either complete registry. Consult the selected publications directly.

## Work

1. Select and inspect the source passages supporting the proposed definitions,
   results, examples, and proofs. Record exact editions, locations, and access
   limits. Assess hypotheses, deductions, and substantial imported prerequisites;
   establish a repair or alternative argument for any affected claim. Reuse
   applicable existing source assessments rather than repeating unchanged checks.
   Maintain the [source register](../docs/corpus.md#source-errors) for material
   actually inspected; distinguish confirmed mathematical defects from valid
   compression, missing explanation, and uncertainty.
2. Choose a coherent reading unit. Map its prerequisites to existing entry/block
   IDs and check their assumptions, including axiom strength where relevant.
   Separate short supporting lemmas from substantial missing theories; narrow or
   defer unsupported scope explicitly. Available Lean declarations do not supply
   missing human exposition.
3. Propose a stable ID, plain-text title, primary area, reading-order placement,
   and outline. Map the outline to precise sources and proposed `based_on`
   citations. Identify motivating examples and any figure-reuse requirements.
4. Note relevant outstanding reference-planning tasks and known consuming blocks
   for the drafting handoff. Full incoming-reference discovery and integration
   belong to step 2. Leave reference planning and existing entries unchanged.

## Checks

Check source provenance, mathematical support, and prerequisite coverage as part
of the work above. If source records changed, rebuild their catalogs and validate
records and links under the [registry contract](../docs/corpus.md#navigating-source-and-planning-records).
No other corpus validation, rendering, Lean/library search, or build is required for this plan.
Formal reuse and signature inspection belong to step 4.

## Deliverable

Return the scope and outline, source-to-outline map and citation objects,
prerequisites and placement, checked repairs and unchecked passages, relevant
integration candidates, and unresolved drafting questions. Report source-register
changes when made. Do not create entries, nodes, proofs, or build-generated proof metadata.
