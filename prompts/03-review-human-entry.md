# Step 3: Review the human entry

Follow the [shared execution rules](../CONTRIBUTING.md#running-one-step-with-an-ai-agent).
Independently review human mathematics and presentation. Entry files remain read-only.

## Inputs

- Entry ID or entry selection.
- Optional narrower review scope, drafting handoff, and relevant source material.

## Context

Read the current entry and metadata, including proofs, examples, figures, and
hidden answers within the requested scope. Use the [corpus contract](../docs/corpus.md),
[scope guidance](../CONTRIBUTING.md#prerequisites-and-scope), and
[reading-order criteria](../CONTRIBUTING.md#reading-order). Judge the actual entry
independently; a drafting self-check is not this review.

Use the [authoring API](../docs/app.md#authoring-api) under the
[shared usage rules](../CONTRIBUTING.md#using-the-authoring-api) to retrieve the
requested entry context, including answers, and relevant references. Use area
listings to inspect placement within the reading order. Keep retrieval within
the requested human-review scope.

## Work

1. Check claims and proofs: hypotheses, quantifiers, domains, conclusions,
   equivalence directions, witnesses, boundary cases, and freedom from circular
   reasoning. Assess axiom-strength claims under their stated assumptions.
   Check that explanations supply the important steps at the intended level.
2. Check definitions, notation, prerequisites, citations, and linked results.
   Consult sources where correctness or attribution needs investigation; do not
   repeat source discovery or re-audit unchanged publications by default.
   Record any newly confirmed source defect or inspected scope under the
   [source-error contract](../docs/corpus.md#source-errors).
3. Review readability, the standalone abstract, title, emphasis, figures, and
   rendered mathematics against the corpus contract. Main-result boxes must
   contain their hypotheses and conclusions. Inspect desktop and relevant narrow
   layouts, including hidden answers. Flag any display requiring horizontal
   scrolling at the normal desktop content width. Split an overflowing row of
   independent claims into separate displays; keep each equation, implication, or equivalence horizontal
   when it fits, and break a genuinely long single statement only at meaningful
   mathematical boundaries. For a line-break audit, enumerate every explicit
   break and keep short formulas and identity lists compact. Formula scrolling
   on mobile is acceptable and does not justify extra line breaks.
4. Check reading order and the entry's references. Review the relevant integration
   changes from step 2 and report missing, stale, or incorrect links/planning
   items. Do not repeat a corpus-wide consumer search or unrelated planning
   cleanup. Return proposed corrections; do not edit reference planning.

## Checks

The independent reading and rendering review above is this step's check. Run
corpus validation only to investigate a specific structural/reference concern.
No writing build, catalog tests, Lean proof checks, or formal-binding audit is
required. Maintain source-register links only if that register was changed.

## Deliverable

Return prioritized findings with block/file references, consequences, and concrete
corrections; separate errors from optional improvements. State reviewed scope,
unavailable checks, and revisions needed before formal preparation. Include
relevant integration findings and source-register changes when applicable.
Do not rewrite entries, metadata, mappings, or proofs, or set approval fields.
