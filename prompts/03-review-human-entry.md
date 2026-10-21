# Step 3: Review the human entry

Follow the [shared execution rules](../CONTRIBUTING.md#running-one-step-with-an-ai-agent).
Independently review human mathematics and presentation. Authored entry content
remains read-only; source-register maintenance follows the shared exception.

In the [area pipeline](../CONTRIBUTING.md#running-an-area-pipeline), the entry
driver requests review and root alone assigns or spawns the reviewer: root, a new
agent or another entry owner. As reviewer, you must not have authored the reviewed
text. Return findings to the entry owner. If delegated, also send them to root
and leave reviewer assignment to root.

## Inputs

- Entry ID or entry selection.
- Optional narrower review scope, drafting handoff, and relevant source material.
- For an area batch, root's identification of the exact shared integration
  files/blocks applied and stable for review, and the current index revision
  after any needed checkpoint.

## Context

Read the current entry and metadata, including proofs, examples, figures, and
hidden answers within the requested scope. Use the [corpus contract](../docs/corpus.md),
[scope guidance](../CONTRIBUTING.md#prerequisites-and-scope), and
[reading-order criteria](../CONTRIBUTING.md#reading-order). Judge the actual entry
independently; a drafting self-check is not this review.

Use the [authoring API](../docs/app.md#authoring-api) under the
[shared usage rules](../CONTRIBUTING.md#using-the-authoring-api) to retrieve the
requested entry context with `include=blocks,references,navigation` and
`include_answers=true`. Use `block_ids` for an explicitly narrower review; a full
entry review must cover every block. Use compact area listings to inspect
placement within the reading order. Keep retrieval within the requested
human-review scope.

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
3. Review readability, the standalone abstract, title, emphasis, figures,
   reading-time estimate, and rendered mathematics against the corpus contract.
   Estimate time from the actual arguments and questions; do not lower the
   metadata to fit a target. Main-result boxes must contain their hypotheses and
   conclusions. Inspect desktop and relevant narrow
   layouts, including hidden answers. Flag any display requiring horizontal
   scrolling at the normal desktop content width. Split an overflowing row of
   independent claims into separate displays; keep each equation, implication,
   or equivalence horizontal when it fits, and break a genuinely long single statement only at meaningful
   mathematical boundaries. For a line-break audit, enumerate every explicit
   break and keep short formulas and identity lists compact. Formula scrolling
   on mobile is acceptable and does not justify extra line breaks.
4. Check reading order and the entry's references. In an area batch, check the
   assigned placement and include global conflicts in your findings; do not replan
   the area during this review.
   Review the relevant applied integration changes from step 2, identified by root
   in an area batch, and report missing, stale, or incorrect links/planning items.
   Do not treat proposed edits as applied or reviewed. Do not repeat a corpus-wide
   consumer search or unrelated planning cleanup. Retrieve only planning records associated with the reviewed entries
   and source records for publications actually investigated, using the
   [registry lookups](../docs/corpus.md#navigating-source-and-planning-records).
   Return proposed corrections; do not edit reference planning.

## Checks

The independent reading and rendering review above is this step's check. Use
`build --no-lean --check` only to investigate a concrete structural/reference
concern. Source-record edits follow the [shared build rules](../CONTRIBUTING.md#validation-and-submission)
for catalog regeneration. In an area batch, if you are a delegated reviewer, send
shared-record changes to root unless exclusive file ownership was assigned, and
leave publication to root. If you are root, apply those changes and refresh the
catalogs at a coordinated checkpoint or the final build.
No routine writing build, catalog tests, Lean proof checks, or formal-binding
audit is required.

## Deliverable

Return prioritized findings with block/file references, consequences, and concrete
corrections; separate errors from optional improvements. State reviewed scope,
unavailable checks, and revisions needed before formal preparation. Include
relevant integration findings and source-register changes when applicable.
Do not rewrite entries, metadata, mappings, or proofs, or set approval fields.
The area entry driver applies corrections through step 2 and requests focused
step-3 rereview from root before continuing; root assigns it. Do not perform those
edits yourself.
