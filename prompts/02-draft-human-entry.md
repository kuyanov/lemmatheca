# Step 2: Draft the human entry

Follow the [shared execution rules](../CONTRIBUTING.md#running-one-step-with-an-ai-agent).
Own the human exposition and its integration into the corpus.

## Inputs

- Entry ID and scope.
- Source plan and outline, or the existing entry for a revision.
- Optional human-review findings and reading-time target.

## Context

Use the applicable step-1 handoff and the [corpus contract](../docs/corpus.md),
including metadata, abstracts, HTML, main-result boxes, and formula/figure layout.
Inspect the affected entries and reading-order index. Recover missing inputs using
only the targeted checks in the shared execution rules; do not repeat an applicable
source audit or the full planning stage.

## Work

1. Write original definitions, statements, proofs, examples, and question answers
   within the agreed scope. Apply relevant review findings. Preserve necessary
   hypotheses, conventions, and reasoning; introduce notation before use. Check
   new source passages only when the supplied assessment does not cover them.
2. Save `corpus/entries/<id>/entry.html`, author-maintained `entry.json` fields,
   and necessary assets. Apply the metadata and presentation contracts rather
   than copying implementation details into the exposition. Use stable IDs and
   links independent of adjacency or area membership. Place a new entry once in
   `corpus/area_entries.json`, with prerequisites before their uses.
3. For new or changed mathematical coverage, own the
   [reference integration](../CONTRIBUTING.md#reference-integration): check useful
   outgoing and incoming links, update the single upcoming-reference table, and
   remove or narrow the related fulfilled tasks in reference planning. Inspect
   exact target statements and assumptions. A local wording or layout revision
   checks affected links only; it does not trigger another corpus-wide search.
4. Leave `data-formal` absent on new blocks. Preserve existing mappings unless
   the mathematics changes; identify affected mappings for step 4. Do not create
   nodes or Lean declarations, and do not use an empty mapping to hide unfinished
   formalization.

## Checks

- Run corpus validation once after the drafting batch, using the
  [change-based checks](../CONTRIBUTING.md#validation-and-submission).
- Inspect the affected rendered pages, including hidden answers and any changed
  formulas or figures, at normal desktop size and relevant narrow widths. Apply
  the [display-layout contract](../docs/corpus.md#mathematics-figures-and-assets);
  horizontal formula scrolling on mobile is acceptable.
- Refresh generated summaries only when required by the shared check matrix.
  A later independent mathematical and presentation audit belongs to step 3.

## Deliverable

Return changed files, material departures from the plan, relevant integration
changes actually saved, checks performed and unavailable checks, and questions
for human review. Include source-register changes only if new inspection required
maintenance. Do not perform formal preparation or the independent review here.
