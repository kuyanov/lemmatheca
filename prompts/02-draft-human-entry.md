# Step 2: Draft the human entry

Follow the [shared execution rules](../CONTRIBUTING.md#running-one-step-with-an-ai-agent).
Own the human exposition and its integration into the corpus.

In the [area pipeline](../CONTRIBUTING.md#running-an-area-pipeline), you are the
entry owner. Follow your assigned plan through steps 2–6 without asking the user
between stages. Request reviews from root; root alone assigns or spawns reviewers
and owns global scope, coverage gaps and reading order.

## Inputs

- Entry ID and scope.
- Source plan and outline, or the existing entry for a revision.
- Optional human-review findings and reading-time target.
- For an area batch, root's assigned prerequisites, placement and file ownership.

## Context

Use the applicable step-1 handoff and the [corpus contract](../docs/corpus.md),
including metadata, abstracts, HTML, main-result boxes, and formula/figure layout.
Use its shared italic proof-label markup for every proof.
Inspect the affected entries and reading-order index. Recover missing inputs using
only the targeted checks in the shared execution rules; do not repeat an applicable
source audit or the full planning stage.

Use the [authoring API](../docs/app.md#authoring-api) under the
[shared usage rules](../CONTRIBUTING.md#using-the-authoring-api) for entry context,
area listings and existing incoming/outgoing references. For known prerequisite
or consumer blocks, use `block_ids` and `include=blocks,references`. If references
alone are needed, query the precise entry or block `target` with the needed
`direction=incoming`, `outgoing`, or `both`. Reuse links already in retrieved
context. Search blocks with concept-specific `q` and `include_answers=true` for
unlinked consumers when coverage changes; backlinks alone cannot find them, and
relevant consumers may lie outside the entry's area.
Save drafting and integration edits to owned corpus files. In an area batch,
send concrete edits for shared registries and existing consumer entries to root
unless it has assigned exclusive ownership of those files.
Request a root index checkpoint before dependent API work when needed; use current
corpus files until root announces the refreshed revision. Do not rebuild it yourself.

## Work

1. Write original definitions, statements, proofs, examples, and question answers
   within the agreed scope. Apply relevant review findings. Preserve necessary
   hypotheses, conventions, and reasoning; introduce notation before use. Check
   new source passages only when the supplied assessment does not cover them.
   Explain the substantive mathematics needed by the formalization under the
   [exposition and formalization rule](../docs/corpus.md#exposition-and-formalization).
   Report a needed split to root in an area batch rather than compressing the
   argument to preserve the planned entry count.
2. Save `corpus/entries/<id>/entry.html`, author-maintained `entry.json` fields,
   and necessary assets. Apply the metadata and presentation contracts rather
   than copying implementation details into the exposition. Use stable IDs and
   links independent of adjacency or area membership. Root saves placement in
   `corpus/area_entries.json` for an area batch; report any prerequisite conflict
   rather than reordering or expanding global scope. For a standalone task,
   place a new entry once, with prerequisites before their uses.
3. For new or changed mathematical coverage, own the
   [reference integration](../CONTRIBUTING.md#reference-integration): check useful
   outgoing and incoming links, update the `upcoming-reference` collection, and
   remove or narrow the related fulfilled tasks in reference planning. Inspect
   exact target statements and assumptions. A local wording or layout revision
   checks affected links only; it does not trigger another corpus-wide search.
   Select planning records by entry ID, area, or kind through the
   [registry lookup workflow](../docs/corpus.md#navigating-source-and-planning-records).
   Edit only affected records under the ownership rule above; supply root with
   exact target blocks and proposed shared-file changes in an area batch.
4. Leave `data-formal` absent on new blocks. Preserve existing mappings unless
   the mathematics changes; identify affected mappings for step 4. Do not create
   nodes or Lean declarations, and do not use an empty mapping to hide unfinished
   formalization.

## Checks

- For a standalone task, finish corpus edits with the writing `build --no-lean`
  and commit changed generated JSON, including `corpus/index.json`. This applies
  even to prose-only or whitespace-only edits; `build --no-lean --check` does not
  refresh the index. Follow the
  [change-based checks](../CONTRIBUTING.md#validation-and-submission):
  statistics-only updates are exempt. For an ongoing multi-stage batch, defer
  the writing build to its final mutating stage and carry that requirement in
  the handoff; a required full `build` satisfies it without a separate no-Lean build.
  In an area batch, root alone runs coordinated index checkpoints and the final
  full build under the area protocol; do not run a writing build locally.
- Inspect the affected rendered pages, including hidden answers and any changed
  formulas or figures, at normal desktop size and relevant narrow widths. Apply
  the [display-layout contract](../docs/corpus.md#mathematics-figures-and-assets);
  display formulas must fit the normal desktop content width without horizontal
  scrolling. Separate independent claims when their combined row would overflow.
  Keep each equation,
  implication, or equivalence horizontal when it fits; break a genuinely long
  single statement only at meaningful mathematical boundaries. Horizontal formula
  scrolling on mobile is acceptable and does not justify extra line breaks.
- A later independent mathematical and presentation audit belongs to step 3.

## Deliverable

Return changed files, material departures from the plan, relevant integration
changes actually saved, checks performed and unavailable checks, and questions
for human review. Include source-register changes only if new inspection required
maintenance. Include refreshed generated data, or identify the pending root build
and concrete shared-file edits. This stage ends at the draft. In an area batch,
request step-3 review from root with those edits. Root applies the shared
integration, identifies the stable files/blocks, completes any needed index
checkpoint, then assigns the reviewer. Apply corrections through step 2 and
request focused rereview; root assigns it before you continue the sequence.
