# Step 2: Draft the human entry

Own the human exposition, entry metadata, assets and reference integration.
Follow the [shared execution rules](../CONTRIBUTING.md#running-one-step-with-an-ai-agent)
and the [area-pipeline protocol](../CONTRIBUTING.md#running-an-area-pipeline) for
ownership, review requests and publication.

## Inputs

- Entry ID, agreed scope, perspective and source plan, or an existing entry to revise.
- Optional human-review findings and reading-time target.
- For an area batch, assigned prerequisites, placement and file ownership.

## Context

Use the step-1 handoff and the [corpus contract](../docs/corpus.md), particularly
[metadata and abstracts](../docs/corpus.md#entry-metadata),
[HTML, proof labels and main-result boxes](../docs/corpus.md#html-and-references),
[display layout](../docs/corpus.md#mathematics-figures-and-assets), and
[exposition depth](../docs/corpus.md#exposition-and-formalization).
Recover only missing drafting inputs; do not repeat area planning or an applicable
source assessment.

Use the [authoring API](../CONTRIBUTING.md#using-the-authoring-api) for prerequisite
and consumer context. Select known blocks with `block_ids` and
`include=blocks,references`. For links alone, query the precise entry/block `target`
and needed reference `direction`. When coverage changes, search blocks with
concept-specific `q` and `include_answers=true` for unlinked consumers across
areas; backlinks alone cannot find them. Select affected planning records by
entry, area or kind using the
[registry workflow](../docs/corpus.md#navigating-source-and-planning-records).

## Work

1. Write original definitions, statements, proofs, examples and question answers
   within the agreed scope and perspective. Preserve hypotheses and reasoning;
   introduce notation before use. Apply human-review corrections. Inspect new
   source passages only when the supplied assessment does not cover them. Report
   scope, prerequisite or entry-splitting needs rather than independently
   replanning the area or compressing the arguments.
   Consider figures that help the reader follow an example, construction or
   proof. Whenever a source includes figures, take that as a cue to consider an
   illustration in the entry as well. Choose figures for their explanatory value
   and follow the [figure and asset contract](../docs/corpus.md#mathematics-figures-and-assets)
   for original artwork, reuse and credit.
2. Save `entry.html`, [authored `entry.json` fields](../docs/corpus.md#entry-metadata)
   and necessary assets. Progress counts and Lean line counts are build outputs in
   the index; do not add them or placeholder summaries to entry metadata.
   Make the abstract understandable before reading the entry and reserve accent green statement boxes for main results.
   Use stable links independent of adjacency or area membership. For a standalone
   new entry, save its agreed placement once in `corpus/reading_order.json`; in an
   area batch, root applies placement and other shared-file edits.
3. For new or changed mathematical coverage, perform
   [reference integration](../CONTRIBUTING.md#reference-integration): add useful
   outgoing links, discover existing consumers, and add their links to the new
   coverage. Check exact target statements and assumptions. Remove or narrow
   fulfilled planning tasks, retaining only outstanding facts and locations.
   Send concrete shared-file edits to root under the ownership rules. A wording
   or layout change checks affected links only.
4. Leave `data-formal` absent on new blocks. Preserve existing mappings unless
   their mathematics changes, and identify affected mappings for step 4. Do not
   create nodes or Lean declarations or use empty mappings to hide unfinished work.

## Checks

Inspect changed rendered pages and hidden answers at normal desktop size and
relevant narrow widths under the display-layout contract. Check the draft's
metadata, links and assets. For each changed figure, also inspect an intrinsic-size
render: edges and arrow tips must meet their intended vertices, comparable labels
must align, and text must remain clear of the drawing and other text. Check actual
glyph bounds and marker geometry, rather than relying on approximate coordinates.
This self-check does not replace step 3's independent review.

Finish mutating work under the
[shared build rules](../CONTRIBUTING.md#validation-and-submission): standalone
corpus edits require a writing build even for prose-only changes; an area batch
leaves checkpoints and final publication to root.

## Deliverable

Return the draft files, applied integration changes, concrete shared edits still
needed, checks, and material departures or unresolved questions. Request step-3
review under the area protocol. Do not treat proposed integration changes as
already applied or reviewed.
