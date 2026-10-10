# Step 2: Draft the human entry

Follow the [single-step execution instructions](../CONTRIBUTING.md#running-one-step-with-an-ai-agent).
Complete this step using the supplied inputs and current repository files;
return its deliverable without starting the next stage.

Create the human-readable Lemmatheca entry before formalization.

## Inputs

- Entry ID and scope (required): use the task's requested topic and audience.
- Selected sources and outline: use the supplied step-1 report or recover them
  from the referenced planning material or existing entry. Identify any essential
  source material that is unavailable rather than inventing it.
- Reading-time target (optional): estimate from the finished content if omitted.
- Review findings (optional): apply relevant findings when revising an entry.

## Context

Read the [project overview](../README.md), [corpus guide](../docs/corpus.md),
[app guide](../docs/app.md), and [contribution workflow](../CONTRIBUTING.md).
Inspect nearby entries, `corpus/taxonomy.json`, and `corpus/area_entries.json`.
Preserve unrelated work and existing stable IDs when revising an entry.

## Work

Check the [prerequisites and scope](../CONTRIBUTING.md#prerequisites-and-scope)
against the current entries before drafting. Link available results by stable IDs
and check that their assumptions fit the proposed use. Develop short supporting
lemmas locally when they fit the topic. If a substantial theory from another area
is missing, report the affected claims, recommend that area's first entry titles,
and draft an independent useful scope within the task's authorization. Make any
scope reduction explicit; do not silently omit a requested central result or
create entries in other areas. Distinguish human prerequisite coverage from
availability of Lean declarations and from formal verification.

Apply the [reading-order criteria](../CONTRIBUTING.md#reading-order) to entry
placement, the sequence of blocks, and the summary and abstract. Check that each
definition is introduced before its first use or reference.

**Upcoming-reference table maintenance is required for every draft and revision in this
step.** Read [Reference backlog and planning](../corpus/reference-planning.md), then inspect
every block of each drafted or revised entry for useful references to future areas. Include
accepted background and locally developed facts whose broader treatment would
help readers; do not limit the audit to missing prerequisites.

- Add or update rows in the single table under
  [Upcoming references](../corpus/reference-planning.md#upcoming-references) using its four columns:
  future area, proposed reference coverage, consuming `entry-id#block-id`
  locations, and the precise fact or context to reference. Group repeated uses.
  Use the actual current block IDs and proposed titles rather than nonexistent
  target links or invented future block IDs.
- When a suitable target already exists, inspect its content and assumptions,
  add the useful entry link now, and remove the fulfilled consuming locations
  from the upcoming-reference table. Keep any locations still awaiting future coverage.
- Keep **Upcoming references** to this one four-column table. Put other planning
  material in the same document's separate sections for
  [existing-target integration notes](../corpus/reference-planning.md#existing-target-integration-notes),
  [cross-area correspondences still to establish](../corpus/reference-planning.md#cross-area-correspondence-to-establish),
  [future-entry plans](../corpus/reference-planning.md#references-available-for-the-planned-expansion),
  and [deferred extensions](../corpus/reference-planning.md#boundaries-of-the-set-theory-expansion).
  Do not add audit narratives, extra tables, or maintenance rules to **Upcoming references**.
- Complete the table edits before returning the draft. Listing proposed rows
  only in the response does not complete this drafting task. Report the actual
  additions, changes, and removals, or explicitly state that the audit found
  no changes needed.

Familiar background, including standard real-number facts, may be used without
an entry reference and does not block drafting merely because a link is unavailable.
The upcoming-reference table does not permit major dependencies on substantial theory missing from
the corpus or excuse incorrect or unsupported reasoning.

Before writing the draft, check the needed source passages for mathematical rigor.
Use a supplied step-1 source-rigor assessment where it applies; if it is missing
or the scope or sources changed, check the passages yourself. Check hypotheses,
logical steps, examples, and nontrivial omissions or cited dependencies. Report
identified errors, gaps, and unchecked arguments in the task discussion **before drafting**,
with precise source locations, affected claims, consequences, and proposed repairs.
An existing applicable report need not be repeated. Establish a checked repair or
supporting argument before using an affected claim; do not silently fill a gap or
write an unsupported argument as proved. If a necessary claim remains unsupported,
report the affected drafting work as blocked and continue independent work where
possible. This assessment does not require an approval flag or automatic permission
request.

**Source-error register maintenance is required for every draft and revision.**
Consult [Source errors](../corpus/source-errors.md) before reusing cited arguments.
Follow the [source-error contract](../docs/corpus.md#source-errors): prioritize
false statements, missing necessary hypotheses, invalid constructions, and failed
deductions. Valid compression and missing explanation are not confirmed errors.
Save new confirmed defects, checked repairs, and consuming block links; update
reviewed coverage for all inspected citations, including no-defect outcomes and
access limits. Distinguish a repaired corpus entry from a corrected upstream source.
Complete these edits before returning the draft; a chat-only list is insufficient.

1. Read the relevant source passages and write original, precise mathematics.
   State domains, codomains, hypotheses, quantifiers, and conventions where they
   matter. Include useful examples, counterexamples, edge cases, and answers to
   questions. Distinguish definitions, claims, explanations, and proofs.
   State the background axioms when their strength matters and check that reused
   arguments respect them. Distinguish definitions, explicit premises, and
   assertions of a principle. Proving an implication does not establish strict
   weakness or independence. Follow the
   [assumption guidance](../CONTRIBUTING.md#prerequisites-and-scope).
   Defer model-theoretic or topological applications when their
   substantial prerequisites are missing, naming the needed entries in the handoff.
2. Use concise prose without filler, repeated conclusions, or unnecessary narration.
   Introduce notation once and link existing prerequisites. Preserve the hypotheses
   and reasoning when shortening. Match existing terminology, including "fiber" and
   "fibers". Treat the reading-time target as a guide, not a reason to omit necessary
   explanations or add padding. Estimate reading_time from the finished content.
3. Organize coherent mathematical sections using the HTML contract in [corpus guide](../docs/corpus.md).
   Use stable block IDs, supported data-kind values, and one direct h2 per block.
   Let the reader generate numbering, navigation, and equation/figure/table labels.
   Use `#block-id` for local references and `entry-id#block-id` across entries. Prefer
   empty local links for generated numbering and meaningful cross-entry link text.
   Entries may be reordered or moved into separate subareas. Keep exposition and
   metadata independent of reading-order position and area membership: name and
   link prerequisites or related topics by stable entry and block IDs. Do not use
   "the next entry," "the previous entries," or cross-entry claims that something
   was "introduced earlier." State the conventions needed by this entry locally.
   Cross-entry links must work across areas; do not embed area paths in them.
   References to mathematical order or steps within the current proof are fine.
   Use collapsible question answers. Figures and tables need stable IDs and captions
   without hard-coded numbers; images need useful alternative text. Keep Lean names
   and build-process details out of the exposition.
   Reserve accent green blocks (`class="statement-box"`) for the entry's main
   results. Select the central conclusions of the entry rather than boxing every
   theorem or lemma. Include the result's hypotheses and conclusion inside the box;
   keep definitions, supporting lemmas, routine facts, examples, questions, proof
   steps, and proofs outside it.
   Match figures to the website's existing visual style. Inspect
   `app/static/css/site.css` and nearby entry figures: use serif mathematical labels,
   muted green accents, thin lines, subdued fills, and clear spacing. Prefer SVG for
   mathematical diagrams. Use `class="proof-figure"` on the figure, wrap its image
   in `class="figure-image"`, and keep the caption directly inside the figure so
   the reader applies its standard panel and caption styling. Give images intrinsic
   width and height, and make labels and legends readable at the displayed size.
   Always check typography and spacing in the desktop reader at normal zoom.
   Keep figure fonts proportionate to the surrounding text, avoiding oversized
   labels. Leave clear space between labels, legends, and bottom notes. Adjust
   the figure height when needed to provide that space.
4. Write `corpus/entries/<entry-id>/entry.html` and entry.json, plus necessary assets.
   Use the author-maintained metadata fields and inspected `based_on` citations from
   [corpus guide](../docs/corpus.md). The entry's `title` must be plain text, with no
   LaTeX commands or math delimiters. Describe mathematical notation in words in
   the title; put formulas in the entry body.
   Choose a primary area and list the ID once, in reading order,
   under that area in `corpus/area_entries.json`. There are no review or editorial
   status fields to add.
   Write the abstract for readers new to the topic or who have not read the entry.
   Consult the cited sources' explanations and motivating examples to find a
   natural starting point, then check it against the entry's scope and assumptions.
   Write original prose beginning with a concrete problem, example, or familiar
   fact that gives readers a reason to follow the rigorous arguments. Use simple
   language and familiar mathematical vocabulary, briefly explaining essential new
   terms; avoid vague substitutes for standard terms and notation that requires the
   entry's definitions. Develop one connected paragraph around the central idea,
   with each sentence building on the previous one. Select a few main results,
   preserve their necessary conditions, and explain their significance and real
   relationships. Avoid proof-technique inventories and section itineraries. Read
   the finished paragraph as an introduction and check that its objects, comparisons,
   and conclusions make sense without the entry.
5. Leave data-formal absent for new blocks. An empty mapping means nothing needs
   formalizing, not that work is unfinished. Preserve existing mappings on an
   edited entry unless the changed mathematics requires revisiting them. Do not
   create new Lean declarations or node records in this drafting step.

## Checks

Confirm that the future-reference audit covered every drafted or revised entry,
that its table changes are saved, and that all consuming block IDs exist. Check
that **Upcoming references** still contains one four-column table of future-area
references only and that other planning notes remain in the document's separate sections.

After editing corpus files, run from the repository root:

```sh
uv run python app/manage.py validate_corpus
```

When adding an entry or changing its block inventory or formal mappings, refresh
the generated `formalization` summary with
`uv run python app/manage.py build`. Keep generated JSON changes with the source
edits; do not calculate summaries by hand. A failed build preserves previous
results, so report the failed refresh and any unrelated blocker.
Run relevant catalog tests only when reader or build-tooling code changes, or
when investigating a rendering or integration failure.

Inspect the rendered entry, including equations, references, hidden answers, tables,
and figures. Always verify font sizes and spacing in the desktop layout, then
check relevant narrow layouts. Check that figure panels and captions match the
site, labels do not overlap or clip, notes have enough separation from nearby
labels, and diagrams fit the reading column.
Restart the development server if adding a new assets directory.

## Deliverable

Return the changed files, the checks performed, and unresolved mathematical or source
questions for GitHub review. Describe any visual checks that could not be completed.
Include the source-rigor findings reported before drafting, their resolutions, and
any remaining gaps or unchecked material. Separate repairs to source arguments
from editorial changes to the entry.
Include the saved source-error IDs and coverage changes, or an explicit finding
that the register already covers the inspected material and needs no changes.
Include prerequisite links, supporting lemmas developed locally, explicit scope
changes, and recommendations for missing areas or entries.
For each entry, include the upcoming-reference audit outcome: rows added, changed,
or removed, or an explicit finding that no changes were needed after inspecting
its blocks. Keep deferred material and future-entry plans separate from these rows
in the corresponding sections of the same reference document.
