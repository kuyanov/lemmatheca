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

Before writing the draft, inspect the step-1 source-rigor assessment against the
passages needed for this entry. If it is missing or the scope or sources changed,
check those passages for mathematical rigor yourself. Check hypotheses, logical
steps, examples, and nontrivial omissions or cited dependencies. Report identified
errors, gaps, and unchecked arguments in the task discussion **before drafting**,
with precise source locations, affected claims, consequences, and proposed repairs.
An existing applicable report need not be repeated. Establish a checked repair or
supporting argument before using an affected claim; do not silently fill a gap or
write an unsupported argument as proved. If a necessary claim remains unsupported,
report the affected drafting work as blocked and continue independent work where
possible. This assessment does not require an approval flag or automatic permission
request.

1. Read the relevant source passages and write original, precise mathematics.
   State domains, codomains, hypotheses, quantifiers, and conventions where they
   matter. Include useful examples, counterexamples, edge cases, and answers to
   questions. Distinguish definitions, claims, explanations, and proofs.
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
   Use collapsible question answers. Figures and tables need stable IDs and captions
   without hard-coded numbers; images need useful alternative text. Keep Lean names
   and build-process details out of the exposition.
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
   [corpus guide](../docs/corpus.md). Choose a primary area and list the ID once, in reading order,
   under that area in `corpus/area_entries.json`. There are no review or editorial
   status fields to add.
   Write the abstract for readers new to the topic or who have not read the entry.
   Use simple language, explain essential unfamiliar terms, and emphasize the main
   results and what they mean. Make it understandable on its own; avoid a section
   itinerary, proof techniques, and notation that requires the entry's definitions.
   Keep necessary conditions, expressing them in plain language where possible.
   Develop one connected paragraph around the entry's central idea. Let each
   sentence build on the previous one, linking the motivating idea to the main
   conclusions. Choose results that support this thread rather than listing every
   topic; transitions should express a real relationship between ideas.
5. Leave data-formal absent for new blocks. An empty mapping means nothing needs
   formalizing, not that work is unfinished. Preserve existing mappings on an
   edited entry unless the changed mathematics requires revisiting them. Do not
   create new Lean declarations or node records in this drafting step.

## Checks

Run from the repository root:

```sh
uv run python app/manage.py validate_corpus
uv run python app/manage.py build
uv run python app/manage.py test catalog
```

Validation can also run during authoring without Lean or generated results.
The build uses the existing Lean project and generates `entry.json`'s `formalization`
summary; do not calculate or edit it by hand. Keep generated JSON changes with the
source edits. A failed build preserves previous results, so it is not a successful
refresh. Report a blocker in unrelated work without altering that work to bypass it.

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
