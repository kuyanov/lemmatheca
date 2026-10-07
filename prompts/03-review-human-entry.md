# Step 3: Review the human entry

Follow the [single-step execution instructions](../CONTRIBUTING.md#running-one-step-with-an-ai-agent).
Complete this step using the supplied inputs and current repository files;
return its deliverable without starting the next stage.

Independently review the human mathematics and presentation of a Lemmatheca entry.

## Inputs

- Entry ID (required): the existing entry to review.
- Review focus or source material (optional): otherwise review the full entry.

## Context

Read the [project overview](../README.md), [corpus guide](../docs/corpus.md),
[app guide](../docs/app.md), and the complete entry, including
metadata, linked prerequisites, figures, proofs, and hidden answers. Consult cited
passages as needed to check attribution or resolve ambiguities.
Judge the current files on their merits rather than relying on a prior summary.
Consult [Source errors](../corpus/source-errors.md) when checking cited arguments.

## Work

Check the following:

- Source checks distinguish serious mathematical defects from lack of explanation.
  Prioritize false statements, missing necessary hypotheses, invalid constructions,
  and failed deductions; valid compression is not an error. Save confirmed source
  defects and checked repairs in [Source errors](../corpus/source-errors.md), and
  update the actual reviewed scope and access limits using the
  [maintenance contract](../docs/corpus.md#source-errors). Check whether affected
  entry blocks already contain a repair. This register is the review's only
  permitted file edit; entry corrections remain in the drafting handoff.

- Claims have the correct hypotheses, quantifiers, domains, codomains, and
  conclusions. Test relevant empty, singleton, boundary, finite, and infinite
  cases. Check both directions of equivalences and the witnesses in examples.
- Proofs establish the stated conclusions without circular reasoning and explain
  the important steps at the intended reader's level. Questions have correct
  answers. Figures and tables agree with the mathematics.
- Accent green blocks (`class="statement-box"`) highlight only the entry's main
  results, with their hypotheses and conclusions included. Check their role in the
  entry rather than their theorem or lemma label. Flag boxes around definitions,
  supporting lemmas, routine facts, examples, questions, proof steps, or proofs,
  and main results whose emphasis is lost among secondary boxes.
- Figures match the website's current typography, muted green palette, and panel
  and caption styling, as defined in `app/static/css/site.css` and nearby figures.
  Check the `proof-figure` and `figure-image` wrappers, readable labels and legends,
  and spacing without overlap or clipping. Always inspect the desktop reader at
  normal zoom: fonts should be proportionate to the surrounding text, with clear
  separation between labels, legends, and bottom notes. Flag oversized fonts or
  cramped spacing even when the figure fits its panel. Also check relevant narrow
  layouts.
- Definitions and notation are consistent, prerequisites are introduced or linked,
  and citations accurately support the material.
  Familiar background, including standard real-number facts, may be used without
  an entry reference. Distinguish useful future links from mathematical gaps and
  major dependencies on substantial missing theory.
  Check that linked results supply the needed content with compatible assumptions,
  including across areas. Flag missing substantial prerequisite theories and
  recommend concrete entry titles, following the
  [scope guidance](../CONTRIBUTING.md#prerequisites-and-scope). Check claims about
  axiom strength separately from ordinary implications and set-closure properties.
  Review these arguments under their stated axioms; Verified badges do not
  establish axiom strength.
- **Audit the [upcoming-reference table](../corpus/reference-planning.md#upcoming-references) for every reviewed
  entry.** Inspect all of its blocks for useful references to future areas,
  including accepted background and facts proved locally. Check that applicable
  rows exist, use actual consuming block IDs, and state the precise fact and
  proposed future-area coverage. Flag omitted uses, stale locations, and rows
  whose suitable targets are now available.
  Require **Upcoming references** to contain one four-column table of future-area
  references. Existing-target integration notes, future-entry plans, correspondences
  still to prove, and deferred extensions belong in the corresponding separate
  planning sections of the same
  [Reference backlog and planning](../corpus/reference-planning.md) document.
  Return concrete proposed additions or replacements using the table's four
  columns, and identify fulfilled locations to remove together with the exact
  available target blocks to link. If no changes are needed, say so explicitly
  after checking the entry. Do not edit the reference document during this read-only
  review; identify omitted or incorrect rows and misplaced planning notes as
  drafting corrections in the handoff, naming the appropriate table or section.
- Exposition and metadata remain valid if entries are reordered or moved into
  separate subareas. Flag references to "the next entry," "previous entries," or
  material "introduced earlier" in another entry. Require named links using stable
  entry and block IDs, without assumptions of adjacency, a shared area, or area
  paths in links. Check that necessary conventions are stated locally. Distinguish
  these issues from references to mathematical order or steps within a proof.
- Prose avoids filler, repeated definitions and conclusions, and unnecessary
  meta-commentary while retaining essential hypotheses and logical transitions.
- The abstract stands on its own for readers new to the topic or who have not read
  the entry. It uses simple language, explains essential unfamiliar terms, and
  emphasizes the main results and their meaning rather than proof techniques or
  a section itinerary. Its claims match the entry and retain necessary conditions.
  Check that it develops a connected idea: each sentence builds on the preceding
  context, and the selected results belong to that thread. Flag isolated facts or
  transitions that suggest a relationship the mathematics does not support.
- HTML, metadata, references, assets, and `corpus/area_entries.json` follow the
  current contract. Inspect the rendered page, including hidden answers and narrow
  layouts where relevant. Unplanned formal mappings are allowed at this stage.
- The entry-list summary is generated data from the build, not an editorial
  approval. Flag missing or inconsistent generated data without fabricating it.

## Checks

Review the current mathematics and rendered presentation. Inspect cited passages
where needed to check attribution or resolve an ambiguity in the entry.
Run `uv run python app/manage.py validate_corpus` only when investigating a
structural or reference concern. No build or catalog test run is required for
an ordinary read-only review.

## Deliverable

Return findings ordered by importance, with file/line or block references, why each
issue matters, and a concrete correction. Separate mathematical errors from optional
editorial improvements. State what was checked and any unavailable source or visual
checks. Include a concise list of revisions needed before formalization.
For each entry, include the upcoming-reference audit outcome with concrete proposed
table rows and removals, or an explicit finding that no changes are needed. Do not
substitute a generic statement that references were checked for this outcome.

This is a read-only review. Do not rewrite the entry or generated JSON, create
formal nodes, or run the writing build command. Reviews and decisions belong in
the GitHub pull request; return the findings here unless posting a review was
explicitly requested. There
is no app approval or draft/final flag to set.
Source-error register maintenance is the sole exception to read-only file work.
Report saved defect IDs and coverage changes, or explicitly state that the
register already covers the inspected source material and needs no changes.
