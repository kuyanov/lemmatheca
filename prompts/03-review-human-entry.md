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

## Work

Check the following:

- Claims have the correct hypotheses, quantifiers, domains, codomains, and
  conclusions. Test relevant empty, singleton, boundary, finite, and infinite
  cases. Check both directions of equivalences and the witnesses in examples.
- Proofs establish the stated conclusions without circular reasoning and explain
  the important steps at the intended reader's level. Questions have correct
  answers. Figures and tables agree with the mathematics.
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

This is a read-only review. Do not rewrite the entry or generated JSON, create
formal nodes, or run the writing build command. Reviews and decisions belong in
the GitHub pull request; return the findings here unless posting a review was
explicitly requested. There
is no app approval or draft/final flag to set.
