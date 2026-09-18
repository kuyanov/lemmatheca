# Mathematical corpus

The near-term goal is connected standard mathematics in a few areas, drafted from
books and the pinned mathlib library, alongside measured AI-formalization trials.
The corpus is edited as repository files; there is no ingestion pipeline, public
submission service, or release API. See the
[experiment and corpus plan](../docs/formalization-experiments.md).

Three draft entries:

- [Sumsets and translations](entries/thm-sumset-lower-bound/entry.html), with
  [metadata](entries/thm-sumset-lower-bound/entry.json), an SVG illustration,
  a table, and a labelled equation with a clickable reference.
- [Adding three sets](entries/thm-triple-sumset-lower-bound/entry.html), with
  [metadata](entries/thm-triple-sumset-lower-bound/entry.json), citing results
  in the first entry, plus a sharper integer bound with a human proof and two
  Lean helper statements with unfinished (`sorry`) proofs.
- [Finding a monotone subsequence](entries/thm-erdos-szekeres/entry.html), with
  [metadata](entries/thm-erdos-szekeres/entry.json), an exposition of Seidenberg's
  [one-page Erdős–Szekeres proof](https://doi.org/10.1112/jlms/s1-34.3.352).
  It is under **Combinatorics → Extremal combinatorics**. All four blocks are
  `not_started`, without Lean sources or mathlib bindings, for a later
  formalization-cost experiment.

Each folder owns its HTML, JSON, and assets. [Taxonomy](taxonomy.json) describes
subjects; [reading order](reading-order.json) controls listings and “Next entry”.
The compact JSON has no version fields or separate proof records. Unproved Lean
statements are listed per block as `unformalized_dependencies`, each with a
`declaration`, `module`, and `source`. The website links both pending dependencies
and completed formalizations to the general Lean file viewer.
A nonempty list prevents `complete` status; existing,
checked mathlib lemmas are not pending dependencies. The `based_on` bibliography
appears as **Based on:** with authors, linked title, and year. Only the first source
is initially visible; additional sources expand on demand. Full publication
details remain in JSON. An empty list, as in the original sumset examples, omits that row.
The website also displays a formalization badge derived from the block statuses.

**Sumsets and translations** has six complete formal bindings, including existing
mathlib declarations. **Adding three sets** has four complete blocks and one
partial block, so its entry badge is partial. All three remain editorial drafts awaiting
maintainer review. See the [authoring guide](../docs/entry-sources.md).

## Growing the collection

Choose a book section and related mathlib modules, match their hypotheses and
definitions, then group the material into a readable note. Bind existing checked
mathlib declarations directly; reserve new Lean proofs for missing mathematics or
experiments on translating a particular argument. A correct binding alone does
not establish that the human proof's strategy has been formalized.

Use original exposition and precise `based_on` citations. Generate only the human
content sections; the shared templates already provide page layout and navigation.
Human editing should improve explanation, mathematical correspondence, and figures.
Preserve stable block IDs and update the primary area's reading order when adding
an entry. Additional areas are metadata only in the current reader.

Keep prompts, attempts, cost measurements, and human review time in experiment
records outside `entry.json`. No run-record system is implemented yet. The
Erdős–Szekeres entry remains unformalized until a measured attempt is launched.

## Validation

```sh
uv run python app/manage.py check_formalizations
uv run python app/manage.py validate_corpus
uv run python app/manage.py test catalog
```
