# Mathematical corpus

The near-term goal is connected standard mathematics in a few areas, drafted from
books and the pinned mathlib library, alongside measured AI-formalization trials.
The corpus is edited as repository files; there is no ingestion pipeline, public
submission service, or release API. See the
[experiment and corpus plan](../docs/formalization-experiments.md).

The active draft is [Sets and maps: a first guide](entries/sets-and-maps/entry.html),
with [metadata](entries/sets-and-maps/entry.json), under **Logic and foundations →
Set theory**. Based on chapters 2–4 of Tim Button's Open Logic textbook, it covers
sets, maps, notation, short proofs, a numbered map diagram, and four questions
with collapsible answers. Estimated reading time: 40 minutes. All 21 blocks are
`not_started`; formalization is reserved for a measured pass.

The earlier examples are archived outside the live entry tree:

- [Sumsets and translations](backup/thm-sumset-lower-bound/entry.html): six complete bindings.
- [Adding three sets](backup/thm-triple-sumset-lower-bound/entry.html): four complete blocks
  and a partial integer bound with two pending Lean helper proofs.
- [Finding a monotone subsequence](backup/thm-erdos-szekeres/entry.html): four unformalized
  blocks based on Seidenberg's proof, reserved for a future measured experiment.

`backup/` is excluded from listings, entry routes, static asset collection, corpus
validation, and formalization checks. Tests load temporary copies of these examples
to exercise features such as cross-entry links and complete/partial badges.
[Taxonomy](taxonomy.json) contains only the working areas;
[taxonomy_complete.json](taxonomy_complete.json) keeps the broader taxonomy for reference.
To restore an archived entry, move it into `entries/`, restore its subjects to the
active taxonomy, and add its ID to the primary area's reading order. Restore any
entries it references as well, and revalidate its bindings.

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

The active entry remains a draft awaiting maintainer review. See the
[authoring guide](../docs/entry-sources.md).

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
Erdős–Szekeres and sets-and-maps entries remain unformalized until measured attempts
are launched.

## Validation

```sh
uv run python app/manage.py check_formalizations
uv run python app/manage.py validate_corpus
uv run python app/manage.py test catalog
```
