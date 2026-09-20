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
with collapsible answers. Estimated reading time: 40 minutes. Definition 1 links
to nine formal nodes whose review is tracked individually, with new proofs left pending.
The other 20 blocks remain `not_started` for a measured pass.

The earlier examples are archived outside the live entry tree:

- [Sumsets and translations](backup/thm-sumset-lower-bound/entry.html): six complete bindings.
- [Adding three sets](backup/thm-triple-sumset-lower-bound/entry.html): four complete blocks
  and a partial integer bound with two pending Lean helper proofs.
- [Finding a monotone subsequence](backup/thm-erdos-szekeres/entry.html): four unformalized
  blocks based on Seidenberg's proof, reserved for a future measured experiment.

`backup/` is excluded from the live corpus. Its JSON preserves the previous
format as a historical snapshot. Tests copy the human HTML and ordinary metadata
into temporary fixtures; formal-node tests use separate fixtures. To restore an
archived entry, remove its old JSON `blocks`, add its subjects and reading-order
record, and restore entries linked by its HTML. Register formal nodes and add
reviewed HTML mappings separately; old reports do not certify new nodes.
[Taxonomy](taxonomy.json) contains the working areas;
[taxonomy_complete.json](taxonomy_complete.json) is reference material only.

## Entry format

Each folder owns its HTML, JSON, and assets. JSON contains only:

```text
id, title, based_on, primary_area, additional_areas,
status, reading_time, summary, abstract
```

There are no JSON blocks, formalization objects, or duplicated references.
The HTML owns block IDs, kinds, titles, order, and links. The reader validates
HTML reference targets directly and derives local labels and return navigation.
`status` is editorial and independent of formal readiness. The `based_on`
bibliography shows the first source compactly, with further sources collapsed.
[Reading order](reading-order.json) controls listings and “Next entry”. See the
[authoring guide](../docs/entry-sources.md) for equations, figures, tables, and links.

## Block-to-node mapping

Human-only submissions need no formalization records. A mathematical section in
`entry.html` can optionally link to records in `formal/nodes/<id>.json`:

| HTML attribute | Meaning |
| --- | --- |
| No `data-formal` attribute | Formalization not started; planning is still needed |
| `data-formal=""` | Not applicable: nothing to formalize |
| `data-formal="example-lemma1 example-lemma2"` | Both formal nodes cover this block |

Node IDs are stable references independent of displayed numbers and categories.
The same node can serve several blocks or entries. An entry-prefixed ID is fine,
but reordering an article must not rename it. Unknown or duplicate node IDs are
validation errors. A question maps its answer or counterexample. Definitions may
map to existing Lean definitions; no artificial theorem is needed.

In the [submission pipeline](../README.md#submission-and-formalization-pipeline),
AI proposes statements and mappings for human review. Committing `data-formal`
is currently the maintainer's record of approving coverage, including empty
mappings. Proposed mappings must be reviewed before being merged. There is no
separate mapping-review service yet. Nodes also record statement review; changing
the intended statement requires renewed review before autonomous proving.

Each block's header badge shows **Not started**, **N/A**, **✓ Complete**, or **◷ 50%**.
If there are nodes, the badge opens a list of their IDs, status icons, and links
to dedicated source pages. No verification footer is needed.

Block percentages count ready nodes, not estimated effort. Entry badges show
**Not started**, **Partial**, or **Complete**, without a percentage. Entry totals
deduplicate shared nodes, and the tooltip gives the count of unmapped blocks.
An entry stays **Partial** when linked nodes are ready but other blocks are still
unmapped. An entry with only not-applicable blocks is N/A, not verified.
See [formal nodes](../formal/README.md#formal-nodes) for readiness and evidence.

## Growing the collection

Choose a book section and related mathlib modules, match their hypotheses and
definitions, then group the material into a readable note. Human text can be
submitted before any Lean work. During its formalization pass, reuse matching
checked mathlib declarations; reserve new Lean proofs for missing mathematics or
experiments on translating a particular argument. A correct binding alone does
not establish that the human proof's strategy has been formalized.

Use original exposition and precise `based_on` citations. Generate only the human
content sections; the shared templates already provide page layout and navigation.
Human editing should improve explanation, mathematical correspondence, and figures.
Preserve stable block IDs and update the primary area's reading order when adding
an entry. Additional areas are metadata only in the current reader.

Keep prompts, attempts, cost measurements, and human review time in experiment
records outside `entry.json`. No run-record system is implemented yet. The
Erdős–Szekeres entry and the remaining sets-and-maps blocks are reserved for
measured attempts. Definition 1's declaration pilot is available for review;
it does not include a measured proof-writing run.

## Validation

```sh
uv run python app/manage.py check_formalizations
uv run python app/manage.py validate_corpus
uv run python app/manage.py test catalog
```
