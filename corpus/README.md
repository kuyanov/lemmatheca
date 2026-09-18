# Mathematical corpus

Two Codex-authored draft entries under Apache-2.0:

- [Sumsets and translations](entries/thm-sumset-lower-bound/entry.html), with
  [metadata](entries/thm-sumset-lower-bound/entry.json), an SVG illustration,
  a table, and a labelled equation with a clickable reference.
- [Adding three sets](entries/thm-triple-sumset-lower-bound/entry.html), with
  [metadata](entries/thm-triple-sumset-lower-bound/entry.json), citing results
  in the first entry, plus a sharper integer bound with a human proof and two
  Lean helper statements with unfinished (`sorry`) proofs.

Each folder owns its HTML, JSON, and assets. [Taxonomy](taxonomy.json) describes
subjects; [reading order](reading-order.json) controls listings and “Next entry”.
The compact JSON has no version fields or separate proof records. Unproved Lean
statements are listed per block as `unformalized_dependencies`, each with a
`declaration`, `module`, and `source`. The website links both pending dependencies
and completed formalizations to the general Lean file viewer.
A nonempty list prevents `complete` status; existing,
checked mathlib lemmas are not pending dependencies. Authors, license, optional source credit, and derived
formalization status are displayed on the website.

**Sumsets and translations** has six complete formal bindings, including existing
mathlib declarations. **Adding three sets** has four complete blocks and one
partial block, so its entry badge is partial. Both remain editorial drafts awaiting
maintainer review. See the [authoring guide](../docs/entry-sources.md).

```sh
uv run python app/manage.py check_formalizations
uv run python app/manage.py validate_corpus
uv run python app/manage.py test catalog
```
