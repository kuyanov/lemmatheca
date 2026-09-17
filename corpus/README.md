# Mathematical corpus

Two unpublished example submissions, each with one HTML source and a JSON sidecar:

- [Sumsets and translations](entries/thm-sumset-lower-bound/entry.html), with an
  entry-local SVG illustration and [metadata](entries/thm-sumset-lower-bound/entry.json).
- [Adding three sets](entries/thm-triple-sumset-lower-bound/entry.html), referencing
  specific results in the first note, with [metadata](entries/thm-triple-sumset-lower-bound/entry.json).

[Taxonomy](taxonomy.json) describes the browsing hierarchy.
[Reading order](reading-order.json) orders entries within their primary areas.
[External lemmas](external-lemmas.json) remains a separate, empty exception registry.
Neither Lean success nor an empty exception registry means a complete mathematical
dependency audit has been performed. Both notes await maintainer review.

See the [authoring guide](../docs/entry-sources.md) for the file contract, links,
assets, and Lean bindings. Validate changes with:

```sh
uv run python app/manage.py validate_corpus
uv run python app/manage.py test catalog
```
