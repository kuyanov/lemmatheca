# Mathematical corpus

The active collection starts with [Sets and maps: a first guide](entries/sets-and-maps/entry.html),
followed by [Equivalence relations, partitions, and quotients](entries/equivalence-relations/entry.html)
and [Ordered sets: comparison, bounds, and quotients](entries/ordered-sets/entry.html).
The first two entries have complete formal verification and current node approvals:
127 nodes for sets-and-maps and 71 for equivalence-relations, sharing ten nodes.
The third is a human draft; its formalization has not started. All three retain
draft editorial status. Entries are edited as repository files and reviewed manually;
source credits appear in their metadata.

## Entry format

```text
entries/<entry-id>/
  entry.json
  entry.html
  assets/       # Optional images and supplementary files
```

Use stable IDs independent of subject categories. JSON contains:

```text
id, title, based_on, primary_area, additional_areas,
review, reading_time, summary, abstract
```

HTML owns mathematical blocks, titles, links, and formal-node mappings.
Cross-entry references use `href="entry-id#block-id"`; same-entry references use
`href="#block-id"`. The reader resolves the stable IDs to URLs, independently of
subject areas. Prefer empty local links for generated numbering and explicit
cross-entry text that fits the sentence. Figures and tables have separate numbering
within each entry; give each a stable ID and one caption without a number.
`review` is `null` for a new draft, or a `{sha256, recorded_at}` approval record.
The reader derives `final` only when its hash matches the current entry; otherwise
it shows `draft`. There is no stored `status` field. Formal readiness is derived
separately. Only drafts show an editorial badge. Write original
exposition and cite sources in `based_on`. See the
[authoring guide](../docs/entry-sources.md) for the full source format.

## Block-to-node mapping

A submission needs no formalization. After planning and review, link a block to
records in `formal/nodes/` using its `data-formal` attribute:

| Attribute | Meaning |
| --- | --- |
| Absent | Formalization not started |
| `data-formal=""` | Nothing to formalize |
| `data-formal="node-a node-b"` | Formal nodes covering this block |

Definitions can use existing Lean definitions; questions map their answers.
Each linked node has a short mathematical description on its node page. Review
that description against the declaration as well as the entry; it is editorial
text, separate from the checked Lean signature.
Maintainers review both the declarations and coverage. Use
`uv run python app/manage.py review --accept --nodes-from-entry <id>` to record approval of an
entry's linked nodes, or `--node <id>` for an individual node. Replace `--accept`
with `--retract` to withdraw approval. Reviews store
target hashes, so changed descriptions or declarations require renewed approval.
Node IDs, proof dependencies, module locations, and environment pins are excluded from those
hashes. ID, module, or environment changes need fresh verification before approval can
be confirmed against the new declaration hash.

Use `uv run python app/manage.py review --accept --entry <id>` separately after
checking that the human text is correct, the page renders properly, and nodes
cover all blocks without redundant nodes or uncovered statements. This records
approval and hides the Draft badge and review note. Every block must have
a mapping (empty is allowed), and every linked node must name a declaration.
Proofs and node approvals may still be unfinished. Entry approval never runs Lean
or changes node records; `--retract --entry <id>` restores `draft`. All review
selectors support `--dry-run`. Metadata, HTML, asset, or linked node description
edits invalidate approval and restore Draft automatically. The HTML includes the
node IDs. Declarations, other node fields, unlinked descriptions, and Lean evidence
are excluded from this hash. Review and accept the changed entry
again when ready. See the [review workflow](../README.md#recording-reviews).

Block percentages count
ready nodes. Entry badges show Not started when every block is unmapped, Partial
while only some are unmapped, and a completed-node percentage (including 100%)
once all blocks have mappings. Shared nodes count once; an entry containing only
empty mappings displays N/A. Adding nodes can lower the percentage. See the
[content model](../docs/content-model.md) and [formal nodes](../formal/README.md#formal-nodes).

## Organization

`taxonomy.json` supplies the working subjects; `reading-order.json` orders entries
within their primary areas. `backup/` contains archived examples, excluded from
the reader. `taxonomy_complete.json` is reference material for future expansion.

Validate edits with `uv run python app/manage.py validate_corpus` from the repository
root. Keep prompts, attempts, and costs outside entry metadata; the
[experiment plan](../docs/formalization-experiments.md) describes the intended workflow.
