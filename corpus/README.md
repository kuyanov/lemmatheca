# Mathematical corpus

The active collection starts with [Sets and maps: a first guide](entries/sets-and-maps/entry.html),
followed by [Equivalence relations, partitions, and quotients](entries/equivalence-relations/entry.html).
The second entry is a human draft awaiting review and formalization. Entries are
edited as repository files and reviewed manually; source credits appear in their metadata.

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
status, reading_time, summary, abstract
```

HTML owns mathematical blocks, titles, links, and formal-node mappings.
`status` is editorial; formal readiness is derived separately. Write original
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
`uv run python app/manage.py review --accept --entry <id>` to record approval of an
entry's linked nodes, or `--node <id>` for an individual node. Replace `--accept`
with `--retract` to withdraw approval. Reviews store
target hashes, so changed declarations require renewed approval. Block percentages count
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
