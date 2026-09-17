# Draft corpus examples

These JSON and Markdown files make the proposal concrete. They are **unpublished,
AI-authored design examples**. No maintainer has accepted them, the general
statements are not yet formalized, and no full Lean dependency audit has run.

The [first Lean project](../formal/README.md) now checks the concrete integer
illustration `{0, 1} + {0, 2} = {0, 1, 2, 3}` from `definition.md` and two supporting
translation lemmas. This does not yet verify the general cardinality lower bound
or turn these draft records into accepted entries.

`taxonomy.json` demonstrates areas, subareas, and topics. Its small initial tree
is extensible and does not claim complete coverage. `external-lemmas.json` is an
empty draft registry; it grants no exceptions.

`sumsets/definition.json` describes a definition.
`sumsets/lower-bound.json` describes a separate statement.
`sumsets/proofs/translation.json` describes one proof, pinned to the statement's
draft revision. Their `text` paths are relative to their own JSON files. Related
entry IDs and prerequisite proposals are explicit.

Prerequisites marked `planned` deliberately do not resolve to accepted entries.
The future publication validator must reject these records until the prerequisites
are resolved, the formalizations are verified, and a human maintainer approves.
These files are examples of a proposed format, not its production JSON Schema.
