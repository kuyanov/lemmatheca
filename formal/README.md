# Lean formalization

Lean **4.34.0** and mathlib **v4.34.0** are pinned by `lean-toolchain`,
`lakefile.toml`, and `lake-manifest.json`. Keep these fixed during an experiment.

## Setup

From the repository root:

```sh
source "$HOME/.elan/env"
cd formal
lake exe cache get
lake build
```

`.lake/` is local build/dependency data and is ignored by Git. The website can use
committed reports without installing it; missing mathlib sources link upstream.

## Formal nodes

Each `nodes/<id>.json` names a declaration, its dependencies, and human review.

Use stable IDs describing the mathematics, such as `set-insert-commute`,
independently of the entries that reference them.

```json
{
  "id": "set",
  "declaration": "Set",
  "module": "Mathlib.Data.Set.Defs",
  "dependencies": [],
  "review": null
}
```

Local modules live in `Lemmatheca/`; existing mathlib declarations are also valid.
The module specifies what to import. Current verification can locate the declaration
in a different source module, including Lean's bundled `Init`, `Lean`, and `Std`
sources. The reader uses the pinned Elan toolchain's installed source when available,
or a link to that Lean version on GitHub. Before a declaration exists, both
`declaration` and `module` may be `null`, with `review: null`.

The sets-and-maps entry has bindings for every mathematical block, including
examples and question answers. Its local declarations are in `SetsAndElements`,
`SetOperations`, and `Maps` under `Lemmatheca/SetTheory/`. The notation-and-conventions
block has an empty mapping. All 121 nodes have accepted reviews and passing
verification. Two proof passes completed 31 and 55 theorem proofs, preserving
every reviewed target hash. These modules contain no `sorry` placeholders.
Ambient types (or subtypes) specify each universe,
domain, and codomain. In the formula question, the reciprocal is specified by
`x * y = 1`, since Lean's division itself is total even at zero.

After inspecting the declarations and their correspondence to the human text,
record your review from the repository root:

```sh
uv run python app/manage.py review --accept --node set-intersection
uv run python app/manage.py review --accept --node set-union set-complement
uv run python app/manage.py review --accept --entry sets-and-maps --dry-run
uv run python app/manage.py review --accept --entry sets-and-maps
```

`--accept --entry` accepts each distinct linked node once; it rejects blocks without
formal mappings. Empty mappings are allowed. Dependencies not linked from that
entry are not automatically accepted. This records formal-target approval, not
editorial publication or proof completion. Shared nodes keep one shared review.

Acceptance refreshes Lean checks when needed, allows `sorry`, and writes a record
instead of a boolean:

```json
"review": {
  "sha256": "<64 lowercase hexadecimal characters>",
  "recorded_at": "<ISO timestamp with timezone>"
}
```

The SHA-256 covers the elaborated target, referenced definitions and inductive
constructors, node identity/dependencies, and pinned environment. Theorem proofs
are excluded; definition bodies are included. Source comments and positions are
excluded. A changed statement or relevant definition makes an existing review
outdated after rechecking. A proof-only edit requires fresh verification but keeps
an unchanged statement's approval. Hashes compare structural declarations, not
arbitrary mathematical equivalence.

To withdraw approval, use the same selectors with `--retract`:

```sh
uv run python app/manage.py review --retract --node set-intersection
uv run python app/manage.py review --retract --entry sets-and-maps --dry-run
uv run python app/manage.py review --retract --entry sets-and-maps
```

Retraction sets existing review records to `null`, leaving other node metadata
and verification evidence intact. It does not run Lean and works with missing or
stale verification and outdated approvals. Whole-entry retraction clears each
distinct linked node once, skipping unmapped blocks; unlinked nodes retain their
reviews. Retracting a shared node affects every entry using it. Nodes without a
review are skipped.

Exactly one of `--accept` and `--retract` is required. Both support `--dry-run`,
which previews changes without editing node records; acceptance can still refresh
the verification report. Reaccepting a current review is a no-op,
including its timestamp. To accept a changed target, inspect it and run the same
command again. Completion also requires passing evidence and ready dependencies.

| Derived status | Meaning |
| --- | --- |
| `declaration_missing` | No declaration assigned |
| `review_pending` | Statement needs human approval |
| `verification_needed` | No valid check for the current declaration |
| `review_outdated` | The checked target differs from the accepted hash |
| `proof_pending` | A current check found direct or transitive `sorry` |
| `dependencies_pending` | A declared dependency is incomplete |
| `complete` | Statement, proof, and dependencies are ready |

The first applicable row determines the node badge and API status. Entry HTML
links to nodes with [`data-formal`](../corpus/README.md#block-to-node-mapping).

## Checking nodes

From the repository root:

```sh
uv run python app/manage.py check_formalizations
```

The command builds registered modules, checks declarations and transitive axioms,
exports review snapshots through `Lemmatheca.ReviewChecks`, and writes
`checks/nodes.json` with target hashes and source locations. Only `propext`, `Classical.choice`, and `Quot.sound`
are allowed in complete proofs; `sorryAx` remains unfinished.

The registry determines which declarations receive an axiom audit. `lake build`
compiles the library; `check_formalizations` records the evidence used by the reader.
The historical sumset report is retained separately from the active node checks.

Rerun after changing declarations, dependencies, Lean sources, or environment pins.
Review records do not invalidate evidence. Lean checks correctness; maintainers
check correspondence with the human mathematics. See
[verification and review](../docs/verification-and-review.md) for evidence rules
and [experiment design](../docs/formalization-experiments.md) for measured runs.
