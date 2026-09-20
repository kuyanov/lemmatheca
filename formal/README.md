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
  "reviewed": false
}
```

Local modules live in `Lemmatheca/`; existing mathlib declarations are also valid.
The module determines the source path. Before a declaration exists, both
`declaration` and `module` may be `null`, with `reviewed: false`.

Set `reviewed: true` after approving a statement. This takes effect without a
Lean rerun. Completion also requires current passing evidence and ready
dependencies. Clear approval if the statement's meaning changes.

| Derived status | Meaning |
| --- | --- |
| `declaration_missing` | No declaration assigned |
| `review_pending` | Statement needs human approval |
| `verification_needed` | No valid check for the current declaration |
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
and writes `checks/nodes.json`. Only `propext`, `Classical.choice`, and `Quot.sound`
are allowed in complete proofs; `sorryAx` remains unfinished.

Rerun after changing declarations, dependencies, Lean sources, or environment pins.
Review toggles do not invalidate evidence. Lean checks correctness; maintainers
check correspondence with the human mathematics. See
[verification and review](../docs/verification-and-review.md) for evidence rules
and [experiment design](../docs/formalization-experiments.md) for measured runs.
