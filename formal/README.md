# Lean project

All active formalizations belong to this Lake project. Its toolchain and mathlib
revision are pinned in `lean-toolchain`, `lakefile.toml`, and `lake-manifest.json`.
The Lean environment is assumed to be installed.

From the repository root:

```sh
uv run python app/manage.py build
```

The command builds `Lemmatheca` and the modules bound by nodes, then checks every
registered declaration and writes the boolean `verified` into `corpus/nodes/*.json`.
Each node's `module` is used for the import and source browser, and is updated to
the defining module reported by Lean. The build also records the pretty-printed
`signature` and `declaration_line` to display declarations and link to exact source lines.
`Lemmatheca/ProofStatus.lean` uses Lean's transitive axiom collection, so a proof
that relies on an unfinished helper is also not verified. A word in a comment has no
effect. A declaration is verified only if its axioms are among `propext`,
`Classical.choice`, and `Quot.sound`; additional axioms are not accepted as proofs.
For a definition, verified means the definition is checked under the same rule.
See Lean's [axiom documentation](https://lean-lang.org/doc/reference/latest/Axioms/).

A missing declaration, compilation error, or interrupted check fails the command
without writing node JSON. Verification, signatures, and source lines continue to
describe the last successful build.
Unbound nodes remain not verified. Unfinished proofs are a valid build result, so `sorry` alone
does not cause the command to fail.

Add local modules under `Lemmatheca/` and import them from `Lemmatheca.lean`.
Bind nodes using their full declaration name and module. Mathlib bindings use
this same environment. The website reads saved results and never invokes Lean.
