# First Lean proofs

This Lake project pins Lean **4.34.0** and uses only its bundled standard library.
There are no mathlib or other external package dependencies.

From the repository root:

```sh
source "$HOME/.elan/env"
cd formal
lake build
```

Sourcing `elan/env` makes `lean` and `lake` available in shells that do not yet have
`~/.elan/bin` on their `PATH`. The Lean VS Code extension is installed separately
from the compiler; `elan` manages the compiler version specified in `lean-toolchain`.

Open [`Sumsets.lean`](Lemmatheca/Combinatorics/Additive/Sumsets.lean) in VS Code to
inspect the proof steps with the Lean extension. This file proves:

1. A translate by an element of `B` lies inside `A + B`.
2. Translation of integers is injective, proved by subtracting the translation
   amount on both sides.
3. The concrete example `{0, 1} + {0, 2} = {0, 1, 2, 3}`, expressed as an
   equivalence of membership for every integer. The proof enumerates the four
   possible pairs and supplies a witness for each resulting sum.

Integer sets are predicates `Int → Prop` in this minimal example. The general
finite-cardinality inequality over arbitrary additive abelian groups remains a
separate, unformalized draft; the predicate encoding here does not commit the
future mathlib-backed corpus to a custom set library.

[`AxiomChecks.lean`](Lemmatheca/AxiomChecks.lean) is part of the default build and
asserts the actual output of `#print axioms` for each theorem:

| Theorem | Transitive axioms |
| --- | --- |
| `Lemmatheca.translate_mem_sumset` | None |
| `Lemmatheca.translate_injective` | `propext` (through standard integer lemmas) |
| `Lemmatheca.example_sumset` | None |

`propext` is propositional extensionality, one of the permitted foundational
axioms in the proposed policy. No theorem above depends on `sorryAx`, a custom
axiom, or compiler-trusting native evaluation. The concrete proof uses ordinary
`decide`, whose result is checked by Lean's kernel.

These assertions make the build fail if the reported axiom dependencies change.
They are not the planned full external-lemma dependency auditor or a maintainer's
editorial acceptance. The general example JSON records therefore remain drafts.
