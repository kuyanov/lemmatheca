# Lean proofs

This Lake project pins **Lean 4.34.0** and **mathlib v4.34.0**. The exact mathlib
commit and all transitive packages are recorded in `lake-manifest.json`.

From the repository root:

```sh
source "$HOME/.elan/env"
cd formal
lake exe cache get  # Fetch precompiled mathlib on a fresh checkout.
lake build
```

Sourcing `elan/env` makes `lean` and `lake` available in shells that do not yet have
`~/.elan/bin` on their `PATH`. The Lean VS Code extension is installed separately
from the compiler; `elan` selects the version specified in `lean-toolchain`.

## The mathematical notes

Open [`FiniteSumsets.lean`](Lemmatheca/Combinatorics/Additive/FiniteSumsets.lean) in
VS Code to inspect the proofs with the Lean extension:

1. **Sumset lower bound**, `Lemmatheca.sumset_card_lower_bound`: for finite nonempty subsets
   of any additive abelian group, `max A.card B.card ≤ (A + B).card`. The proof
   constructs two translation injections, matching the human argument.
2. **Triple sumset lower bound**, `Lemmatheca.triple_sumset_card_lower_bound`:
   `max (max A.card B.card) C.card ≤ ((A + B) + C).card`. It proves `A + B` is
   nonempty, then calls the first lemma twice, just as the website does.

The file also proves nonemptiness for two and three summands, the identity
`A + {0} = A`, and the counterexamples in the collapsible answers. The triple
nonemptiness lemma calls the two-set lemma twice. Display numbers belong to each
article and do not form part of a Lean declaration's identity.

Finite subsets use mathlib's `Finset`; `open scoped Pointwise` gives sumset
notation. The `DecidableEq G` instance lets finite sets compute membership and
remove duplicates. Classical equality supplies such an instance for any group,
so it adds no mathematical restriction to the human statement.

The first proof uses elementary finite-set infrastructure
(`Finset.card_le_card_of_injOn`, `Finset.mem_add`), group cancellation, and order
lemmas. It does not invoke an upstream sumset-cardinality bound. These are explicit
dependencies to review, not a blanket approval of mathlib. The full transitive
mathematical dependency auditor and foundations allowlist remain future work.

[`checks/sumsets.json`](checks/sumsets.json) records the local build and axiom
check, source hashes, entry/block revisions, and the pinned environment. This
is a development check record, not a production verification certificate or
maintainer approval. The entry metadata in `corpus/entries/` includes human-to-Lean step alignment.

## Original integer illustration

[`Sumsets.lean`](Lemmatheca/Combinatorics/Additive/Sumsets.lean) retains the earlier
standard-library-only illustration. It uses predicates `Int → Prop` to prove
translation membership, translation injectivity, and
`{0, 1} + {0, 2} = {0, 1, 2, 3}` by enumerating the four pairs.

## Axiom checks

[`AxiomChecks.lean`](Lemmatheca/AxiomChecks.lean) is part of the default build and
asserts the actual output of `#print axioms` for every example theorem:

| Theorem | Transitive axioms |
| --- | --- |
| `Lemmatheca.translate_mem_sumset` | None |
| `Lemmatheca.translate_injective` | `propext` |
| `Lemmatheca.example_sumset` | None |
| `Lemmatheca.sumset_card_lower_bound` | `propext`, `Classical.choice`, `Quot.sound` |
| `Lemmatheca.triple_sumset_card_lower_bound` | `propext`, `Classical.choice`, `Quot.sound` |
| `Lemmatheca.finite_sumset_nonempty` | `propext`, `Classical.choice`, `Quot.sound` |
| `Lemmatheca.sumset_zero` | `propext`, `Classical.choice`, `Quot.sound` |
| `Lemmatheca.triple_sumset_nonempty` | `propext`, `Classical.choice`, `Quot.sound` |
| `Lemmatheca.sumset_empty_counterexample` | `propext`, `Classical.choice`, `Quot.sound` |
| `Lemmatheca.triple_sumset_no_strict_growth` | `propext`, `Classical.choice`, `Quot.sound` |

These are the foundational axioms permitted by the proposed policy. None of these
proofs depends on `sorryAx`, a custom axiom, or compiler-trusting native evaluation.
The assertions fail the build if their reported axiom dependencies change. Axiom
checks do not substitute for review of the mathematical lemmas used in a proof.
