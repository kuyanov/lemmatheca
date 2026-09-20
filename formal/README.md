# Lean proofs

This Lake project pins **Lean 4.34.0** and **mathlib v4.34.0**. The exact mathlib
commit and all transitive packages are recorded in `lake-manifest.json`.

Its current role is to check formal nodes and provide a reproducible environment
for AI-formalization experiments. It is not an automated translator or experiment
runner. Keep these pins fixed during a comparison; record any upgrade as a new
environment. See the [experiment plan](../docs/formalization-experiments.md).

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

`formal/.lake/` is a local dependency/build directory and is ignored by Git.
Pulling the repository on another machine does not populate it; run the setup
commands above when you want to compile Lean or view mathlib sources locally.
The website can serve the corpus without it, using the committed reports and a
pinned GitHub source link for referenced mathlib files that are absent locally.
Keep the tracked Lean sources, reports, and manifest on the web server.

## Formal nodes

`formal/nodes/<id>.json` is the formal registry, independent of entry metadata.
Definition 1 of sets-and-maps currently links to nine nodes. Each records its
human review separately. A node record has exactly these fields (this is illustrative, not
an active node):

```json
{
  "id": "sumsets-lower-bound",
  "declaration": "Lemmatheca.sumset_card_lower_bound",
  "module": "Lemmatheca.Combinatorics.Additive.FiniteSumsets",
  "dependencies": [],
  "reviewed": false
}
```

Use the module actually containing the chosen declaration. Local declarations use
`Lemmatheca.*` modules in `formal/Lemmatheca/`; mathlib declarations use `Mathlib.*`.
The module determines the source path, so no duplicate `source` field is stored.
Each node names one declaration; a block can link any number of nodes. Definitions
can name existing definitions, structures, or instances. IDs stay fixed across
article reordering and can be reused by several entries.

Before a declaration exists, `declaration` and `module` can both be `null`, with
`reviewed: false`. Dependencies are unique node IDs; unknown IDs and cycles fail
validation. Pending Lean statements may contain `sorry`. A node has no editable
`status` or report path: readiness is derived from `formal/checks/nodes.json`.

A human sets `reviewed: true` after reviewing the intended formal statement.
Saving this flag takes effect on the next page load without rerunning Lean.
It changes **Pending review** to **Complete** only if the declaration already has
current passing evidence and ready dependencies. A reviewed theorem with `sorry`
still shows **Proof pending**. Setting the flag back to `false` withdraws approval
without discarding the Lean check.

Committing HTML `data-formal` mappings records the maintainer's coverage review,
including empty mappings. When changing a target's assumptions or conclusion,
clear its review flag and obtain renewed review. Review is currently a manual
repository convention; an automated target-locking or review service is not
implemented. Proof attempts must keep approved targets fixed.

Node pages at `/formal/nodes/<id>/` show the declaration, status, dependencies,
and escaped source with line numbers. The declaration line is inferred when
possible; generated declarations may have no source line. The separate read-only
API lives at `/api/formal/nodes/` and `/api/formal/nodes/<id>/`. It can be used
without loading the human corpus. Proving agents and write endpoints come later.

Nodes expose one derived `status` and its `status_label`, used by every badge.
There is no separate `reason` field or repeated reason paragraph on the page.
The first applicable row determines the status:

| API status | Badge | Meaning |
| --- | --- | --- |
| `declaration_missing` | Declaration missing | No Lean declaration has been assigned |
| `review_pending` | Pending review | The declaration still needs human approval |
| `verification_needed` | Verification needed | The current declaration has no valid check |
| `proof_pending` | Proof pending | A current check found direct or transitive `sorry` |
| `dependencies_pending` | Dependencies pending | The declaration is approved and checked, but a dependency is incomplete |
| `complete` | Complete | The declaration and its dependencies are ready |

`checked_on` is present for a current check, including one that found an unfinished
proof. A stale check cannot determine proof readiness. The verification report
still records proof evidence as `complete` or `pending`; human review and
dependency readiness are combined with that evidence when deriving node statuses.

## Checking nodes

From the repository root:

```sh
uv run python app/manage.py check_formalizations
```

The checker builds all registered modules, imports them, runs `#check` and
`#print axioms`, and writes one atomic report to `formal/checks/nodes.json`.
It does not read archived or active JSON block bindings. With no declarations it
skips Lean and leaves historical reports alone. It also rejects formal inputs
that change during the check.

A ready node needs an approved statement, current passing evidence, and ready
node dependencies. The permitted foundational axioms are `propext`,
`Classical.choice`, and `Quot.sound`. Direct or transitive `sorryAx` is recorded
as pending; other axioms fail the run. There is no promotion based merely on a
successful build, and a proved node with an unfinished declared dependency stays
pending. Proof-dependency extraction is not implemented: declared node edges and
Lean's transitive axiom checks serve different purposes.

Evidence fingerprints node IDs, declarations, modules, and dependencies, but
excludes the human `reviewed` flag. It also covers the toolchain/manifest/Lake configuration,
all local Lemmatheca sources, and the source import closure of checked modules.
The reader compares fingerprints without running Lean; file hashes are cached
until file metadata changes. Source scanning is conservative and may invalidate
unrelated nodes from the same run. The import scanner supports ordinary module
imports; this is a trusted repository check, not an audit of arbitrary metaprograms
or custom build steps. Dependencies supplied with Lean use its toolchain pin.

A web-only checkout may omit `.lake/packages/`; recorded external source hashes
are checked when those files are installed, and otherwise the pinned environment
and committed report are trusted. Missing local sources are errors. Node edits
other than review toggles, source changes, or changed pins require a fresh check. A report does not establish
that the formal statement covers the human text or follows its proof strategy.

Keep prompts, attempts, statement-writing costs, proof-writing costs, and human
review time in separate experiment records. No model runner, costing system, or
autonomous proving service is implemented yet.

## Active corpus and archived examples

The active corpus contains only **Sets and maps: a first guide**. Its first
definition is a declaration pilot with nine nodes:

- Existing mathlib definitions: `Set`, `Set.Mem`, `Set.ofPred`, and `Set.insert`.
- A local definition of the set of even natural numbers.
- Four pending claims: insertion order, repeated insertion, the cardinality of
  `{2, 5, 8}`, and membership of zero in the even-number set.

The local declarations are in
[`SetsAndElements.lean`](Lemmatheca/SetTheory/SetsAndElements.lean). They compile,
but all four theorem proofs contain `sorry`. Review and proof work advance its
progress separately; each node's `reviewed` flag records human approval. The other
20 blocks remain `not_started` for a measured pass.

The examples discussed below are preserved in `corpus/backup/`, outside the live
reader and formalization checks. Their reusable Lean modules remain here.

## The existing sumset proofs

Open [`FiniteSumsets.lean`](Lemmatheca/Combinatorics/Additive/FiniteSumsets.lean) in
VS Code to inspect the proofs with the Lean extension:

1. **Sumset lower bound**, `Lemmatheca.sumset_card_lower_bound`: for finite nonempty subsets
   of any additive abelian group, `max A.card B.card ≤ (A + B).card`. The proof
   constructs two translation injections, matching the human argument.
2. **Triple sumset lower bound**, `Lemmatheca.triple_sumset_card_lower_bound`:
   `max (max A.card B.card) C.card ≤ ((A + B) + C).card`. It proves `A + B` is
   nonempty, then calls the first lemma twice, matching the archived human argument.

The file also proves nonemptiness for two and three summands, the identity
`A + {0} = A`, and the counterexamples in the collapsible answers. The triple
nonemptiness lemma calls the two-set lemma twice. Display numbers belong to each
article and do not form part of a Lean declaration's identity.

The archived **Finding a monotone subsequence** remains unformalized for later
measurements; it has no registered formal nodes.

Finite subsets use mathlib's `Finset`; `open scoped Pointwise` gives sumset
notation. The `DecidableEq G` instance lets finite sets compute membership and
remove duplicates. Classical equality supplies such an instance for any group,
so it adds no mathematical restriction to the human statement.

The first proof uses elementary finite-set infrastructure
(`Finset.card_le_card_of_injOn`, `Finset.mem_add`), group cancellation, and order
lemmas. It does not invoke an upstream sumset-cardinality bound. Existing mathlib
results are allowed as direct bindings. Full transitive mathematical dependency
extraction remains future work.

For standard-corpus curation, reuse a matching mathlib declaration instead of
duplicating its proof. For a proof-translation experiment, specify the permitted
prerequisites and check that the generated proof follows the supplied argument.
Calling an existing target theorem is a retrieval success, not evidence that its
human proof was translated. Record those outcomes separately.

[`checks/sumsets.json`](checks/sumsets.json) is a historical record in the old
format. It is not consumed by the node checker. Archived JSON bindings are not
live nodes; restoring them requires registering nodes and checking them anew.

The archived examples also used mathlib's `Finset.add` and `Finset.Nonempty.add`
and the local definitions `Lemmatheca.translateFinset` and `Lemmatheca.tripleSumset`.
Pending helper statements still live in:

- [IntegerSumsetChain.lean](Lemmatheca/Combinatorics/Additive/Pending/IntegerSumsetChain.lean)
- [IncreasingListCard.lean](Lemmatheca/Combinatorics/Additive/Pending/IncreasingListCard.lean)

Their `sorry` proofs remain unfinished. They are not imported by the main library
and are not checked by the node command unless registered. Registered node pages
display the relevant source; other files can be read directly in the repository.

## Original integer illustration

[`Sumsets.lean`](Lemmatheca/Combinatorics/Additive/Sumsets.lean) retains the earlier
standard-library-only illustration. It uses predicates `Int → Prop` to prove
translation membership, translation injectivity, and
`{0, 1} + {0, 2} = {0, 1, 2, 3}` by enumerating the four pairs.

## Axiom checks

[`AxiomChecks.lean`](Lemmatheca/AxiomChecks.lean) is part of the default build and
asserts the actual output of `#print axioms` for the following local example theorems:

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

These are the foundational axioms permitted by the implemented checker. None of these
proofs depends on `sorryAx`, a custom axiom, or compiler-trusting native evaluation.
The assertions fail the build if their reported axiom dependencies change. Axiom
checks do not substitute for review of the mathematical lemmas used in a proof.
