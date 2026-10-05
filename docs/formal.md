# Lean project

All active formalizations share the Lake project in [`formal/`](../formal/).
The environment is pinned by [lean-toolchain](../formal/lean-toolchain),
[lakefile.toml](../formal/lakefile.toml), and
[lake-manifest.json](../formal/lake-manifest.json). Use those files as the version authority;
keep their pins fixed unless an environment upgrade is part of the task. The Lean
environment and dependency sources are assumed to be installed; see the
[setup instructions](../README.md#lean-environment) for a fresh checkout.

## Formal nodes

Node records live in `corpus/nodes/<id>.json`, independently of the entries that
reference them. A new binding can be written as:

```json
{
  "id": "set-subset-transitive",
  "description": "If A is a subset of B and B is a subset of C, then A is a subset of C.",
  "module": "Mathlib.Data.Set.Basic",
  "declaration": "Set.Subset.trans",
  "dependencies": ["set-subset"],
  "axioms": ["choice"],
  "verified": false
}
```

Use stable mathematical IDs and reuse existing nodes where possible. `description`
is plain text stating the result with its hypotheses, domains, and quantifiers,
or describing the object being defined. It should make sense without opening an
entry. Mathematical notation is supported; escape LaTeX backslashes in JSON, for
example `"For every set \\(A\\), \\(A\\cup\\varnothing=A\\)."`. Avoid HTML, proofs,
and implementation commentary in descriptions.

`declaration` is the full Lean name. `module` is the module that defines it, used
for both importing and browsing its source. There is no separate import/source
module field. A node can bind directly to a local, mathlib, or Lean core declaration.
Before a target exists, `module` and `declaration` may both be `null`; start new
nodes with `verified: false`.

`axioms` is required on every node, including unbound definitions. It records the
extra mathematical assumptions permitted above ZF, independently of generated
verification data. For now, use `["choice"]` for every node: the mathlib-based
formal project permits ambient AC throughout, including definitions, human
ZF-only results, and implications between choice principles. This allowance
does not claim that AC is mathematically necessary. The currently supported
identifier is `choice`; unknown identifiers and duplicates are rejected.

The current formal verification checks statements in the ambient ZFC development.
It does not certify that a human argument uses only ZF, that a weaker choice
principle suffices, or that an equivalence holds over a weaker base theory.
Preserve and assess those human claims separately. Ordinary authoring and proving
should reuse mathlib without trying to eliminate `Classical.choice`.

The format and checker still support `[]` for explicitly requested experiments
with narrower allowances; it is not the current corpus convention. Shared nodes
carry one allowance wherever they are used, and the build applies it separately
to each node. Adding narrower principles to the supported vocabulary requires
an appropriate formal encoding and checker support. The node page displays the
declared allowance as “ZF only” or “ZF + AC”; current corpus nodes all display
“ZF + AC”. The API includes the authored `axioms` array.

The build writes `verified`, the pretty-printed `signature`, and `declaration_line`,
and refreshes `module` from Lean's defining-module information. Do not fabricate
these results or source locations. Generated declarations may point to a source
origin with a different name; compare the exported signature with the actual target.
The reader uses local project, Lake dependency, and Elan toolchain sources for its
source browser and line links.

## Bindings and proof planning

Inspect existing nodes and the pinned library before introducing declarations.
Prefer direct bindings to existing definitions or theorems, including suitable
specializations and equivalent formulations. Avoid wrappers whose only purpose is
to rename, reverse, or bundle existing results. Explain representation changes in
the GitHub review, and check domains, quantifiers, conventions, and assumptions.
Several nodes may collectively cover a block, and one node may serve several blocks.
See the [mapping contract](corpus.md#block-to-node-mapping).

`dependencies` contains direct proof-planning hints. It is not a reading order,
a list of every concept in a statement, or an extracted Lean dependency graph.
Keep useful prerequisites without cycles or their transitive closure.
Each node's allowance must include all axioms declared by its direct dependencies,
even for unfinished or unbound nodes. Direct-edge checks enforce inheritance along
longer chains. `validate_corpus` fails on a mismatch, identifying the source node,
each missing axiom, and the prerequisites declaring it. The build applies the
same check before writing any results. All current nodes permit AC, so ordinary
proof plans share that allowance. A permitted axiom need not actually be used,
and a hint need not match the current Lean proof. A listed hint's verification
flag does not determine the node's flag. Lean's actual use of an unfinished
declaration does affect verification, even if that declaration is not listed as
a hint.

Put local modules under `formal/Lemmatheca/` and import them from
`formal/Lemmatheca.lean`.
Use appropriate namespaces for reusable mathematics and
`Lemmatheca.Entry.<EntryName>` for entry-specific examples. Keep related declarations
together rather than creating nearly empty modules. Use the existing Lean project;
do not introduce separate per-entry Lake projects.

## Build and verification

After editing Lean declarations or proofs, node bindings or axiom allowances,
or entry block mappings, refresh verification from the repository root:

```sh
uv run python app/manage.py build
```

Run `uv run python app/manage.py validate_corpus` when node metadata, bindings,
or entry structure changes. Run relevant catalog tests for reader or build-tooling
changes, or when investigating an integration failure; routine proof edits do not
require them.

The build reads the node registry, builds `Lemmatheca` and the bound non-core
modules, and checks each registered declaration with `formal/Lemmatheca/ProofStatus.lean`.
Core modules are supplied by the toolchain. The checker reports each declaration's
transitive kernel axioms, including dependencies in its type and definition. The
build applies the allowance separately for each node: `propext` and `Quot.sound`
are always supported, while `Classical.choice` is permitted only by `"choice"` in
that node's `axioms`. Any undeclared Choice dependency, direct or inherited
`sorryAx`, or unsupported custom axiom gives `verified: false`. Declaring Choice
does not permit unfinished proofs or arbitrary axioms. Definitions use the same
rule; a comment containing the word `sorry` does not affect the result. Raw kernel
names are checker diagnostics, not a replacement for the authored `axioms` array.

A successful build may contain unfinished proofs or unmet axiom allowances. It
records those nodes as Not verified and continues checking all other nodes;
declarations that pass their own checks become Verified. Unbound
nodes are Not verified. A missing declaration, invalid binding, or compilation
error fails the build instead of producing a new verification result.

After checking Lean, the build parses entry HTML and computes entry-list summaries
from the new results. It validates all summaries before saving node records and the
`formalization` object in each `corpus/entries/<id>/entry.json`. Failed Lean checks
or invalid summaries write neither set of results; prior saved data stays intact.
Metadata edits made while Lean runs are preserved. A changed binding discards its
stale proof result; the current authored axiom allowance is applied to the returned
kernel report. Dependency-allowance errors prevent publication of all prepared
results. Individual JSON files are replaced atomically. Home-page statistics and count
history are updated separately by automation after pushes to `main`; the proof
build neither reads nor writes `corpus/statistics.json`.

Commit changed Lean sources, bindings, and all generated node and entry JSON
alongside the change. Verification describes
the last successful build: the server
never runs Lean or performs source-freshness checks on a page request. Rerun the
build after editing proofs, bindings, axiom allowances, or entry block mappings. To compile locally
while working, `lake build` from `formal/` is useful, but it does not refresh corpus
JSON; finish with the Django build command.

The [CI workflow](../.github/workflows/ci.yml) validates the corpus, installs the
pinned environment, checks source availability, runs the tests and build, then checks that committed node results and entry
summaries match regenerated files. The tests exercise successful, unfinished,
undeclared direct and inherited Choice, unsupported-axiom, missing-declaration,
and failed builds in an isolated Lean project. They also check different allowances
for shared declarations, dependency-allowance errors, metadata edits, and node-page/API
presentation.
`formal/.lake/` contains ignored local dependencies and build output.

### Inspecting kernel axioms

The build consumes kernel reports internally and prints verification totals; it
does not save `lean_axioms` in node JSON. To inspect a declaration without updating
the corpus, run from `formal/` after compiling the relevant modules:

```sh
lake env lean --stdin <<'LEAN'
import Lemmatheca
#node_status "Set.Subset.trans"
LEAN
```

Replace the declaration name and import its module if it is not included in
`Lemmatheca`. The `NODE_STATUS` report includes `lean_axioms`. Its `verified` flag
only rejects unfinished proofs and globally unsupported axioms; it does not read
node metadata. In an explicitly requested narrower-allowance experiment, a report
containing `Classical.choice` can have `verified: true` while a node bound to that
declaration with `axioms: []` remains Not verified after the build applies its
allowance. Current corpus nodes all permit Choice.

## Interpreting axiom checks

The node build's kernel checks do not formalize derivability from first-order ZF.
Lean derives classical excluded middle using `Classical.choice`, and library
representations can introduce it through chosen representatives. Consequently, a
failed allowance check does not establish that the mathematical statement needs
Choice.
Record whether a finding arises from classical logic, a representation, or an
actual selection argument before making claims about mathematical axiom strength.
A passing result likewise does not establish ZF derivability. See Lean's
[account of classical axioms](https://lean-lang.org/theorem_proving_in_lean4/Axioms-and-Computation/).

## Choice dependence in the pinned library

The following observations explain the current ambient-AC convention. They are
limits on isolating mathematical axiom strength, not verification blockers under
the current allowances.

The local natural-number sets are built directly from finite pre-sets, with
enumeration, induction, Peano properties, and comparison proved without general
ordinal representatives. Transitive closure lifts an explicit pre-set construction
through the quotient once, rather than selecting representatives for each member
of an indexed family. Its membership characterization and universal property are
checked in Lean. The old indexed-union expression is still proved equal to this
construction when proving the rank result. Finite membership cycles are ruled out
directly by membership induction. Integer and finite-order examples use explicit
case analysis, and the rational equivalence relation uses integer cross-products.

The pinned library introduces Choice in several ways:

- Some dependencies already occur in a declaration's signature, through general
  ordinal orders or representatives, rational arithmetic, or other library
  structures. A new proof of that same signature cannot remove those dependencies.
- Computable library operations can depend on Choice through their proof fields.
  In the pinned toolchain, `Rat.mul` and `Rat.add` have such dependencies; many
  rational and cut statements inherit them. Their computation is not a selection
  of arbitrary elements, but the kernel check still follows those proofs.
- General ranges of `ZFSet`-valued functions use `Quotient.out` and shrinking
  equivalences. The current Replacement witnesses inherit this dependency;
  eliminating their local `.choose` alone would not remove transitive Choice.
- `choice_iff_wellOrdering` and `wellOrdering_iff_zorn` still invoke ambient
  well-ordering or Zorn results. Formalizing their derivations from the explicit
  premises requires a development that also avoids the library's ambient choices.
  Other proof-only findings, such as existence of a least member of an arbitrary
  subset and total comparison of arbitrary cuts, involve classical reasoning.

Keep the pinned dependency sources intact and preserve mathematical statements.
Ordinary proof work permits these Choice dependencies; isolating AC requires an
explicitly requested development. Rerun the corpus build after changing proofs;
it checks their transitive axioms against the declared allowance and refreshes
verification data.

## Review and proving

Reviews of human exposition and formal correspondence take place on GitHub. There
are no in-app approvals, review commands, hashes, or dates. Verification checks the
Lean declaration; it does not prove that the description or entry says the same
thing. Review the mathematical text, block coverage, and description-to-declaration
correspondence separately.

Use the [contribution workflow](../CONTRIBUTING.md). Preserve the intended
statement and definitions while replacing unfinished proofs. Use unregistered
helpers for routine proof steps; add a node only when it represents useful
mathematical coverage. Keep proof-search or translation logs outside corpus
metadata, and distinguish library reuse from translating a particular human proof.
