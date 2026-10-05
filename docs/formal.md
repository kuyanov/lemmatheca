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
for both importing and browsing its source. A node can bind directly to a local, mathlib, or Lean core declaration.
Before a target exists, `module` and `declaration` may both be `null`; start new
nodes with `verified: false`.

Formalization uses classical Lean and mathlib with `propext`, `Classical.choice`,
and `Quot.sound` permitted by default. This convention
permits Choice without asserting that it is mathematically necessary.
A Verified badge checks the Lean declaration; it does not certify provability
from first-order ZF or the strength of a weaker choice principle. Assess those
human claims separately using their arguments and an appropriate logical encoding.

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
A listed hint's verification flag does not determine the node's flag. Lean's
actual use of an unfinished declaration does affect verification, even if that
declaration is not listed as a hint. Validation checks dependency references and
cycles.

Put local modules under `formal/Lemmatheca/` and import them from
`formal/Lemmatheca.lean`.
Use appropriate namespaces for reusable mathematics and
`Lemmatheca.Entry.<EntryName>` for entry-specific examples. Keep related declarations
together rather than creating nearly empty modules. Use the existing Lean project;
do not introduce separate per-entry Lake projects.

## Build and verification

After editing Lean declarations or proofs, node bindings,
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
Core modules are supplied by the toolchain. The checker collects each declaration's
transitive kernel axioms, including dependencies in its type and definition.
Only `propext`, `Classical.choice`, and `Quot.sound` are permitted. Direct or inherited
`sorryAx`, or unsupported custom axioms, give `verified: false`. Definitions use the
same rule; a comment containing the word `sorry` does not affect the result.

A successful build may contain unfinished or unsupported proofs. It records those
nodes as Not verified and continues checking all other nodes; declarations that
pass the check become Verified. Unbound nodes are Not verified. A missing
declaration, invalid binding, or compilation error fails the build instead of
producing a new verification result.

After checking Lean, the build parses entry HTML and computes entry-list summaries
from the new results. It validates all summaries before saving node records and the
`formalization` object in each `corpus/entries/<id>/entry.json`. Failed Lean checks
or invalid summaries write neither set of results; prior saved data stays intact.
Metadata edits made while Lean runs are preserved. A changed binding discards its
stale proof result. Invalid dependency references prevent publication of all
prepared results. Individual JSON files are replaced atomically. Home-page statistics and count
history are updated separately by automation after pushes to `main`; the proof
build neither reads nor writes `corpus/statistics.json`.

Commit changed Lean sources, bindings, and all generated node and entry JSON
alongside the change. Verification describes
the last successful build: the server
never runs Lean or performs source-freshness checks on a page request. Rerun the
build after editing proofs, bindings, or entry block mappings. To compile locally
while working, `lake build` from `formal/` is useful, but it does not refresh corpus
JSON; finish with the Django build command.

The [CI workflow](../.github/workflows/ci.yml) validates the corpus, installs the
pinned environment, checks source availability, runs the tests and build, then checks that committed node results and entry
summaries match regenerated files. The tests exercise successful, unfinished,
unsupported-axiom, missing-declaration, and failed builds in an isolated Lean
project. They also check Choice used directly, through other declarations, or in
a type, and metadata edits during builds. `formal/.lake/` contains ignored local
dependencies and build output.

### Inspecting kernel axioms

To inspect a declaration without changing corpus data, run from `formal/` after
compiling the relevant modules:

```sh
lake env lean --stdin <<'LEAN'
import Lemmatheca
#print axioms Set.Subset.trans
#node_status "Set.Subset.trans"
LEAN
```

Replace the declaration name and import its module if it is not included in
`Lemmatheca`. Lean's `#print axioms` reports actual kernel dependencies;
`#node_status` reports verification, the signature, and source information.
Choice is always permitted by the proof checker. These kernel checks do not establish mathematical necessity
or derivability from first-order ZF; classical logic and library representations
can introduce `Classical.choice` independently of a human selection argument.

## Review and proving

Reviews of human exposition and formal correspondence take place on GitHub. Verification checks the Lean declaration; it does not prove that the description or entry says the same
thing. Review the mathematical text, block coverage, and description-to-declaration
correspondence separately.

Use the [contribution workflow](../CONTRIBUTING.md). Preserve the intended
statement and definitions while replacing unfinished proofs. Use unregistered
helpers for routine proof steps; add a node only when it represents useful
mathematical coverage. Keep proof-search or translation logs outside corpus
metadata, and distinguish library reuse from translating a particular human proof.
