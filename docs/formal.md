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
for both importing and browsing its source. There is no separate import/source
module field. A node can bind directly to a local, mathlib, or Lean core declaration.
Before a target exists, `module` and `declaration` may both be `null`; start new
nodes with `verified: false`.

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
Keep useful prerequisites without cycles or their transitive closure. A listed
hint's verification flag does not determine the node's flag. Lean's actual use of
an unfinished declaration does affect verification, even if that declaration is
not listed as a hint.

Put local modules under `formal/Lemmatheca/` and import them from
`formal/Lemmatheca.lean`.
Use appropriate namespaces for reusable mathematics and
`Lemmatheca.Entry.<EntryName>` for entry-specific examples. Keep related declarations
together rather than creating nearly empty modules. Use the existing Lean project;
do not introduce separate per-entry Lake projects.

## Build and verification

From the repository root:

```sh
uv run python app/manage.py validate_corpus
uv run python app/manage.py build
uv run python app/manage.py test catalog
```

The build reads the node registry, builds `Lemmatheca` and the bound non-core
modules, and checks each registered declaration with `formal/Lemmatheca/ProofStatus.lean`.
Core modules are supplied by the toolchain. The checker collects transitive axioms:
only `propext`, `Classical.choice`, and `Quot.sound` are allowed. Direct or inherited
`sorryAx`, or additional axioms, give `verified: false`. Definitions use the same
rule; a comment containing the word `sorry` does not affect the result.

A successful build may contain unfinished proofs. It records those nodes as
Not verified, while declarations that pass the check become Verified. Unbound
nodes are Not verified. A missing declaration, invalid binding, or compilation
error fails the build instead of producing a new verification result.

After checking Lean, the build parses entry HTML and computes entry-list summaries
from the new results. It validates all summaries before saving node records and the
`formalization` object in each `corpus/entries/<id>/entry.json`. Failed Lean checks
or invalid summaries write neither set of results; prior saved data stays intact.
The build also prepares the home-page statistics and count history before saving
any results. Changed counts append timestamped history points; unchanged counts
keep their previous series. Failed builds leave the history intact too.
Individual JSON files are replaced atomically.

Commit changed Lean sources, bindings, and all generated node and entry JSON
alongside the change, including `corpus/statistics.json`. Verification describes
the last successful build: the server
never runs Lean or performs source-freshness checks on a page request. Rerun the
build after editing proofs, bindings, or entry block mappings. To compile locally
while working, `lake build` from `formal/` is useful, but it does not refresh corpus
JSON; finish with the Django build command.

The [CI workflow](../.github/workflows/ci.yml) validates the corpus, installs the
pinned environment, checks source availability, runs the tests and build, then checks that committed node results and entry
summaries match regenerated files. The tests exercise successful, unfinished,
unsupported-axiom, missing-declaration, and failed builds in an isolated Lean project.
`formal/.lake/` contains ignored local dependencies and build output.

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
