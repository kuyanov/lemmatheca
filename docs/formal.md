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
  "description": "If \\(A\\subseteq B\\) and \\(B\\subseteq C\\), then \\(A\\subseteq C\\).",
  "module": "Mathlib.Data.Set.Basic",
  "declaration": "Set.Subset.trans",
  "dependencies": ["set-subset"],
  "verified": false
}
```

Use stable mathematical IDs and reuse existing nodes where possible. `description`
is readable mathematical prose stating the result with its hypotheses, domains,
and quantifiers, or describing the object being defined. It should make sense without opening an
entry. Write ordinary prose normally, and put mathematical notation in
`\(...\)` for inline formulas or `\[...\]` for display formulas. This includes
variables, subscripts, function applications, quantifiers, and expressions using
relation or operation symbols. Raw Unicode symbols or ASCII expressions such as
`z0<z1` remain ordinary text in the reader; dollar signs and Markdown backticks
are not supported math delimiters. Escape every LaTeX backslash in JSON, for
example `"For every set \\(A\\), \\(A\\cup\\varnothing=A\\)."` or
`"The natural-number order satisfies \\(\\forall z_0\\,\\exists z_1\\;(z_0<z_1)\\)."`.
Use LaTeX commands for the intended symbols and operators, such as `\omega_1`,
`\mathfrak{b}`, and `\operatorname{cf}`. Check that an ASCII spelling inside a
formula has not become a product of letters. Keep ordinary words, including the
indefinite articles “a” and “A,” outside math delimiters. Decide from each
occurrence's mathematical context whether `a` is an article or a variable; a
blanket exclusion of that letter misses valid notation.
Use consistent notation for specific named ordinals and cardinals, such as
`\omega`, `\omega_1`, `\aleph_0`, `\beth_a`, and `\varepsilon_0`. Write indexed
families as complete formulas, such as `\aleph_a`, rather than mixing a worded
family name with a separately typeset index. General topic names such as
“aleph sequence” or “epsilon number” can remain prose.
Avoid HTML, proofs, and implementation commentary in descriptions.
For display formulas, follow the [corpus layout guidance](corpus.md#mathematics-figures-and-assets):
prefer natural horizontal statements on desktop and allow scrolling within the
formula on mobile. Do not stack the sides of an equivalence merely to fit a phone.

Check every new or edited description for notation outside math delimiters and
unmatched or nested delimiters, then inspect its rendered node page. Confirm that the
formulas render, subscripts and quantifiers display correctly, and there are no
KaTeX errors or literal LaTeX fragments. Valid JSON and a successful Lean build
do not check formula rendering. Formatting-only description changes require
corpus validation and a rendering check; unchanged bindings and proofs do not
need a Lean rebuild.
Review the complete descriptions as well as running symbol scans. Include ASCII
operator applications, fractions, decimals, tuples, intervals, set braces, and
variables that resemble English articles. For a corpus-wide audit, inspect
untouched records too; a scan for Unicode symbols or single-letter tokens alone
does not cover these cases. State the actual coverage and limitations of checks.

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
Ordinary mathematical conclusions may be bound to classical Lean theorems even
when the human argument assumes only countable or dependent choice. Such bindings
verify the conclusion under the default foundation, not the sufficiency of those
weaker assumptions; do not add a duplicate unbound node solely to record them.
Claims whose content is logical strength, including implications or equivalences
between choice principles, first-order recursion schemas, and equivalences between
axiom systems, remain unbound until an appropriate encoding exists. Adding a
provable choice principle as a Lean premise does not certify axiom strength.
Bind faithful principle definitions and constructions with supplied data separately.

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

Compare hypotheses, universes, subtypes, domains, codomains, and conclusions,
including existence versus uniqueness and boundary cases. Check library
conventions such as total division and natural-valued cardinality on infinite
sets. Inspect elaborated relations and typeclass instances, particularly for
custom types and literals; a type annotation alone may not select the intended
relation. When stating inverse laws, ensure both laws concern the same map.

Check which inputs each constructed witness may depend on. If one construction
must work for every background theory, choose it before quantifying over that
theory: `∀ σ, ∃ τ, ∀ T, ...`, rather than `∀ σ T, ∃ τ, ...`. Inspect the
statement itself, even when its proof happens to make a uniform choice. When the
claim concerns a specified map, the exposed conclusion must identify that map;
returning an embedding type alone does not state that its underlying function is
the supplied function. Retain an explicit identity or a predicate on that function.

When a proof uses a separate formula syntax, connect it to the shared syntax.
The translations must preserve satisfaction, variable scope, and any required
syntactic property such as being quantifier-free. Bind the resulting theorem for the actual theory;
binding a definition beside a theorem for an unrelated local syntax does not
establish that the theory satisfies the definition. Check dependent completeness,
elementarity, and definability claims in that same representation.

For a proof calculus, compare the primitive rules of the human and formal systems.
An operation made a constructor of the formal proof type has not thereby been
proved admissible in the human system. Derived-rule and conservative-expansion
claims require syntactic transformations into proofs using the stated basic rules.
If an extended proof representation is used, include this translation in the
formalization of completeness for the basic calculus. Soundness of the extension
alone does not provide it. Do not use the completeness theorem being constructed
to justify a syntactic step in its own proof. Distinguish substitution of free names
from instantiation of quantified placeholders, and define both operations when used,
including the treatment of fresh auxiliary names.

Step 4 implements translation definitions and states the necessary bridge,
preservation, and admissibility theorems, allowing unfinished proofs. Step 5 checks
that these definitions and statements would establish the intended correspondence.
Step 6 proves them before claiming completed formal coverage. A correct unproved
bridge is proof work; a missing bridge target is a correspondence gap. See the
[stage responsibilities](../CONTRIBUTING.md#stage-responsibilities).

`dependencies` contains direct proof-planning hints. It is not a reading order,
a list of every concept in a statement, or an extracted Lean dependency graph.
Keep useful prerequisites without cycles or their transitive closure.
A listed hint's verification flag does not determine the node's flag. Lean's
actual use of an unfinished declaration does affect verification, even if that
declaration is not listed as a hint. Validation checks dependency references and
cycles.

Put local modules under `formal/Lemmatheca/` and import them from
`formal/Lemmatheca.lean`.
Put reusable definitions, theorem statements, proofs, and construction lemmas in
the general theory layer for its area, such as `Lemmatheca.SetTheory` or
`Lemmatheca.MathematicalLogic`. This applies even when
a declaration first appears in one entry or has only one current caller. Standard
constructions on particular carriers, such as rational enumeration or Dedekind
cuts, are still general theory.
Reserve `Lemmatheca.Entry.<EntryName>` for particular illustrative examples and
counterexamples with no wider mathematical use, plus their example-specific
helpers. An entry module must not hold general definitions, general edge cases,
or reusable steps of an argument. General modules must not import entry modules;
examples import the theory they illustrate. Keep related declarations together,
leave routine helpers private where possible, and remove empty entry modules.
Use the existing Lean project; do not introduce separate per-entry Lake projects.

## Build and verification

After editing Lean declarations or proofs, node bindings, or entry block mappings,
refresh verification from the repository root at delivery:

```sh
uv run python app/manage.py build
```

Follow the [shared check and batching rules](../CONTRIBUTING.md#validation-and-submission).
A multi-stage batch may defer this writing build until its final mutating stage;
step 4 still compiles targets and inspects their actual signatures before step 5.
Saved results describe the last successful build and do not certify edits made
while a refresh is deferred. Standalone handoffs include the required refresh.

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
never runs Lean or performs source-freshness checks on a page request. Refresh the
build results at delivery after the relevant edits. To compile locally
while working, `lake build` from `formal/` is useful, but it does not refresh corpus
JSON; finish with the Django build command.

The [CI workflow](../.github/workflows/ci.yml) validates the corpus, installs the
pinned environment, checks source availability, runs the tests and build, then checks that committed node results and entry
summaries match regenerated files. The tests exercise successful, unfinished,
unsupported-axiom, missing-declaration, and failed builds in an isolated Lean
project. They also check Choice used directly, through other declarations, or in
a type, and metadata edits during builds. `formal/.lake/` contains ignored local
dependencies and build output.

### Build warnings

Inspect the complete Lean and Lake output from the full build, including warnings.
A successful exit and refreshed verification flags do not establish that warnings
were resolved. Fix warning causes in project-owned Lean sources, using local proof
or style changes that preserve the intended statements, definitions, and permitted
axioms. Naming intentionally unused parameters with a leading underscore is
legitimate cleanup that preserves their hypotheses. Do not weaken the mathematics,
hide unfinished proofs, suppress diagnostics through local or global linter
settings, or change the pinned environment to remove diagnostics.

After warning fixes, rerun `uv run python app/manage.py build` from the repository
root and inspect the full output again. Local compilation is useful during repairs,
but the final full build checks the integrated project and refreshes generated data.
Report the warnings fixed and identify any remaining diagnostics by source location
and reason. Separate diagnostics originating in pinned Lean/mathlib dependencies
from project diagnostics; if dependency warnings cannot be fixed within the pinned
environment, report them rather than editing dependency caches or changing pins.

This does not require completing unrelated, deliberately unfinished declarations.
Their `sorry` warnings may remain outside the selected completion claim and must be
reported accurately. Unbound nodes and Not verified results are supported states;
do not invent bindings, change statements, or add axioms merely to quiet their
reports. Completed selected proofs must still meet the verification rules above.

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
