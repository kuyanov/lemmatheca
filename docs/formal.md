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
do not check formula rendering. Formatting-only description changes require the
writing `build --no-lean` and a rendering check; commit changed generated files,
including `corpus/index.json`. Follow the
[batching rules](../CONTRIBUTING.md#validation-and-submission); unchanged bindings
and proofs do not need a Lean rebuild.
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
these results or source locations. Verification fields may be absent before a
build; a missing `verified` value is treated as false. Generated declarations may point to a source
origin with a different name; compare the exported signature with the actual target.
The reader uses local project, Lake dependency, and Elan toolchain sources for its
source browser and line links.

## Bindings and proof planning

Inspect existing nodes and the pinned library before introducing declarations.
Prefer direct bindings to existing definitions or theorems, including suitable
specializations and equivalent formulations. Avoid wrappers whose only purpose is
to rename, reverse, or bundle existing results. Explain representation changes in
the review handoff, and check domains, quantifiers, conventions, and assumptions.
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

## Module layout

Put mathematical modules in the owning entry's directory under
`formal/Lemmatheca/`, converting its ID to PascalCase: `arithmetic-theories`
owns `Lemmatheca/ArithmeticTheories/`. An entry may have several modules; import
them through `formal/Lemmatheca.lean`. Use the existing Lake project. Build
infrastructure such as `Lemmatheca/ProofStatus.lean` stays outside entry directories.

Module paths describe ownership; reusable declarations' namespaces describe
mathematical areas. For example, the module
`Lemmatheca.ArithmeticTheories.ArithmeticTheories`
defines declarations under `Lemmatheca.ModelTheory.ArithmeticTheories`. Keep
area-based namespaces such as `Lemmatheca.SetTheory`,
`Lemmatheca.MathematicalLogic`, `Lemmatheca.ModelTheory`,
`Lemmatheca.ComputabilityTheory`, and `Lemmatheca.ProofTheory`. Moving an entry to
another area changes namespaces and node declaration bindings as needed, without
moving its directory. Update imports and node module bindings when files move.

Reusable definitions, proofs and construction lemmas also have one owning entry;
other entries import those modules rather than duplicating code or creating a
parallel area directory. Place foundational definitions and lemmas with the entry
that first explains and uses them. Audit imports and node bindings that point to a
later owner in the same area's reading order: remove unnecessary imports, or
extract the earlier prerequisite from a mixed module instead of moving the whole
module. Code ownership follows the mathematical exposition; a broad import alone
does not establish ownership. Keep later construction and integration results
with their own entries. When reducing a module's imports, give its consumers
explicit imports for dependencies they previously received indirectly.

Within an area's declaration namespace, use coherent topic subnamespaces for
reusable code, such as `Lemmatheca.MathematicalLogic.Propositional`, rather than
putting generic names such as `eval`, `subst`, or `Derives` directly at the area
root. Related entries may share a topic namespace independently of file ownership.
Give local instances explicit names unique to their module when sharing a namespace.

Keep particular illustrative examples and counterexamples
in `Examples.lean` or another clearly named example module within the same entry
directory. Illustrative declarations may use `Lemmatheca.Entry.<EntryName>`
namespaces independently of their file paths. Reusable modules must not depend
on illustrative examples; examples import the mathematics they illustrate.
A construction's first appearance or sole
current caller does not make it an illustrative example. Keep related declarations
together, leave routine helpers private where possible, and remove empty modules.

## Build and verification

See the [build guide](build.md) for stages, outputs and flags, and the
[contribution rules](../CONTRIBUTING.md#validation-and-submission) for batching checks.
The default `uv run python app/manage.py build` validates canonical inputs, builds
`Lemmatheca` and bound non-core modules, then checks each declaration with
`formal/Lemmatheca/ProofStatus.lean`. Core modules come from the pinned toolchain.
The checker inspects transitive kernel axioms, including dependencies in types
and definitions. Only `propext`, `Classical.choice`, and `Quot.sound` are permitted.
Direct or inherited `sorryAx` or custom axioms produce `verified: false`.
Definitions follow the same rule; a comment containing “sorry” has no effect.

A successful build can include unfinished or unsupported proofs: their nodes
remain Not verified while other nodes are checked. Missing declarations, invalid
bindings and compilation failures fail the command. Inspect the actual results
and full diagnostics before claiming proof completion.

Include changed generated node/entry JSON, catalogs and `corpus/index.json` with
the sources. `build --no-lean` reuses saved proof results; it does
not certify changed declarations or bindings. Reader requests never run Lean or
establish source freshness.

Focused `lake env lean` or `lake build` checks are useful while editing, but do not
refresh corpus metadata. Finish formal changes with the full integrated build.
Step 4 still elaborates prepared targets before independent correspondence review,
even when the writing build is deferred to the end of a multi-stage batch.
In an [area pipeline](../CONTRIBUTING.md#running-an-area-pipeline), entry agents use
focused checks and report proofs ready for integration; the root completes step 6
with the final full build after their edits are frozen. Root-owned intermediate
index checkpoints may expose new nodes to other agents, but reuse saved proof
results and are not fresh Lean verification.
The [CI workflow](../.github/workflows/ci.yml) runs an early structural check,
tests and the combined `build --check --check-sources` verification.

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

Reviews of human exposition and formal correspondence are independent stages,
reported in the task discussion or a pull request. Verification checks the Lean
declaration; it does not prove that the description or entry says the same thing.
Review the mathematical text, block coverage, and description-to-declaration
correspondence separately. Post reviews to GitHub only when requested.

Use the [contribution workflow](../CONTRIBUTING.md). Preserve the intended
statement and definitions while replacing unfinished proofs. Use unregistered
helpers for routine proof steps; add a node only when it represents useful
mathematical coverage. Keep proof-search or translation logs outside corpus
metadata, and distinguish library reuse from translating a particular human proof.
