# Lean formalization

**Node dependencies are used only for proving.** A node's `dependencies` list is a
manual plan of proof prerequisites, used to order proof work. Add a dependency
because the proof needs it, not merely because a
definition appears in the statement or a reader should learn it first. Keep direct,
useful prerequisites rather than copying their transitive closure. Entry HTML owns
human references and `data-formal` coverage; Lean imports resolve declarations.
The list is not a complete extracted proof graph, and the axiom audit detects
transitive `sorry` independently of these edges.
Changing this list does not affect node completion, correspondence approval, or
Lean evidence. A reviewed node with a verified proof is complete even if a listed
prerequisite is unfinished or unreviewed. Actual use of an unfinished proof is
detected through transitive `sorryAx` and leaves the node's own proof pending.

**Review establishes correspondence, not proof completion.** Lean can prove a
correct declaration that says something different from the human text. Reviewers
compare the node description with the actual declaration, then check that the
entry's linked nodes collectively cover its claims. Node approval tracks the first
comparison; entry text and coverage remain a separate Git review.

Lean **4.34.0** and mathlib **v4.34.0** are pinned by `lean-toolchain`,
`lakefile.toml`, and `lake-manifest.json`. Keep these fixed during an experiment.
The root [pipeline](../README.md#submission-and-formalization-pipeline) links the
reusable `.txt` prompts for adding and reviewing entries.

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

Each `nodes/<id>.json` contains a mathematical description, a declaration,
its proof prerequisites, and human review.

Use stable IDs describing the mathematics, such as `set-insert-commute`,
independently of the entries that reference them.

```json
{
  "id": "set",
  "description": "A set of elements of an ambient type is represented by a predicate on that type.",
  "declaration": "Set",
  "module": "Mathlib.Data.Set.Defs",
  "dependencies": [],
  "review": null
}
```

`description` is required, nonempty plain text. State the theorem with its
hypotheses, or describe the object being defined; include the relevant domains and
quantifiers. Keep it concise and understandable without opening an entry. For a
generic library target, explain a useful specialization when the node ID suggests
a concrete example. Avoid proofs, implementation commentary, HTML, and duplicated
entry paragraphs. Mathematical notation supports `\(...\)` and `\[...\]`;
escape backslashes in JSON, for example `"For every set \\(A\\), \\(A\\cup\\varnothing=A\\)."`.

The description appears first on the node page, followed by the checked Lean
signature. Review/check dates sit alongside it, proof dependencies expand to show
compact node links with adjacent statuses, and the source file stays collapsed
until opened. A source line link opens the file and scrolls to that line. The layout
adapts to narrow screens; the API returns the same description as plain text.

Descriptions are human statements, not Lean-checked text. They are included in
correspondence review hashes: any description edit, including a wording correction,
requires renewed approval immediately. It preserves the current Lean evidence.
The node ID, module, environment pins, and proof-planning dependencies are excluded from
review hashes.
Moving an unchanged declaration between modules requires a recheck but retains its
approval when its Lean name and meaning are unchanged. Changing the statement or
a referenced definition requires both a recheck and renewed approval.

Search the existing node registry and pinned Lean/mathlib sources before adding
local declarations. Reuse an existing node when possible; otherwise bind directly
to a library declaration when specialization or a straightforward reformulation
covers the human claim. Avoid wrappers that only rename a theorem, reverse an
equality, or bundle existing results. Record the correspondence for review.

Local modules live in `Lemmatheca/`; existing Lean and mathlib declarations are also
valid targets. The node's module specifies a `Lemmatheca.*` or `Mathlib.*` import
exposing that target. Current verification can locate the declaration
in a different source module, including Lean's bundled `Init`, `Lean`, and `Std`
sources. The reader uses the pinned Elan toolchain's installed source when available,
or a link to that Lean version on GitHub. Before a declaration exists, both
`declaration` and `module` may be `null`, with `review: null`.

Node pages also show the declaration signature exported by Lean during verification.
For generated declarations, the source origin can name a different declaration:
for example, `Even.zero` is generated from `IsSquare.one` by `to_additive`.
The checked signature shows the actual target even when it has no handwritten
source declaration. Stale verification hides that signature until rechecking.

Reusable set and map definitions and theorems use the namespace
`Lemmatheca.SetTheory` and live in `Lemmatheca/SetTheory/Basic.lean`.
`Lemmatheca/SetTheory.lean` imports the reusable theory modules. Each formalized entry
has one source file under `Lemmatheca/Entry/`; its examples use the corresponding
`Lemmatheca.Entry.<EntryName>` namespace.

```text
Lemmatheca/
  ReviewChecks.lean
  SetTheory.lean
  SetTheory/
    Basic.lean
    EquivalenceRelations.lean
  Entry/
    SetsAndMaps.lean
    EquivalenceRelations.lean
```

`Entry/SetsAndMaps.lean` groups sets and elements, set operations, and map examples
in sections. It imports `SetTheory.Basic` and its mathlib prerequisites.
Import `Lemmatheca.SetTheory` for all reusable set theory,
`Lemmatheca.SetTheory.Basic` for the basic sets-and-maps declarations, or
`Lemmatheca.Entry.SetsAndMaps` for those declarations and the first entry's examples.

The sets-and-maps entry has bindings for every mathematical block, including
examples and question answers. The notation-and-conventions block has an empty
mapping. Its 127 nodes have passing Lean verification: 85 bind directly to mathlib
or Lean declarations, 9 to the general theory, and 33 to entry-specific declarations.
The [mathlib binding audit](../docs/mathlib-binding-audit.md) records direct
replacements, splits of bundled claims, and changes to examples and dependencies.
New or changed nodes require explicit review; verification does not accept them.
These modules contain no `sorry`
placeholders. Ambient types (or subtypes) specify each universe,
domain, and codomain. In the formula question, the reciprocal is specified by
`x * y = 1`, since Lean's division itself is total even at zero.

The equivalence-relations entry has bindings for all 15 blocks, reusing ten nodes
and adding 61: 41 direct Lean/mathlib bindings and 20 local theorems.
All 71 linked nodes have current approvals and passing verification. Six reusable
theorems live in
`Lemmatheca/SetTheory/EquivalenceRelations.lean`, under `Lemmatheca.SetTheory`;
fourteen examples live in `Lemmatheca/Entry/EquivalenceRelations.lean`, under
`Lemmatheca.Entry.EquivalenceRelations`. The root module imports both entries.
Import `Lemmatheca.SetTheory.EquivalenceRelations` for the reusable additions alone.
The [binding preparation record](../docs/equivalence-relations-bindings.md) lists
coverage, target declarations, representation bridges, and proof prerequisites.
In particular, `Setoid.classes` represents the quotient as a set of subsets,
while the library equivalence to `Quotient` connects this with the type used for
maps. Both equivalence-relations modules are free of `sorry` placeholders.

The active registry has 188 nodes, all currently approved and verified. Ordered sets
has 19 human blocks with no formal bindings yet. Historical additive-combinatorics
sources and reports are separate from this registry.

After inspecting the declarations and their correspondence to the human text,
record your review from the repository root:

```sh
uv run python app/manage.py review --accept --node set-intersection
uv run python app/manage.py review --accept --node set-union set-complement
uv run python app/manage.py review --accept --entry sets-and-maps --dry-run
uv run python app/manage.py review --accept --entry sets-and-maps
```

`--accept --entry` accepts each distinct linked node once; it rejects blocks without
formal mappings. Empty mappings are allowed. Dependencies not linked from that
entry are not automatically accepted. This records description/declaration approval, not
editorial publication or proof completion. Shared nodes keep one shared review.

Acceptance refreshes Lean checks when needed, allows `sorry`, and writes a record
instead of a boolean:

```json
"review": {
  "sha256": "<64 lowercase hexadecimal characters>",
  "recorded_at": "<ISO timestamp with timezone>"
}
```

The SHA-256 covers the description, declaration name, elaborated target,
referenced definitions and inductive constructors. The node ID, pinned environment,
theorem proofs, import module, manual proof dependencies, source comments, and
positions are excluded; definition bodies are included. These referenced Lean
definitions determine the statement's meaning and are distinct from the manual
`dependencies` list. A changed statement or relevant definition makes an existing
review outdated after rechecking. A proof-only edit requires fresh verification but
keeps an unchanged statement's approval. Hashes compare structural declarations,
not arbitrary mathematical equivalence.

Environment pins remain part of verification fingerprints. Changing the Lean or
mathlib environment requires fresh checks and declaration hashes. If the reviewed
target is unchanged, approval is retained without reacceptance; if an upgraded
definition or elaborated statement changes its hash, review is required again.

Renaming a node ID preserves correspondence approval. Rename its JSON file to match
and update `data-formal` mappings and other nodes' dependency lists. Run
`check_formalizations` to refresh the report under the new ID; an unchanged target
retains the existing review record and timestamp. Renaming a Lean declaration is
different: declaration names remain part of the structural semantic hash.

Review hash version 3 excludes node IDs. Current version-2 approvals were converted
by matching their full old hashes against checked targets, preserving timestamps
and leaving other records untouched. Approvals predating descriptions still need
explicit renewal; verification never accepts or migrates reviews automatically.
Report format 4 stores declaration hashes
separately and combines them with current descriptions when loading nodes. See the
[review architecture](../docs/verification-and-review.md) for details and limitations.

To withdraw approval, use the same selectors with `--retract`:

```sh
uv run python app/manage.py review --retract --node set-intersection
uv run python app/manage.py review --retract --entry sets-and-maps --dry-run
uv run python app/manage.py review --retract --entry sets-and-maps
```

Retraction sets existing review records to `null`, leaving other node metadata
and verification evidence intact. It does not run Lean and works with missing or
stale verification and outdated approvals. Whole-entry retraction clears each
distinct linked node once, skipping unmapped blocks; unlinked nodes retain their
reviews. Retracting a shared node affects every entry using it. Nodes without a
review are skipped.

Exactly one of `--accept` and `--retract` is required. Both support `--dry-run`,
which previews changes without editing node records; acceptance can still refresh
the verification report. Reaccepting a current review is a no-op,
including its timestamp. To accept a changed target, inspect it and run the same
command again. Completion also requires passing evidence for the node's own proof.

| Derived status | Meaning |
| --- | --- |
| `declaration_missing` | No declaration assigned |
| `review_pending` | Statement needs human approval |
| `verification_needed` | No valid check for the current declaration |
| `review_outdated` | The checked target differs from the accepted hash |
| `proof_pending` | A current check found direct or transitive `sorry` |
| `complete` | Correspondence is approved and the node has a verified proof |

The first applicable row determines the node badge and API status. Entry HTML
links to nodes with [`data-formal`](../corpus/README.md#block-to-node-mapping).

## Checking nodes

From the repository root:

```sh
uv run python app/manage.py check_formalizations
```

The command builds registered modules, checks declarations and transitive axioms,
exports review snapshots through `Lemmatheca.ReviewChecks`, and writes
`checks/nodes.json` with semantic declaration hashes and source locations. Only `propext`, `Classical.choice`, and `Quot.sound`
are allowed in complete proofs; `sorryAx` remains unfinished.

The registry determines which declarations receive an axiom audit. `lake build`
compiles the library; `check_formalizations` records the evidence used by the reader.
The historical sumset report is retained separately from the active node checks.

Rerun after changing bindings, Lean sources, or environment pins.
Descriptions, manual proof dependencies, and review records do not invalidate evidence. Lean checks
correctness; maintainers check correspondence with the human mathematics. See
[verification and review](../docs/verification-and-review.md) for evidence rules
and [experiment design](../docs/formalization-experiments.md) for measured runs.
