# Step 4: Prepare formal nodes

Follow the [single-step execution instructions](../CONTRIBUTING.md#running-one-step-with-an-ai-agent).
Complete this step using the supplied inputs and current repository files;
return its deliverable without starting the next stage.

Prepare formal bindings for the mathematical claims in a Lemmatheca entry,
without proving new theorems.

## Inputs

- Entry ID (required): the existing entry to formalize.
- Human-review findings or agreed revisions (optional): use the supplied report
  or referenced discussion. Without one, inspect the current entry and report
  mathematical ambiguities without claiming that it has been reviewed.

## Context

Read the [project overview](../README.md), [corpus guide](../docs/corpus.md),
[formalization guide](../docs/formal.md), and [contribution workflow](../CONTRIBUTING.md).
Inspect the full entry, `corpus/nodes/`, local Lean modules, and pinned library
sources. Use the single project in formal/ and preserve unrelated work.

## Work

1. Inventory definitions and claims in every block, including examples, question
   answers, witnesses, edge cases, and assertions embedded in prose. Make a
   block-to-claims-to-nodes map. Coverage is collective: multiple nodes may cover a
   block, and a node may serve multiple blocks. Do not create nodes for every
   sentence or routine proof step.
2. Search existing nodes, then Lean and pinned mathlib declarations, before writing
   local definitions or statements. Inspect signatures and relevant definition
   bodies. Consider specialization, symmetry, definitional equality, and standard
   predicates. Prefer direct bindings; avoid wrappers that merely rename, reverse,
   specialize, or bundle results already covering the text.
3. Explain representation changes and specializations. Check hypotheses, universes,
   subtypes, domains, codomains, and conventions such as total division or finite
   cardinality functions on infinite sets. Distinguish existence from uniqueness;
   ensure both inverse laws refer to the same map. Preserve the intended mathematics
   rather than adapting it silently to a convenient library declaration. Inspect
   elaborated comparisons and instances for custom types and concrete literals;
   a type annotation alone may not select the intended relation.
   Choice is permitted by default. For axiom-strength claims, identify the required
   logical encoding and missing prerequisites using the
   [assumption guidance](../CONTRIBUTING.md#prerequisites-and-scope). Report limits
   of coverage rather than binding such a claim to an ordinary Lean theorem with
   a different meaning. Leave the intended claim unbound when a classical
   declaration proves its principles or conclusion outright and does not encode
   the claimed implication over ZF. Keep faithful principle definitions bound and
   cover the actual constructions with supplied-data lemmas; do not add provable
   choice premises to library facts as a substitute for the missing logical encoding.
4. Remove redundant coverage while retaining explicitly stated witnesses and
   distinct claims. A linked equivalence may already cover its two directions.
   Bind the definitions actually given in the text and the stated mathematical
   claims, examples, and answers. A separate definition binding may be dropped
   when the text does not give that definition and the retained claims already
   cover the construction. This applies to formal representation and implementation
   helpers, not to definitions given in prose rather than a displayed formula.
   Do not expand a block's bindings to include its claims' dependencies: helper
   statements arising only in a proof need no separate block binding when the
   retained nodes cover the stated claims and any explicit construction or witness.
   Keep necessary Lean helpers; useful registered prerequisites may remain in
   dependency hints without direct block links. Reuse existing nodes across
   entries instead of duplicating them.
5. Implement missing definition bodies and declare missing theorem statements with
   `by sorry`. Do not replace existing proofs or prove new theorem bodies in this
   step. Put reusable mathematics under the general theory layer, currently
   `formal/Lemmatheca/SetTheory/`, even if introduced by or used in only one entry.
   This includes general definitions, theorem statements, edge cases, and
   construction lemmas; a standard construction on a particular carrier is still
   reusable mathematics. Reserve `Entry/` and `Lemmatheca.Entry.<EntryName>` for
   particular illustrative examples and counterexamples with no wider use, and
   their example-specific helpers. General modules must not import entry modules.
   Group related mathematics in coherent modules, remove empty example modules,
   and add imports to `formal/Lemmatheca.lean`. Keep environment pins fixed.
6. Create `corpus/nodes/<node-id>.json` using the current contract in [formalization guide](../docs/formal.md).
   Write a concise plain-text mathematical description with needed assumptions and
   quantifiers. Optional LaTeX must be escaped for JSON. Bind declaration to its full
   Lean name and module to its defining module, including Lean core modules where
   appropriate. An unbound planned node may have both fields null. New nodes start
   with `verified: false`.
   Do not add review fields, a separate source-module field,
   or invented verification signatures or line numbers.
7. Set dependencies to direct proof-planning hints, not reading prerequisites,
   concepts merely mentioned in a statement, or imported modules. Avoid cycles and
   transitive duplication. These hints do not determine verification; Lean checks
   actual transitive use independently, rejecting unfinished proofs and unsupported
   axioms. Validation checks dependency references and cycles.
8. Link the nodes using `data-formal` in `entry.html`. Use `data-formal=""` only for a
   block with nothing to formalize, and explain that decision. Leave genuinely
   unplanned blocks distinguishable from empty mappings. The build owns the derived
   formalization object in entry.json; do not write it manually.

## Checks

After changing node records, block mappings, or Lean declarations, run from the
repository root:

```sh
uv run python app/manage.py validate_corpus
uv run python app/manage.py build
```

Validation can also run during authoring without Lean or generated results.
The build checks all registered declarations, saves verified/signature/source-line
data, and refreshes entry summaries. A theorem using sorry is a valid unfinished
result, as is a proof depending on an unsupported axiom. The build continues
checking the other nodes; a missing declaration or compile error fails the build and preserves prior
results. Inspect the resulting signatures and defining source locations. A generated
target can point to a differently named source origin; judge its actual signature.
Run relevant catalog tests only if reader or build-tooling code changes, or when
investigating an integration failure.

## Deliverable

Return the coverage map, new/rebound/retired node IDs and targets, reasons for local
declarations, representation notes, proof-planning hints, and checks performed.
Include generated JSON changes and list questions for correspondence review on
GitHub. Do not claim that passing Lean checks establish correspondence or record
any approval in the corpus.
