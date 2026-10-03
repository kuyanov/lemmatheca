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

Before adding formalizations, inspect the source-rigor assessment and relevant
source passages supporting the entry. If the assessment is missing, incomplete,
or no longer applies to the current scope, check the needed passages for rigorous
statements and arguments, including nontrivial omissions and cited prerequisites.
Report source errors, gaps, and unchecked arguments in the task discussion
**before creating or changing formal definitions, theorem statements, nodes, or
bindings**. Give precise source locations, affected claims, consequences, and
proposed repairs. Do not silently inherit or repair a gap; establish a checked
repair or supporting argument before formalizing the affected claim. Leave
unresolved affected work distinguishably unplanned and continue independent work
where possible. An applicable earlier report need not be repeated. A library
theorem or successful Lean check does not certify the rigor of the source argument.

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
4. Remove redundant coverage while retaining explicitly stated witnesses and
   distinct claims. A linked equivalence may already cover its two directions.
   Proof helpers need not become registered nodes. Reuse existing nodes across
   entries instead of duplicating them.
5. Implement missing definition bodies and declare missing theorem statements with
   `by sorry`. Do not replace existing proofs or prove new theorem bodies in this
   step. Put local modules under `formal/Lemmatheca/`, use appropriate namespaces,
   and add their imports to `formal/Lemmatheca.lean`. Group related mathematics in
   coherent modules. Keep environment pins fixed.
6. Create `corpus/nodes/<node-id>.json` using the current contract in [formalization guide](../docs/formal.md).
   Write a concise plain-text mathematical description with needed assumptions and
   quantifiers. Optional LaTeX must be escaped for JSON. Bind declaration to its full
   Lean name and module to its defining module, including Lean core modules where
   appropriate. An unbound planned node may have both fields null. New nodes start
   with `verified: false`. Do not add review fields, a separate source-module field,
   or invented verification signatures or line numbers.
7. Set dependencies to direct proof-planning hints, not reading prerequisites,
   concepts merely mentioned in a statement, or imported modules. Avoid cycles and
   transitive duplication. These hints do not determine verification; Lean checks
   actual transitive axioms independently.
8. Link the nodes using `data-formal` in `entry.html`. Use `data-formal=""` only for a
   block with nothing to formalize, and explain that decision. Leave genuinely
   unplanned blocks distinguishable from empty mappings. The build owns the derived
   formalization object in entry.json; do not write it manually.

## Checks

Run from the repository root:

```sh
uv run python app/manage.py validate_corpus
uv run python app/manage.py build
uv run python app/manage.py test catalog
```

Validation can also run during authoring without Lean or generated results.
The build checks all registered declarations, saves verified/signature/source-line
data, and refreshes entry summaries. A theorem using sorry is a valid unfinished
result; a missing declaration or compile error fails the build and preserves prior
results. Inspect the resulting signatures and defining source locations. A generated
target can point to a differently named source origin; judge its actual signature.

## Deliverable

Return the coverage map, new/rebound/retired node IDs and targets, reasons for local
declarations, representation notes, proof-planning hints, and checks performed.
Include generated JSON changes and list questions for correspondence review on
GitHub. Do not claim that passing Lean checks establish correspondence or record
any approval in the corpus.
Include the source-rigor findings reported before formalization, checked repairs,
and unresolved gaps or unchecked material, identifying affected unplanned work.
