# Step 5: Review correspondence

Follow the [single-step execution instructions](../CONTRIBUTING.md#running-one-step-with-an-ai-agent).
Complete this step using the supplied inputs and current repository files;
return its deliverable without starting the next stage.

Independently audit correspondence between a Lemmatheca entry and its formal
bindings. Check collective coverage and redundancy, not one-to-one matching.

## Inputs

- Entry ID (required): the existing entry whose formal bindings should be audited.
- Preparation report or review focus (optional): use it as context, while checking
  coverage independently against the current files.

## Context

Read the [project overview](../README.md), [corpus guide](../docs/corpus.md),
[formalization guide](../docs/formal.md), the full entry, linked node
records, and the actual Lean declarations. Inspect referenced definitions and
saved signatures alongside the sources. Saved verification describes the last
successful build; it is not a live freshness check or evidence of correspondence.

## Work

Inspect the earlier source-rigor assessment and any claimed repairs alongside the
source passages relevant to the audited claims. Report newly found source errors,
gaps, or unchecked arguments separately from binding errors, with precise locations
and consequences. A correct formal binding does not validate the source's proof.
Identify repairs needed before further affected drafting or formalization changes;
do not silently resolve them within this read-only audit.

1. Make a coverage table by block: human definitions and claims, covering node IDs,
   specialization or representation bridges, and gaps. Include examples, hidden
   answers, witnesses, prose claims, and relevant boundary cases. Explain empty
   mappings and distinguish them from unplanned blocks.
2. Compare each description with both its declaration and the human text. Check
   hypotheses, quantifiers, logical directions, conclusions, and domains. Check
   existence as well as uniqueness, both laws for the same inverse, the surrounding
   set for complements, and codomains for surjectivity and composition. Inspect
   conventions involving total operations, subtypes, and cardinalities. A more
   general library result is a valid binding only when the specialization covers
   the human claim; record that specialization explicitly. For custom types,
   inspect elaborated expressions to check which order or other instance Lean
   actually selected, especially in comparisons involving concrete literals.
3. Find opportunities to reuse nodes and library declarations, unnecessary wrappers,
   duplicate targets, redundant directions of equivalences, and repeated coverage.
   Explain why each proposed removal preserves the human claims. Do not discard
   an explicitly stated witness or distinct reformulation merely because it follows
   from other mathematics. Proof helpers need not all be registered nodes.
4. Review dependencies as proof-planning hints. Identify unnecessary edges, cycles,
   or useful missing hints without reconstructing mathlib's dependency graph. A
   hint's saved verification flag does not control the reviewed node's status;
   actual Lean use of an unfinished declaration is detected separately.
5. Check the full declaration name and defining module. There is one module field
   for both import and source browsing. Generated declarations may point to a
   differently named source origin; compare signatures rather than names alone.
   Small temporary Lean checks can clarify a representation bridge without editing
   tracked statements or proving pending production theorems.
6. Check that the saved entry-list summary agrees with the mappings and saved node
   results. If build output is missing or stale, report that it needs regeneration
   with app/manage.py build; do not infer fresh verification from old JSON.

## Checks

```sh
uv run python app/manage.py validate_corpus
```

This read-only check does not invoke Lean or refresh saved verification data.

## Deliverable

Return findings with concrete file/block/node references, their consequences, and
suggested changes, followed by the coverage table and checks performed. Distinguish
incorrect bindings, missing coverage, unstated representation bridges, and optional
simplifications. Explain any correspondence that needs renewed discussion after a
proposed statement or description change.
Include remaining source-rigor concerns and whether they were reported before the
affected drafting and formalization work.

Keep this audit read-only: do not change bindings, descriptions, generated data, or
proofs, and do not run the writing build command. Review decisions belong in the
GitHub pull request; return findings here unless posting was explicitly requested.
There are no approval records, hashes, or review dates to update in the app. Human
text and rendering still need their own review even when the Lean proof is verified.
