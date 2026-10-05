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
   Check whether claims of provability in a weaker axiom system or independence
   are actually encoded. A verified ambient theorem, even with a choice premise,
   is not evidence of the claimed axiom strength. Report missing logical
   prerequisites or limits of coverage using the
   [assumption guidance](../CONTRIBUTING.md#prerequisites-and-scope).
   Check the required node `axioms` array against the current convention:
   every node permits ambient AC via `["choice"]`. Human assumptions, including
   entry-wide ZF-only claims and explicit choice-principle premises, need separate
   review; a Verified ambient theorem does not certify weaker axiom strength.
   Review definitions and explicit premises separately from unconditional assertions
   of a principle. Use read-only `#node_status`
   checks for transitive kernel-axiom reports when assessing axiom strength.
   Distinguish actual selection from classical logic or
   representation dependencies; neither a pass nor a failure proves ZF derivability.
3. Find opportunities to reuse nodes and library declarations, unnecessary wrappers,
   duplicate targets, redundant directions of equivalences, and repeated coverage.
   Explain why each proposed removal preserves the human claims. Do not discard
   an explicitly stated witness or distinct reformulation merely because it follows
   from other mathematics. Proof helpers need not all be registered nodes.
4. Review dependencies as proof-planning hints. Identify unnecessary edges, cycles,
   or useful missing hints without reconstructing mathlib's dependency graph. A
   hint's saved verification flag does not control the reviewed node's status;
   actual Lean use of an unfinished declaration is detected separately. Review
   dependency allowances: each source node must include every axiom declared by
   its direct prerequisites. Mismatches fail validation and prevent build writes.
   A broader allowance does not establish actual use or mathematical necessity.
   Flag an argument that needs a stronger result than its assumptions permit;
   preserve the current ambient-AC convention and report weaker axiom-strength
   claims that remain outside formal coverage.
5. Check the full declaration name and defining module. There is one module field
   for both import and source browsing. Generated declarations may point to a
   differently named source origin; compare signatures rather than names alone.
   Small temporary Lean checks can clarify a representation bridge without editing
   tracked statements or proving pending production theorems.
6. Check that the saved entry-list summary agrees with the mappings and saved node
   results. If build output is missing or stale, report that it needs regeneration
   with app/manage.py build; do not infer fresh verification from old JSON.

## Checks

Inspect the current entry, node records, and Lean declarations. Use focused Lean
checks when needed to resolve signature or representation questions. Run
`uv run python app/manage.py validate_corpus` only when investigating a structural
or binding-reference concern. No build or catalog test run is required for this
read-only audit.

## Deliverable

Return findings with concrete file/block/node references, their consequences, and
suggested changes, followed by the coverage table and checks performed. Distinguish
incorrect bindings, missing coverage, unstated representation bridges, and optional
simplifications. Explain any correspondence that needs renewed discussion after a
proposed statement or description change.

Keep this audit read-only: do not change bindings, descriptions, generated data, or
proofs, and do not run the writing build command. Review decisions belong in the
GitHub pull request; return findings here unless posting was explicitly requested.
There are no approval records, hashes, or review dates to update in the app. Human
text and rendering still need their own review even when the Lean proof is verified.
