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
Consult [Source errors](../corpus/source-errors.md) if checking external cited
arguments. Save confirmed source defects and extensions of checked coverage using
the [maintenance contract](../docs/corpus.md#source-errors). Prioritize false
statements and failed deductions; missing explanation and valid compression are
not errors. Keep corpus-only binding problems in the review handoff. Source-error
register maintenance is this review's only permitted file edit.

## Work

1. Make a coverage table by block: human definitions and claims, covering node IDs,
   specialization or representation bridges, and gaps. Include examples, hidden
   answers, witnesses, prose claims, and relevant boundary cases. Explain empty
   mappings and distinguish them from unplanned blocks.
2. Compare each description with both its declaration and the human text. Inspect
   its rendered node page as well: mathematical notation must use `\(...\)` or
   `\[...\]` with JSON-escaped LaTeX. Flag raw variables, subscripts, function
   applications, quantifiers, relations, operations, fractions, decimals, tuples,
   intervals, or set braces left outside math delimiters, unmatched or nested
   delimiters, literal LaTeX, and KaTeX errors. Keep ordinary English words
   outside formulas; check for articles accidentally marked as variables
   and ASCII spellings rendered as products of letters instead of the intended
   Greek symbols or named operators. Follow the
   [node-description contract](../docs/formal.md#formal-nodes); valid JSON and
   Lean verification do not check this presentation.
   Inspect each ambiguous `a` in context, including records left untouched by a
   formatting pass. Check complete notation for indexed families (`\aleph_a`,
   `\beth_a`) and consistent symbols for specific named ordinals and cardinals.
   Read the descriptions in full rather than relying only on Unicode or token
   scans, and state the actual scope and limitations of the audit.
   Check hypotheses, quantifiers, logical directions, conclusions, and domains. Check
   existence as well as uniqueness, both laws for the same inverse, the surrounding
   set for complements, and codomains for surjectivity and composition. Inspect
   the order of quantifiers governing constructed witnesses: a transformation
   chosen once and valid for every background must precede that background's
   universal quantifier. A uniform proof of a weaker statement does not repair its
   signature. For a supplied map, require a checked identity with the constructed
   map, or a property stated directly of the supplied map. Check that descriptions
   and dependency hints were refreshed when a statement or proof changed.
   Inspect conventions involving total operations, subtypes, and cardinalities. A more
   general library result is a valid binding only when the specialization covers
   the human claim; record that specialization explicitly. For custom types,
   inspect elaborated expressions to check which order or other instance Lean
   actually selected, especially in comparisons involving concrete literals.
   If a proof introduces a separate formula syntax, inspect actual translations
   preserving satisfaction, scope, and required properties such as being
   quantifier-free. Require a theorem applying the bound definition to the actual
   shared-language theory. A correct local-syntax theorem beside an unused shared
   definition leaves a coverage gap. Check that completeness, elementarity, and
   definability consequences concern that same theory and syntax.
   For proof calculi, compare primitive constructors with the human rule list.
   A derived-rule claim needs an actual syntactic admissibility transformation,
   not a constructor granting the rule. If the proof representation includes
   extra rules, inspect its conservative translation into the stated basic system.
   Soundness of the enlarged system does not establish completeness of the basic
   one. Check that a completeness proof uses syntactic derivations where theory
   membership is required, rather than semantic equivalences justified only by
   the completeness result under construction.
   Choice is permitted by default. Check whether claims about weaker axiom systems
   or independence are actually encoded; a Verified badge does not establish them.
   Ordinary conclusions may be bound under default Choice even when the human proof
   uses only countable or dependent choice. Assess the weaker-assumption argument
   separately; do not require duplicate unbound nodes merely for those hypotheses.
   Logical-strength claims, including principle implications, first-order schemas,
   and axiom-system equivalences, still require a suitable encoding or an unbound node.
   A provable choice premise does not make an ordinary Lean theorem a check of
   restricted axiom strength, even if the proof uses it. When a binding is presented
   as certifying that strength, require an unbound logical claim instead and
   separately inspect construction lemmas with supplied data.
   Check module placement as well: reusable definitions and results belong in
   general theory, even if used by only one entry. `Entry/` should contain only
   particular illustrative examples and counterexamples with no wider use, and
   their example-specific helpers. General modules must not import entry modules.
   Distinguish definitions, explicit premises, and unconditional assertions of a
   principle. Report arguments exceeding their stated assumptions, missing logical
   prerequisites, and limits of coverage using the
   [assumption guidance](../CONTRIBUTING.md#prerequisites-and-scope).
3. Find opportunities to reuse nodes and library declarations, unnecessary wrappers,
   duplicate targets, redundant directions of equivalences, and repeated coverage.
   Explain why each proposed removal preserves the human claims. Do not discard
   an explicitly stated witness or distinct reformulation merely because it follows
   from other mathematics. Check whether each definition binding corresponds to
   a definition actually given in the text, including prose definitions. If it
   only exposes a formal representation or implementation helper, it may be
   dropped when the retained nodes cover the construction and stated claims.
   Bindings need not include the retained claims' dependencies or helper statements
   arising only in their proofs. Retain coverage of the stated definitions,
   claims, examples, answers, and explicit constructions or witnesses. Distinguish
   removing a block binding from deleting a node record or Lean declaration:
   useful nodes may still serve as dependency hints, and Lean helpers may still
   be needed by retained proofs.
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

Inspect the current entry, node records, and Lean declarations. Use focused Lean
checks when needed to resolve signature or representation questions. Run
`uv run python app/manage.py validate_corpus` only when investigating a structural
or binding-reference concern. No build or catalog test run is required for this
read-only audit.

## Deliverable

Return findings with concrete file/block/node references, their consequences, and
suggested changes, followed by the coverage table and checks performed. Distinguish
node-description formatting defects, incorrect bindings, missing coverage,
unstated representation bridges, and optional
simplifications. Explain any correspondence that needs renewed discussion after a
proposed statement or description change.

Keep this audit read-only: do not change bindings, descriptions, generated data, or
proofs, and do not run the writing build command. Review decisions belong in the
GitHub pull request; return findings here unless posting was explicitly requested.
Report saved source-error IDs and coverage changes when source checks were made,
or explicitly state that the register needs no changes for that inspected scope.
