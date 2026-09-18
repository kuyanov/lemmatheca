# Verification and review

Lean checks a formal declaration. Maintainers judge whether it expresses the
intended human mathematics and whether the exposition is suitable for the library.
These are separate decisions. AI may propose translations and grades; it cannot
publish an entry.

## Allowed formalizations

A block can point to a declaration in the local `formal/Lemmatheca/` project or to
an existing declaration in the pinned mathlib dependency. Existing mathlib results
are accepted as formal bindings without rewriting their proofs. Definitions can
bind to existing definitions or instances. A question binds its answer or
counterexample, not an unchecked conjecture.

Each formalization records `status`, `declaration`, `source`, `verification_report`,
`module`, and `unformalized_dependencies`. Each pending dependency identifies a
local Lean statement by `declaration`, `module`, and `source`. Its proof may use
`sorry`; the reader links to the source, clearly marked incomplete. The list
belongs to its block. Already-proved mathlib lemmas are not pending
dependencies simply because they are external to the corpus. There is no global
external-lemma registry or individual exception-approval requirement for using
ordinary mathlib results.

`complete` requires an empty pending-dependency list, a complete binding, and a
passing report. Validation rejects a complete block with pending statements, even
when report checking is disabled for regeneration. `partial` permits
unfinished work and missing binding fields; `not_started` indicates no completed
formalization. The entry badge is derived from all block statuses. Neither a
complete badge nor a mathlib binding grants publication approval.

## Local check workflow

Run `uv run python app/manage.py check_formalizations`. The command:

1. Validates the metadata and source paths, allowing reports to be regenerated.
2. Runs `lake build` using the pinned Lean/mathlib environment, explicitly building
   pending modules as well as the main library.
3. Imports the bound modules and runs `#check` and `#print axioms` for complete
   declarations and pending dependencies.
4. For complete declarations, rejects axioms outside `propext`, `Classical.choice`,
   and `Quot.sound`, including direct or transitive use of `sorryAx`. Pending
   dependencies also permit `sorryAx`, so their statement types can be checked
   before proofs are available.
5. Writes local reports with bindings, axiom lists, content hashes, and environment
   pins. Pending dependencies appear in a separate `pending_dependencies` list,
   never among certified complete `declarations`. Incomplete blocks are not
   certified, and no status is automatically promoted.

The reader validates that complete declarations appear in a passing report; it
also checks that a complete mathlib binding's source is recorded in that report.
It does not require an installed mathlib checkout or execute Lean during page
requests. Missing local Lemmatheca files remain errors. The command is intended for trusted
repository content. A report should be regenerated when mathematical content,
bindings, or the environment changes.

`unformalized_dependencies` is an author-maintained account of missing work, not
a full dependency closure. Full dependency extraction remains future work, as does
checking that the submitted human argument follows the same proof strategy. In
particular, type agreement alone does not certify an exposition.

## Human review and later automation

A maintainer checks hypotheses, domains, quantifiers, the explanation, authorship,
license, source credit, and the formal binding. Finite sets must not silently turn
into infinite sets or misleading cardinality conventions. Conjectures remain
questions rather than accepted theorems.

Future submission handling should preserve submitted text and make suggested
changes visible. Formalization and grading workers operate outside public page
requests. Untrusted Lean code requires isolated workers with resource limits and
no access to secrets; public HTML requires sanitization and asset checks. The
current local command is not that public submission service.

Beauty grades should distinguish clarity, economy, conceptual insight, reuse, and
faithfulness to the submitted argument. Record reasons, not only a score. Human
and AI recommendations remain visible as recommendations. A selected maintainer
makes the final publication decision.

Git commits and content hashes identify what was reviewed and checked. There are
no entry/proof version counters in the metadata. After a change, rerun checks and
review the new content rather than carrying approval forward automatically.
