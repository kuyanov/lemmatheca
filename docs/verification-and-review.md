# Verification and review

Lean checks a formal declaration. Maintainers judge whether it expresses the
intended human mathematics and whether the exposition is suitable for the library.
These are separate decisions. AI may propose translations and grades; it cannot
publish an entry.

The current phase focuses on formalization experiments and standard-corpus
construction. Review and inclusion are manual repository work. Drafts are visible
in the reader; there is no account-based publication control or automated AI
grading service. Those public features are deferred.

## Nodes and human review

A block optionally links formal nodes through HTML `data-formal`. A node names
one local or mathlib declaration, its module, dependencies, and a `reviewed`
flag. Definitions can bind to definitions or instances. A question binds its
answer or counterexample. The [formal README](../formal/README.md#formal-nodes)
specifies the schema; entry JSON contains no formal metadata.

A maintainer reviews proposed statements and coverage before proof work. Committing
HTML mappings records coverage approval, including an empty mapping for material
that needs no formalization. `reviewed: true` records statement approval; clear it
when changing the target's assumptions or conclusion. This is a manual convention,
not an automatic target-locking system. Future proving agents must not silently
change approved targets. Maintainers retain the final inclusion decision.

A node without a declaration shows **Declaration missing**; an unreviewed
declaration shows **Pending review**. Changing `reviewed` takes effect
on the next page load and does not invalidate Lean evidence. Approval alone cannot
complete a node with missing or stale evidence, a `sorry` proof, or pending
dependencies. Its status becomes **Verification needed**, **Proof pending**, or
**Dependencies pending**, respectively. The badge displays this status without
repeating it as reason text; the API exposes the same distinct status codes.

## Local check workflow

Run `uv run python app/manage.py check_formalizations`. The command:

1. Loads the formal node registry independently of the human corpus and validates
   IDs, module paths, dependency targets, and acyclicity.
2. Fingerprints node metadata except `reviewed`, local Lemmatheca sources, imported dependency sources,
   and the pinned environment, then runs `lake build` for registered modules.
3. Imports these modules and runs `#check` and `#print axioms` for declarations.
4. Allows `propext`, `Classical.choice`, and `Quot.sound` for complete proofs.
   Direct or transitive `sorryAx` means pending; other axioms fail the run.
5. Rejects inputs changed during the run and atomically writes
   `formal/checks/nodes.json`, recording evidence for complete and pending proofs.

With no node declarations, the command skips Lean. Old archived JSON bindings
and `checks/sumsets.json` are not part of the new registry.

The reader derives readiness from current evidence, statement review, and ready
node dependencies. For a reviewed declaration, a missing or stale report yields
`verification_needed`, never `complete` or a proof status from outdated evidence.
Node metadata other than `reviewed`, source, dependency, or environment changes invalidate affected
evidence. All local Lean sources are checked conservatively, so an unrelated
local edit can invalidate several nodes. File hashes are cached by file metadata;
page requests never run Lean.

A web-only deployment can omit Lake dependencies: the committed report and pinned
environment are trusted when external files are absent; installed dependency
sources are compared with their recorded hashes. Local Lean sources must exist.
The import scanner supports ordinary module imports and does not audit arbitrary
metaprogram file access or custom build steps. The command operates on trusted
repository content.

Node dependencies are explicitly maintained; Lean axiom checking catches
transitive `sorry` even if an edge was not recorded. Full mathematical dependency
extraction, proof-strategy correspondence, and novelty checks are separate work.
A successful check does not itself establish that a human block is fully covered.

## Experiment outcomes

Measure statement correctness, Lean proof completion, and faithfulness to the
human argument independently. Existing mathlib bindings are valid for corpus
curation, even when the upstream proof uses another method. They do not by
themselves count as successful translation of the displayed proof.

Before a measured attempt, fix the input, environment, allowed prerequisites,
retrieval policy, and cost/repair limits. Keep all attempts and human interventions
in separate run records; current verification reports do not record them. Review
the elaborated statement against the intended mathematics before counting a proof
as a success. The [experiment plan](formalization-experiments.md) describes the
proposed pilot and metrics; no experiment runner is implemented yet.

## Human review and later public automation

A maintainer checks hypotheses, domains, quantifiers, the explanation, authorship,
license, source credit, and the formal binding. Finite sets must not silently turn
into infinite sets or misleading cardinality conventions. Conjectures remain
questions rather than accepted theorems.

Future submission handling should preserve submitted text and make suggested
changes visible. Future formalization and grading workers should operate outside public page
requests. Untrusted Lean code requires isolated workers with resource limits and
no access to secrets; public HTML requires sanitization and asset checks. The
current local command is not that public submission service.

Formal beauty grading is deferred; initial reviews should give actionable feedback
on correctness, clarity, and proof correspondence. Later grades can distinguish
clarity, economy, conceptual insight, reuse, and
faithfulness to the submitted argument. Record reasons, not only a score. Human
and AI recommendations remain visible as recommendations. A selected maintainer
makes the final publication decision.

Git commits and content hashes identify what was reviewed and checked. There are
no entry/proof version counters in the metadata. After changing mathematical
content, rerun checks and review the new content rather than carrying approval
forward automatically.
