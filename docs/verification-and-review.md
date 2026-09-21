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
one local or mathlib declaration, its module, dependencies, and a `review`
record (or `null`). Definitions can bind to definitions or instances. A question binds its
answer or counterexample. The [formal README](../formal/README.md#formal-nodes)
specifies the schema; entry JSON contains no formal metadata.

A maintainer reviews proposed statements and coverage before proof work. Committing
HTML mappings records coverage approval, including an empty mapping for material
that needs no formalization. Run `review --accept --node <id> [<id> ...]` or
`review --accept --entry <id>` through `app/manage.py` to record statement approval.
The command saves a SHA-256 target hash and a recording timestamp in each selected
node. `--dry-run` previews the changes; repeated acceptance preserves current
records. Whole-entry acceptance deduplicates linked nodes and rejects unplanned
blocks. It does not automatically accept unlinked dependencies or publish an entry.
Maintainers retain the final inclusion decision.

Use `review --retract` with the same node or entry selectors to withdraw approval.
It clears existing review records to `null` without running Lean or changing
verification evidence, even when checks are missing or stale. Entry retraction
skips unmapped blocks and leaves unlinked nodes alone. Shared nodes have one
review across all entries. `--dry-run` also works for retraction, and nodes
without an approval are skipped.

Review hashes cover elaborated theorem types, definition bodies, inductive
constructors and recursor rules, and their reachable constants. Theorems contribute
their statements, not their proofs, even when referenced by a definition. Expression
metadata and binder names are omitted. Node metadata and the pinned environment
also enter the hash. Changing a statement or a referenced definition invalidates
review after rechecking; proof-only edits can retain it. This is a structural hash,
not a test of mathematical equivalence. Proving agents must still preserve approved
targets rather than silently reaccepting their own changes.

A node without a declaration shows **Declaration missing**; an unreviewed
declaration shows **Pending review**. A recorded review with stale evidence shows
**Verification needed** until a recheck can compare the target hash. A mismatch
then shows **Review outdated**, which remains until the new target is reviewed
and accepted. Recording a review does not invalidate Lean evidence. Approval alone
cannot complete a node with a `sorry` proof or pending dependencies: these show
**Proof pending** or **Dependencies pending**. The badge displays this status without
repeating it as reason text; the API exposes the same distinct status codes.

## Local check workflow

Run `uv run python app/manage.py check_formalizations`. The command:

1. Loads the formal node registry independently of the human corpus and validates
   IDs, module paths, dependency targets, and acyclicity.
2. Fingerprints node metadata except `review`, local Lemmatheca sources, imported dependency sources,
   and the pinned environment, then runs `lake build` for registered modules.
3. Imports these modules and runs `#print axioms` for each registered declaration.
4. Allows `propext`, `Classical.choice`, and `Quot.sound` for complete proofs.
   Direct or transitive `sorryAx` means pending; other axioms fail the run.
5. Exports structural review snapshots independently of theorem proof terms,
   hashes each target's reachable declarations and pinned context, and rejects
   missing snapshot data rather than accepting an incomplete hash.
6. Rejects inputs changed during the run and atomically writes
   `formal/checks/nodes.json`, recording evidence for complete and pending proofs,
   and Lean's declaration source locations when available. The reader uses these
   locations only with current evidence. Source links follow the defining module,
   which may differ from the node's import module. Imported mathlib/local sources
   must be fingerprinted; bundled Lean sources use the pinned toolchain version.
   This also supplies line links for anonymous instances without running Lean on page requests.

With no node declarations, the command skips Lean. Axiom auditing is driven by
the node registry; the old fixed list of sumset checks has been removed. Archived
JSON bindings and `checks/sumsets.json` remain historical records outside this pipeline.

The reader derives readiness from current evidence, statement review, and ready
node dependencies. For a reviewed declaration, a missing or stale report yields
`verification_needed`, never `complete` or a proof status from outdated evidence.
Node metadata other than `review`, source, dependency, or environment changes invalidate affected
evidence. All local Lean sources are checked conservatively, so an unrelated
local edit can invalidate several nodes. File hashes are cached by file metadata;
page requests never run Lean.

A web-only deployment can omit Lake dependencies: the committed report and pinned
environment are trusted when external files are absent; installed dependency
sources are compared with their recorded hashes. Local Lean sources must exist.
The import scanner supports ordinary module imports and does not audit arbitrary
metaprogram file access or custom build steps. The command operates on trusted
repository content.

`review --accept` refreshes verification if the selected targets have no current
hashes. Both review actions validate every selected node before writing and check
for concurrent input changes. They stage records and replace each node file atomically. Existing
approvals are never silently updated by `check_formalizations`. The migration from
boolean flags recorded hashes for the 30 nodes approved at that time and left the
other 91 unreviewed; its timestamps record migration time, not original review dates.

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

Git commits and target hashes identify what was reviewed and checked. There are
no entry/proof version counters in the metadata. After changing mathematical
content, rerun checks and review changed targets. Human text and mapping coverage
still require Git review; the node hash does not certify unchanged human prose.
