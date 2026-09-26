# Verification and review

Lean checks a formal declaration. Maintainers judge whether it expresses the
intended human mathematics and whether the exposition is suitable for the library.
These are separate decisions. A proof can compile while establishing the wrong
claim: for example, the prose could promise a unique solution while the declaration
only asserts existence. Correspondence review catches that mismatch; proof
verification alone cannot. AI may propose translations and grades; it cannot
publish an entry.

The current phase focuses on formalization experiments and standard-corpus
construction. Review and inclusion are manual repository work. Drafts are visible
in the reader; there is no account-based publication control or automated AI
grading service. Those public features are deferred.

## Nodes and human review

A block optionally links formal nodes through HTML `data-formal`. A node names
one local or mathlib declaration, a mathematical `description`, its module,
proof dependencies, and a `review`
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
metadata and binder names are omitted. The declaration name and exact
description text also enter the hash. The node ID, pinned environment, import module,
and manual `dependencies` list do not. A referenced Lean definition affects
the meaning of the statement; a manually listed proof prerequisite does not.

The report stores the semantic declaration hash separately from node review.
The reader combines current descriptions with current checked declaration hashes,
so even a description-only edit invalidates approval immediately without running
Lean. The stored approval remains available for comparison; it is never silently
updated. This is a structural hash, not a test of mathematical equivalence.
Proving agents must preserve approved targets rather than reaccepting their own
changes.

Stale verification does not retract a recorded review. When the approval matches
the current description and the last checked declaration, the node page retains
**Reviewed on …**, alongside **Not verified**. A stale check does not imply that
the statement changed: proof edits alone also require fresh verification.
The API's `review_matches_last_check` exposes this historical comparison;
`review_current` remains false and `target_sha256` remains unavailable until a fresh
check. Historical approval cannot complete a node or be used to accept a new target.
Description and binding edits still stop matching immediately; a changed statement
or referenced definition is detected when Lean exports the new semantic hash.

| Change | Correspondence approval | Lean evidence |
| --- | --- | --- |
| Node description, even a wording edit | Needs renewed approval immediately | Retained |
| Theorem statement or reachable definition body | Needs renewed approval after rechecking | Needs rechecking |
| Theorem proof only | Retained if the target is unchanged after rechecking | Needs rechecking |
| Node ID rename, same description and declaration | Retained after refreshing the report under the new ID | Needs refreshing under the new ID |
| Module move, same Lean name and semantic graph | Retained after rechecking | Needs rechecking |
| Manual proof dependencies | Retained; node completion is unchanged | Retained |
| Review record | Changes approval | Retained |
| Pinned environment | Retained if the target is unchanged after rechecking | Needs rechecking |
| Entry text or `data-formal` mapping | Requires separate coverage review through Git | Retained |

Environment pins remain in verification fingerprints. After an environment change,
Lean must verify the declarations again and export fresh semantic hashes. Approval
is retained when those hashes are unchanged. An upgrade that changes a statement
or referenced definition still requires renewed review. Renaming a declaration or
making a mathematically equivalent reformulation can also change this structural
hash; unchanged mathematical meaning does not guarantee an unchanged hash.

A node without a declaration shows **Declaration missing**; an unreviewed
declaration shows **Pending review**. A recorded review with stale evidence shows
**Verification needed** until a recheck can compare the target hash. A mismatch
then shows **Review outdated**, which remains until the new target is reviewed
and accepted. Recording a review does not invalidate Lean evidence. Approval alone
cannot complete a node with direct or transitive `sorry`: it shows **Proof pending**.
Manual proof dependencies do not gate completion; an unfinished or unreviewed
listed prerequisite does not block a node whose own review and proof are complete.
The badge displays this status without
repeating it as reason text; the API exposes the same distinct status codes.

## Local check workflow

Run `uv run python app/manage.py check_formalizations`. The command:

1. Loads the formal node registry independently of the human corpus and validates
   IDs, module paths, dependency targets, and acyclicity.
2. Groups project nodes by their import module and all direct Mathlib bindings
   under one `Mathlib` audit. Each group records its transitive local
   source imports, the `Lemmatheca.ReviewChecks` exporter, pinned environment, and
   verification policy. Mathlib and the other Lake packages share one installed-revision
   fingerprint. Node fingerprints cover ID, declaration, and import module.
   Groups with current evidence for all their nodes are reused, preserving check dates.
   Reused groups need no import traversal or Lean process. For a stale group, the
   import walker still reads transitive library imports to collect local inputs;
   installed library files are represented by the shared revision fingerprint.
3. Runs `lake build` for each stale group's import modules and the exporter, then
   checks each declared import separately with `#print axioms` for its registered
   declarations. The shared Mathlib record does not permit a binding to rely on
   imports from another binding's module.
4. Allows `propext`, `Classical.choice`, and `Quot.sound` for complete proofs.
   Direct or transitive `sorryAx` means pending; other axioms fail that group's check.
5. Exports structural review snapshots independently of theorem proof terms,
   hashes each target's reachable declarations, and rejects
   missing snapshot data rather than accepting an incomplete hash.
6. Rejects inputs or group membership changed during that group's check and atomically writes
   `formal/checks/nodes.json`, recording evidence for complete and pending proofs,
   semantic declaration hashes, and Lean's declaration source locations when
   available. The reader uses these
   locations only with current evidence. Source links follow the defining module,
   which may differ from the node's import module. Imported mathlib/local sources
   must be fingerprinted; bundled Lean sources use the pinned toolchain version.
   This also supplies line links for anonymous instances without running Lean on page requests.

Use `--module Lemmatheca.Entry.SetsAndMaps` to select registered import modules
(multiple names are allowed), or `--force` to recheck even current modules. The
flags can be combined. `--module Mathlib`, or any registered `Mathlib.*` module,
selects the shared audit of all direct library bindings. Without selectors, every
stale verification group is checked. A failed group loses its usable evidence,
but successful and reused groups are
saved; the command then exits with an error. Concurrent report writes are rejected
instead of overwriting another check's results.

With no node declarations, the command skips Lean. Axiom auditing is driven by
the node registry; the old fixed list of sumset checks has been removed. Archived
JSON bindings and `checks/sumsets.json` remain historical records outside this pipeline.

The reader derives readiness from the node's current evidence and correspondence
review. For a reviewed declaration, a missing or stale report yields
`verification_needed`, never `complete` or a proof status from outdated evidence.
Binding changes invalidate the changed node's evidence. Local project source edits invalidate
the module and its transitive importers, including other declarations in those
modules; unrelated modules keep their evidence and dates. Adding or removing an
unimported module has no effect. Environment, exporter, or verification-policy
changes invalidate all affected module records. Descriptions, manual proof
dependencies, and review records do not invalidate Lean evidence. File hashes are
cached by file metadata; page requests never run Lean.

Installed Lake packages are assumed immutable. The shared library fingerprint
records package names and installed Git revisions, without scanning source trees,
hashing library contents, or checking for uncommitted edits. Lake's usual detached
HEADs are read directly; Git resolves branches, packed refs, and linked worktrees.
Source archives without Git metadata are trusted to match their manifest pins.
Changing a package revision, adding or removing a package, or changing the project's
manifest, toolchain, or Lake configuration invalidates affected evidence. Local edits
inside installed packages are deliberately outside this check; keep reusable local
changes in project sources. Local replacements of external module namespaces are
still content-hashed. Project files under `Lemmatheca/` retain per-module invalidation.

A web-only deployment can omit Lake dependencies: the committed report and pinned
environment are trusted when the dependency checkout is absent. With installed
packages, the revision fingerprint is compared; removal of some packages needs
rechecking. Individual library-file edits or removals are not detected. An unreadable
installed Git revision invalidates evidence and blocks fresh verification.
Missing local sources invalidate
their module and its importers without blocking unrelated nodes. A different file
resolving to the same imported module name also invalidates affected evidence.
The import scanner supports ordinary module imports and does not audit arbitrary
metaprogram file access or custom build steps. The command operates on trusted
repository content.

`review --accept` refreshes the selected nodes' modules if their targets have no
current hashes. Unrelated failed modules do not block this refresh. Both review
actions validate every selected node before writing and check
for concurrent input changes. They stage records and replace each node file atomically. Existing
approvals are never silently updated by `check_formalizations`.

Report format 7 has a `modules` map containing each project import module and one
`Mathlib` record for direct library bindings. Records contain `status`, `checked_on`,
`policy_sha256`, and a direct `sha256` map from input path to fingerprint. The special
`formal/.lake/packages` path represents the combined package revisions and local
library overrides; ordinary file inputs use content hashes. Each
record retains its own hashes, so refreshing one group cannot silently refresh
another group's stale evidence. Failed records also contain an `error`.
The report uses ordinary JSON, with no input table or numeric references.
The reader ignores unsupported report formats, including the former indexed
format, until the checker regenerates evidence. Individual installed-library file
hashes are no longer report inputs.
The `nodes` map retains each declaration's axiom results, signature, source location,
and `declaration_sha256`. The API exposes the dynamically computed `target_sha256`
and the verification group's check date. Node bindings and source locations retain
their exact `Mathlib.*` module names. Older report formats need regeneration with
`check_formalizations`. Verification-policy and report-format versions are separate;
regenerating evidence does not accept reviews. Existing approvals are retained when
their targets are unchanged.
Review hash version 3 still excludes node IDs. At its migration, current
version-2 approvals were converted only when their full hashes matched the current
description and checked declaration; their timestamps were preserved. Outdated and
unreviewed records were left untouched. Approvals from before descriptions entered
the hash still require explicit renewal: they cannot approve text outside their scope.

To rename a node, update its `id`, JSON filename, `data-formal` mappings, and proof
dependency references. Preserve its review record and run `check_formalizations`:
verification reports remain indexed and fingerprinted by node ID, but an unchanged
description and declaration retain the same review target. A Lean declaration
rename can change its structural hash and still requires renewed review.

Node dependencies are explicitly maintained; Lean axiom checking catches
transitive `sorry` even if an edge was not recorded. Full mathematical dependency
extraction, proof-strategy correspondence, and novelty checks are separate work.
A successful check does not itself establish that a human block is fully covered.

## Remaining correspondence gaps

Node approval checks **description ↔ Lean declaration**. Coverage review checks
**entry claims ↔ linked node descriptions**, including specializations, omitted
cases, and redundant nodes. `review --accept --entry` currently selects and accepts
nodes; it does not create an independently tracked coverage approval. Editing an
entry can therefore break correspondence while all its node approvals remain
current. Coverage is still reviewed through Git.

The next useful improvement is a separate per-block coverage record, bound to the
reviewed mathematical text and selected node review targets. Text edits, changed
mappings, or changed node targets would flag that block for review without revoking
shared node approvals in other entries. Figure and table content, question answers,
and surrounding assumptions must be considered when defining the reviewed scope.

Readable approval snapshots would also help: retain the approved description and
checked signature, then show their diff and which referenced definitions changed.
A hash detects a mismatch but does not explain it. These coverage records and diff
views are proposed improvements, not part of the current approval command.

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
