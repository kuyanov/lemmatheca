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

A maintainer reviews proposed statements and coverage before proof work. An empty
mapping explicitly marks material that needs no formalization.
Run `review --accept --node <id> [<id> ...]` or
`review --accept --nodes-from-entry <id>` through `app/manage.py` to record statement approval.
The command saves a SHA-256 target hash and a recording timestamp in each selected
node. `--dry-run` previews the changes; repeated acceptance preserves current
records. `--nodes-from-entry` deduplicates linked nodes and rejects unplanned
blocks. It does not automatically accept unlinked dependencies or change entry status.
Maintainers retain the final inclusion decision.

Use `review --retract` with the same node selectors to withdraw approval.
It clears existing review records to `null` without running Lean or changing
verification evidence, even when checks are missing or stale. `--nodes-from-entry` retraction
skips unmapped blocks and leaves unlinked nodes alone. Shared nodes have one
review across all entries. `--dry-run` also works for retraction, and nodes
without an approval are skipped.

Entry review is a separate action: `review --accept --entry <id>` records that the
maintainer checked the text for errors, inspected its rendered presentation, and
confirmed that all blocks are covered without redundant nodes or missing claims.
It validates the corpus and requires explicit mappings on every block and a
declaration for every linked node; an empty mapping is allowed. These structural
checks cannot establish semantic coverage or visual correctness automatically.
The command stores `review: {sha256, recorded_at}` in `entry.json`; new entries use
`review: null`. Editorial status is derived, with no stored `status`: a matching
approval makes the entry `final`, removing the Draft badge and review note.
It never runs Lean or changes node reviews or verification.
Unfinished proofs, pending node approvals, and missing verification evidence are
allowed. `--retract --entry <id>` returns the entry to `draft`, even with unplanned
blocks or invalid HTML. Both entry actions support `--dry-run` and skip unchanged
approvals. Git records the history of these decisions.

Entry hash version 2 covers all metadata fields except `review`, the exact
`entry.html` bytes, and the relative paths and contents of every file under the
entry's `assets/`, plus a map from each directly linked node ID to its description.
Shared nodes are included once; unlinked nodes and proof prerequisites are excluded.
HTML includes the selected node IDs, so mapping edits invalidate
approval. JSON formatting and key order do not matter; HTML whitespace does.
Adding, removing, renaming, or editing an asset invalidates approval, as does
editing a linked description. Node declarations, modules, proof dependencies,
node approvals, Lean sources, reports, and environment pins are excluded. Shared
templates/styles, other entries, taxonomy, and reading order are also outside
this entry-owned content hash.

A mismatch displays Draft on the entry and area pages without rewriting the
saved approval. Reviewing and accepting the current content replaces the saved
hash and timestamp. Reverting content exactly restores a matching approval;
explicit retraction clears it, so reverting cannot restore a retracted approval.
All existing entries were drafts and migrated to `review: null`; no entry was
auto-approved. Any version-1 entry approval needs renewed review because it did
not cover linked descriptions; hashes are not upgraded automatically. Approval
writes also reject concurrent changes to entry files or linked descriptions.
See the [review workflow](../README.md#recording-reviews).

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

Stale or failed verification does not retract a recorded review. When the approval matches
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
| Entry text or `data-formal` mapping | Node approval retained; retract and repeat the separate entry review | Retained |

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
2. Groups all nodes by their declared import module, including Mathlib bindings.
   Each group records its transitive local
   source imports, the `Lemmatheca.ReviewChecks` exporter, pinned environment, and
   verification policy. Mathlib and the other Lake packages share one installed-revision
   fingerprint. Node fingerprints cover ID, declaration, and import module.
   Groups with current evidence for all their nodes are reused, preserving check dates.
   Reused groups still require clean installed Git dependencies, but need no import
   traversal or Lean process. For a stale group, the
   import walker still reads transitive library imports to collect local inputs;
   installed library files are represented by the shared revision fingerprint.
3. Runs `lake build` for each stale group's import module and the exporter, then
   checks that import separately with `#print axioms` for its registered declarations.
   A binding cannot rely on imports from another group's module.
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
flags can be combined. A registered `Mathlib.*` selector checks just that import;
`--module Mathlib` selects all registered Mathlib modules as independent groups.
Nodes with the same declared import share one group's outcome. Without selectors, every
stale verification group is checked. A failed group retains its last successful
snapshots for review history, while its verification is unavailable. Successful and reused groups are
saved; the command then exits with an error. Concurrent report writes are rejected
instead of overwriting another check's results.

With no node declarations, the command skips Lean. Axiom auditing is driven by
the node registry; the old fixed list of sumset checks has been removed. Archived
JSON bindings and `checks/sumsets.json` remain historical records outside this pipeline.

The [CI workflow](../.github/workflows/ci.yml) installs the pinned Lean environment,
builds the project, and runs `check_formalizations --force` on pushes, pull requests,
and manual runs. Its Lake cache retains dependencies and build artifacts, but
every registered declaration is checked again. Lean errors, missing declarations,
unapproved axioms, and invalid dependency checkouts fail the job. Pending proofs
and human reviews remain allowed; CI neither records approval nor commits reports.

The reader derives readiness from the node's current evidence and correspondence
review. For a reviewed declaration, a missing or stale report yields
`verification_needed`, never `complete` or a proof status from outdated evidence.
Binding changes invalidate the changed node's evidence. Local project source edits invalidate
the module and its transitive importers, including other declarations in those
modules; unrelated modules keep their evidence and dates. Adding or removing an
unimported module has no effect. Environment, exporter, or verification-policy
changes invalidate all affected module records. Descriptions, manual proof
dependencies, and review records do not invalidate Lean evidence. File hashes are
cached by file metadata; page requests never run Lean. `formalization/verification.py`
owns these checks and shares current input hashes within each freshness operation,
so modules with different saved versions of one input still compare against the
same current snapshot. The dependency requirement is part of that cache's key:
reader fallback for an absent checkout cannot satisfy a verification command.

Installed Lake packages must be clean Git checkouts. The shared library fingerprint
records package names and installed revisions. A Git status query per package
supplies the commit and checks staged, unstaged, untracked, and submodule changes;
ignored build output is allowed. This handles detached HEADs, branches, packed
refs, and linked worktrees without walking or hashing package sources in Python.
Dirty checkouts, source archives without Git metadata, and unreadable Git status
invalidate affected evidence and block verification, including cached reuse. The
checker identifies invalid packages and does not modify or clean their files.
Restore a clean checkout or commit intended dependency changes before retrying.
Changing a package revision, adding or removing a package, or changing the project's
manifest, toolchain, or Lake configuration invalidates affected evidence. Project
proofs may remain uncommitted. Local replacements of external module namespaces are
still content-hashed. Project files under `Lemmatheca/` retain per-module invalidation.

A web-only deployment can omit Lake dependencies: the committed report and pinned
environment are trusted when the dependency checkout is absent. With installed
packages, cleanliness and the revision fingerprint are checked; removal of some
packages needs rechecking. The verification command requires installed clean
dependencies even when reusing evidence; the absent-dependency fallback is only
for reading committed evidence. Policy version 6 requires checks under this rule;
older policy evidence must be regenerated. Node approval hashes are unchanged.
Missing local sources invalidate
their module and its importers without blocking unrelated nodes. A different file
resolving to the same imported module name also invalidates affected evidence.
The import scanner supports ordinary module imports and does not audit arbitrary
metaprogram file access or custom build steps. The command operates on trusted
repository content.

`review --accept --node` and `review --accept --nodes-from-entry` refresh the selected nodes' modules if their targets have no
current hashes. Unrelated failed modules do not block this refresh. Both review
actions validate every selected node before writing and check
for concurrent input changes. They stage records and replace each node file atomically. Existing
approvals are never silently updated by `check_formalizations`.

Report format 8 has a `modules` map containing each project and Mathlib import
module independently. Records contain `status`, `checked_on`,
`policy_sha256`, and a direct `sha256` map from input path to fingerprint. The special
`formal/.lake/packages` path represents the combined package revisions and local
library overrides; ordinary file inputs use content hashes. Each
record retains its own hashes, so refreshing one group cannot silently refresh
another group's stale evidence. Failed records also contain an `error`. If a prior
check succeeded, a failed record includes `last_success`: the original successful
module record, including its input hashes, policy, and check date. Existing node
snapshots remain paired with that successful record; the failed attempt's hashes
never certify them. Repeated failures replace the latest attempt and keep just one
successful record, without nesting failure history. A first failure has no
`last_success` and creates no node snapshots. A successful retry replaces the node
snapshots and removes the failure and saved historical module record.

The reader uses retained snapshots only for the historical review comparison;
failed groups expose neither current target hashes nor current verification.
Description and binding edits still prevent matching old approvals. The checker
always retries failed groups, even if their last successful inputs match again.
Format-7 shared Mathlib records migrate to separate import records with the
original input hashes, check dates, node snapshots, and any `last_success` history.
The reader adapts these records without writing; the checker persists format 8.
Migration does not invent successful checks: a failed shared audit remains failed
in each resulting module until that module passes a new check. Node fingerprints
prevent a changed or newly added binding from using another binding's evidence.
The full original input set is retained conservatively until a fresh check records
the individual module's import closure. Current successful evidence can be reused;
node approval hashes and review dates are unchanged.
The report uses ordinary JSON, with no input table or numeric references.
The reader ignores unsupported report formats, including the former indexed
format, until the checker regenerates evidence. Individual installed-library file
hashes are no longer report inputs.
The `nodes` map retains each declaration's axiom results, signature, source location,
and `declaration_sha256`. The API exposes the dynamically computed `target_sha256`
and the verification group's check date. Node bindings and source locations retain
their exact `Mathlib.*` module names. Formats older than 7 need regeneration with
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
cases, and redundant nodes. `review --accept --entry` records this decision through
the entry's content hash, independently of node approval and proof completion.
Entry and linked-description edits invalidate it automatically. Declaration
changes belong to node review and do not invalidate entry approval. Changes to
unlinked descriptions also leave it intact.

The next useful improvement is a separate per-block coverage record, bound to the
reviewed mathematical text, selected node IDs, and descriptions. Text, mapping,
or description edits could then flag only the affected block instead of the entire
entry. Figure and table content, question answers,
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
require a separate entry review; the node hash does not certify unchanged human prose.
