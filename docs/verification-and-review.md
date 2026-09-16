# Verification, dependencies, and editorial review

## What “checked by Lean” means

Lean's kernel checks formal proof terms against formal propositions. This does not
automatically establish that the proposition matches the human statement, that
the proof follows the human argument, or that every mathematical dependency has
an explanatory proof in Lemmatheca. Treat these as separate checks.

Use a clean build with pinned Lean/mathlib versions and inspect each exported
declaration's transitive axioms. A successful build is insufficient: Lean can
accept declarations containing `sorry`. The official
[proof validation guide](https://lean-lang.org/doc/reference/latest/ValidatingProofs/)
explains axiom inspection and additional checking options.

Suggested initial axiom policy: permit only `propext`, `Classical.choice`, and
`Quot.sound`, while recording which are actually used. Reject `sorryAx`, custom
axioms, and native-evaluation/compiler-trust axioms. Kernel-checked computational
proofs are welcome; compiler-trusting proof paths are outside the initial policy.
Implement this as an exact allowlist for the pinned version, not a search for
particular axiom-name substrings. See Lean's
[axiom reference](https://lean-lang.org/doc/reference/latest/Axioms/).

Group laws supplied as hypotheses of a group structure are not new global axioms.
Likewise, a theorem can have assumptions such as finiteness or nonemptiness.
Those assumptions must match the displayed human statement; an extra hypothesis
asserting the desired conclusion would make a formal proof useless for this task.

## Four dependency categories

| Category | Treatment |
| --- | --- |
| Logical foundations | Lean kernel rules and the explicit permitted axiom set |
| Elementary mathematical infrastructure | A small, versioned allowlist of exact declarations in `foundations.json` |
| Internal mathematics | Accepted definitions/statements/proofs at pinned revisions, with audited dependencies |
| External nontrivial results | Separate records in `external-lemmas.json`; never silently treated as elementary |

“Elementary” is a project policy, not a label inferred from a short proof or an AI
opinion. Start with logic, equality, basic natural-number arithmetic, elementary
set/finite-set operations, and the laws defining the structures in use. Before
publication, replace those informal families with reviewed declaration names,
source versions, and hashes. Do not whitelist whole namespaces such as `Nat` or
entire mathlib modules.

Reusing mathlib's definitions avoids rebuilding its algebraic and analytic
infrastructure. Reusing a nontrivial theorem still requires either an internal
proof or a declared external dependency. Definitions and typeclass instances can
hide proof dependencies too; their names alone are not permission to skip auditing.

Default publication target: a **strict core** with no external nontrivial lemmas.
If broader coverage requires an exception, a human maintainer explicitly approves
the external record and its uses. Such entries carry a visible **external
dependencies** label and are excluded from strict-only API queries. An empty
external registry means no exceptions have been authorized, not that an audit has
already proved the library self-contained.

An external record includes a stable ID, human statement and hypotheses, upstream
URL and immutable revision, Lean declaration, verification/axiom status, why it is
external, approving maintainer/decision, and an eventual internal replacement.
Compute reverse dependents rather than maintaining their list by hand.

Distinguish an externally authored **Lean-checked theorem** from an
**unformalized mathematical claim**. The latter may be catalogued as a reference
or a future task, but cannot enter an accepted proof as an unchecked custom axiom
under the initial policy. Even an approved external Lean theorem must pass the
foundational axiom policy.

## Dependency extraction

`#print axioms` does not enumerate all nontrivial lemmas. Build a separate Lean
auditor that traverses declaration types and proof/value expressions, including
implicit arguments, instances, generated helper declarations, and opaque theorem
bodies available in the pinned environment. Expand dependencies transitively with
cycle detection/memoization; record provenance for every referenced constant.
Handle inductives, constructors, and recursors explicitly.

Classify leaves against exact foundation, internal, and external manifests. Report
unknown declarations and fail the publication gate until they are classified.
Keep the full closure available even where the human report collapses it behind
an approved foundational item. A foundational item's approval covers its reviewed
closure at that version; the independent axiom check still traverses all of it.

Do not derive trust from imports alone, a source-text scan, or the submitter's
own dependency list. Tactics can discover theorems the author did not name, and
a copied helper can conceal an external dependency. Narrow imports and explicit
tactics help reproducibility but are not the final enforcement mechanism.

For a strict proof, verify that no selected internal dependency leads transitively
to an external theorem. Reject logical dependency cycles at the revision level.
The current submission cannot be used as its own approved premise under a new
name. A pre-existing upstream proof of the same result counts as an external
dependency, not an independent formalization of the proposed argument.

Every verification artifact binds the exact source, statement and proof revisions,
dependency lock, assets relevant to the argument, policy version, and auditor
version. An upgrade creates a new verification run; historical results keep their
original environment. Changes to an assumption trigger review of reverse dependents.

## Translation workflow

```text
draft → submitted → formalizing → verifying → awaiting_review
                                                    ├→ changes_requested → new revision
                                                    ├→ rejected
                                                    └→ approved → published
```

Track job state separately: a timeout, exhausted budget, or translation failure
does not mean the mathematical statement is false. It returns diagnostics and
leaves the submission available for revision or manual formalization. Successful
AI work never changes the editorial state to `approved`.

1. Save immutable human text, explicit hypotheses, figures, and attribution.
2. Identify an existing statement for an alternate proof, or propose a new formal
   statement. Flag ambiguous notation and missing assumptions for human resolution.
3. Retrieve definitions and already accepted prerequisites from a frozen release.
4. Generate Lean source and a mapping from the human steps to formal steps.
5. Compile and repair within an explicit attempt, time, token, and cost budget.
6. Independently verify the candidate and generate the axiom/dependency report.
7. Collect editorial grades and present the exact candidate to a maintainer.
8. Publish only the exact approved revision through the trusted publisher.

The formalizer must not silently strengthen hypotheses, weaken a conclusion, or
replace a submitted combinatorial argument with a different algebraic proof.
Proposed changes require an explicit new human-visible revision. The author can
also submit Lean directly; it goes through the same verification and review gates.

## Safe execution and authority

Lean source, tactic code, macros, build files, and model output are executable or
untrusted input. Build candidates in a separate unprivileged sandbox with no
network, credentials, host mounts, or publication capability; enforce CPU, memory,
disk, process-count, output-size, and wall-clock limits. Use a trusted fixed build
configuration and dependency image rather than executing a submitted Lake file.
For public arbitrary-code submissions, use a hardened sandbox/VM boundary rather
than assuming a default container alone is sufficient isolation.

Generate acceptance reports outside the candidate's writable workspace using
trusted tooling. For production, evaluate Lean's documented independent/rechecking
tools on the pinned release. A candidate's stdout saying “verified” is not a
certificate. AI grading workers also cannot edit roles, decisions, or trust policy.

Only an explicitly selected human maintainer account may approve a revision or
authorize an external exception. Enforce this in server-side permissions and the
publication service. Separate an AI identity from a human account even if both
write reviews. Ordinary contributors can submit but cannot grant themselves a
maintainer role. Log role changes and final decisions.

## Grading beauty

Correctness, statement alignment, argument alignment, and dependency compliance are
publication gates. Grade mathematical exposition and argument quality separately,
on a 1–5 scale with an explanation and concrete passages supporting each grade.

| Dimension | What a high grade means |
| --- | --- |
| Insight | The proof exposes the mechanism behind the result |
| Economy | Few essential ideas and no unnecessary machinery; gaps do not count as brevity |
| Clarity | Explicit hypotheses, readable notation, and understandable transitions |
| Naturalness | The method fits the statement and the intended audience's prerequisites |

Use shared anchors: 1 = major weakness, 3 = sound ordinary exposition, 5 = exceptional
on that dimension. Allow “not assessable” with a reason. Require the grader to
state the intended audience. A short Lean script is not evidence of mathematical
beauty; it may merely call a powerful external theorem. Grade formal code readability
and maintainability separately from the human proof if useful.

Both internal AI judges and selected human maintainers may grade. Store every
grade independently with reviewer type, rubric version, rationale, and target
revision. For AI, also store model/version and prompt configuration. Show human
and AI assessments separately; disagreements remain visible. Avoid a single
leaderboard score initially, and do not impose an automatic beauty threshold.

A maintainer may accept an essential ordinary lemma with a modest beauty grade,
feature an elegant alternate proof, ask for clarification, or reject a checked
but unsuitable submission. AI recommendations never cast a binding vote.
