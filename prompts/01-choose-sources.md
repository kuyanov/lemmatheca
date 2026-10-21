# Step 1: Plan the area and choose sources

You are the root agent; execute this step yourself. Follow the
[area-pipeline protocol](../CONTRIBUTING.md#running-an-area-pipeline) and
[shared execution rules](../CONTRIBUTING.md#running-one-step-with-an-ai-agent).
Own the area-wide source plan, coverage assessment, entry scopes, prerequisites,
reading order and delegation. Do not draft entries during the planning phase.

## Inputs

- Specified area and the requested development scope.
- Optional batch size, proposed entries, source preferences, reading-time target,
  existing plan or review findings.
- Whether the request is planning-only or authorizes the entry-addition pipeline.
  Follow the user's scope; do not infer entry creation from a planning-only request.

## Context

Inspect the area's existing entries, reading order, nearby prerequisite coverage,
and relevant [planning records](../corpus/reference-planning/index.json). Use the
[scope](../CONTRIBUTING.md#prerequisites-and-scope),
[reading-order](../CONTRIBUTING.md#reading-order), and
[citation](../docs/corpus.md#entry-metadata) contracts. Reuse applicable source
assessments and handoffs instead of repeating unchanged audits.

Use the [authoring API](../docs/app.md#authoring-api) under the
[shared usage rules](../CONTRIBUTING.md#using-the-authoring-api) to list entries
with `area` and `fields=id,title,reading_position`. Add summaries when titles do
not establish scope. Search blocks with concept-specific `q` and
`include_answers=true` to distinguish existing coverage from gaps; inspect
shortlisted blocks with `block_ids` and `include=blocks,references`. Check relevant
cross-area prerequisites too. Look up source records by publication URL and
planning records by area, entry or kind, using the
[registry workflow](../docs/corpus.md#navigating-source-and-planning-records).
Inspect the selected publications directly; do not read whole registries.

## Work

1. Inventory the area's current human coverage and pending plans. Identify
   missing definitions, intermediate results and accessible elementary material
   in the sources that should precede more advanced topics. Distinguish an actual
   exposition gap from missing formal proofs or an optional further direction.
2. Select source passages for the proposed definitions, results, examples and
   proofs. Record editions, precise locations and access limits. Assess
   hypotheses, mathematical support and known source defects; establish repairs
   or alternatives where needed. Maintain the
   [source register](../docs/corpus.md#source-errors) for material actually
   inspected. Do not treat compressed valid proofs as source errors.
3. Choose coherent entries within the requested scope and size. Follow the
   [reading-time target](../docs/corpus.md#entry-metadata): normally about 30–40
   minutes, with up to about 50 for a cohesive topic when useful. Treat 50 as an
   allowance, not the default. Combine closely related material where it fits,
   without padding the entry count or compressing explanations to meet a number.
   Allow room to explain the substantive constructions and intermediate arguments
   the formalization will need; follow the
   [exposition and formalization rule](../docs/corpus.md#exposition-and-formalization)
   when choosing or revising entry boundaries.
   Include necessary in-scope prerequisite entries, or narrow/defer material
   needing substantial theory outside the authorized scope. State which proposals
   are for execution now and which belong to the later roadmap.
4. Build the prerequisite dependencies and reading order. Place elementary
   material before its uses and group related entries where dependencies permit.
   Name existing prerequisites by stable entry/block IDs and proposed prerequisites
   by entry ID and required result, without inventing unwritten block anchors.
   Check for cycles, forward prerequisites, redundant coverage, and assumptions
   imported from other areas.
5. Give each proposed entry a stable ID, plain-text title, scope and main results,
   outline, source-to-outline map and citation objects, reading-time estimate,
   prerequisites, and intended placement. Note known consuming blocks and related
   pending references; full entry-level integration discovery belongs to step 2.
   Assign file ownership to entry agents and identify the shared edits you will
   coordinate.
6. For an authorized entry-addition pipeline, spawn an entry agent for each entry
   in the execution plan with prompts 02–06 and its complete handoff. Schedule
   independent entries in parallel and dependency-bound work when its inputs
   exist. Entry owners request reviews for steps 3 and 5; assign or spawn their
   reviewers yourself under the independence rule. Plan index checkpoints before
   dependent agents need to discover earlier additions. Follow the central protocol for
   applying integration edits before review, shared ownership, final gap/order
   checks, and integrated verification.

## Checks

You own source support, prerequisite completeness, coverage gaps and reading order
under the [area protocol](../CONTRIBUTING.md#running-an-area-pipeline). Do not
hand off the planning decision or repeat formal node-reuse searches, which belong
to step 4.

Planning alone leaves entries, taxonomy, reading order and reference planning
unchanged. If source-register records changed in a planning-only task, finish with
`build --no-lean` under the
[shared build rules](../CONTRIBUTING.md#validation-and-submission). For a full
pipeline, combine that refresh with an index checkpoint you coordinate or the final
batch build. No routine rendering, Lean build or catalog tests are required for
the planning phase.

## Deliverable and continuation

Provide the area coverage/gap assessment, ordered entry plan and source maps,
prerequisite dependencies, inspected-source limits, execution/deferred scopes,
and per-entry assignments. For a planning-only request, stop here.

For an authorized pipeline, continue through delegation and shared integration
without a new permission request between stages. Before delivery, check the actual
added coverage and reading order, resolve in-scope gaps through the affected stages,
and complete the final build. Report deferred prerequisites and unavailable checks
honestly; do not present a roadmap or unverified worker handoff as completed entries.
