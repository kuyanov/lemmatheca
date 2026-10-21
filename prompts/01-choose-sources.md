# Step 1: Plan the area and choose sources

You are the root agent; execute this step yourself. Own the area plan and source
selection. Do not draft entries, prepare formal nodes, or perform later-stage
reviews. Follow the [shared execution rules](../CONTRIBUTING.md#running-one-step-with-an-ai-agent).

## Inputs

- Specified area and authorized development scope.
- Optional batch size, proposed topics, source preferences, reading-time target,
  existing plan or review findings.
- Whether the request is planning-only or authorizes entry creation.

## Context

Inspect the taxonomy description, existing human coverage, reading order, nearby
prerequisites and relevant pending plans. Apply the
[scope](../CONTRIBUTING.md#prerequisites-and-scope),
[area-fit and continuity](../CONTRIBUTING.md#area-fit-and-continuity), and
[reading-order](../CONTRIBUTING.md#reading-order) policies.

Use the [authoring API](../CONTRIBUTING.md#using-the-authoring-api) to list entries
with `area` and `fields=id,title,reading_position`; add summaries where needed.
Search blocks with concept-specific `q` and `include_answers=true`, then inspect
shortlisted blocks with `block_ids` and `include=blocks,references`. Check relevant
cross-area coverage too. Select source records by publication URL and planning
records by area, entry or kind through the
[registry workflow](../docs/corpus.md#navigating-source-and-planning-records).
Reuse applicable assessments; inspect selected publications directly.

## Work

1. Inventory the area's level, notation, main questions, thematic groups and
   coverage. Ground the plan in those existing entries and explain any change in
   direction. Identify missing definitions, intermediate results and accessible
   source material that should precede advanced topics. Distinguish exposition
   gaps from unfinished formal proofs and optional extensions.
2. Select passages supporting each proposed definition, result, example and
   proof. Record editions, precise locations, hypotheses and access limits.
   Resolve known source defects with checked repairs or alternative sources;
   maintain the source register for material actually inspected.
3. Choose coherent entry scopes and perspectives. Explain each entry's area fit
   and connection to the existing sequence. Allow useful treatments of the same
   topic from different areas, distinguishing their pedagogical contribution
   from newly covered mathematics. Follow the
   [reading-time target](../docs/corpus.md#entry-metadata):
   normally 30–40 minutes, with up to about 50 for a cohesive topic. Allow room for
   the substantive constructions formalization will need under the
   [exposition and formalization rule](../docs/corpus.md#exposition-and-formalization);
   split or narrow compressed material rather than preserving an arbitrary entry count.
4. Establish prerequisites and reading order. Put elementary material before its
   uses and group related topics where dependencies allow. Cite existing
   prerequisites by stable entry/block IDs; identify proposed prerequisites by
   entry ID and required result, without inventing block anchors. Check cycles,
   forward prerequisites, unnecessary repetition and cross-area assumptions.
   Narrow or defer material needing substantial theory outside the authorized
   scope. Separate the execution batch from the deferred roadmap.
5. Prepare each entry's handoff: stable ID, plain-text title, scope, main results,
   outline, source-to-outline map and citation objects, reading-time estimate,
   prerequisites, placement and intended perspective. Identify owned files and
   shared integration work. Note known consumers and pending references; leave
   full reference-integration discovery to step 2 and node-reuse searches to step 4.

## Checks and deliverable

Check the plan's area continuity, source support, prerequisite completeness,
coverage gaps and reading order. Return the ordered plan and per-entry handoffs,
including justified overlap, inspected-source limits and unresolved/deferred work.
No entry rendering, Lean work or catalog tests belong to this step. Any
source-register edits follow the shared publication rules.

A planning-only request ends here. For authorized entry creation, continue under
[Running an area pipeline](../CONTRIBUTING.md#running-an-area-pipeline); delegation,
review scheduling, index checkpoints and final integration belong to that driver
protocol, not to the planning work above.
