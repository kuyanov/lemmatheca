# Content and machine access

An entry is a reading unit containing definitions, lemmas, theorems, questions,
proofs, and explanations. Each mathematical block is addressed by
`(entry_id, block_id)`. The [authoring guide](entry-sources.md) defines the file
contract.

Entry JSON contains identity, `based_on` citations, subject memberships, editorial
status, reading time, summary, and abstract. HTML owns block IDs, titles, kinds,
order, links, and optional `data-formal` mappings. There are no JSON block records
or duplicated references. Git supplies history; model attempts and costs belong
in separate experiment records.

## Numbering and navigation

Blocks are numbered separately by kind within an entry. These display numbers
are never identifiers. Source references use `href="entry-id#block-id"` across entries
and `href="#block-id"` within an entry. The catalog resolves stable entry IDs and
the renderer generates reader URLs; neither area paths nor file paths belong in
entry references. Reclassifying an entry requires no reference edits.

Links preserve non-empty source text and inline formatting.
Empty or whitespace-only links use a generated label: the block kind and number
for local references, the target heading for cross-entry references, and the figure
or table number for local figure/table references. Prefer empty same-entry links for automatic
numbering and explicit cross-entry text that fits the sentence. References return
to the citing block, reopening an answer when needed.
Equations, figures, and tables have separate numbering within each entry. Figures
and tables each have one caption, with a generated label; referenced elements need
stable IDs. Tables and images belong to the human source; assets stay inside the
entry folder.

Categories form a browsing hierarchy; reading order is explicit by primary area.
Only `corpus/entries/` and the working taxonomy are live inputs. Archived examples
and `taxonomy_complete.json` are reference material. Entry paths do not encode
categories.

## Formal nodes and progress

Formal records live in `formal/nodes/<id>.json` and Lean modules in
`formal/Lemmatheca/` or pinned mathlib. Each node names at most one declaration;
blocks can link multiple nodes, and nodes can be shared. Each node also has a
required plain-text mathematical description, with optional LaTeX notation, for
reviewing its statement or definition. A node without a
declaration is an unreviewed placeholder. See the [schema](../formal/README.md#formal-nodes).

| Mapping | Block status |
| --- | --- |
| Missing `data-formal` | Not started; planning needed |
| Empty `data-formal=""` | Not applicable |
| Nonempty list | Complete if every node is ready; otherwise a percentage |

A node is ready only with current correspondence approval and valid verification
evidence of a complete proof. Other nodes have explicit statuses for missing
declarations, review, verification, or unfinished proofs. Manually listed proof
dependencies do not affect completion. Missing proofs, including transitive
`sorry`, cannot count as ready. Definitions can use existing
Lean definitions; questions map their answers or counterexamples.

Entry badges show Not started when every block is unmapped, and Partial when
some blocks are unmapped but others have mappings (including empty ones). Once
every block has a mapping, the badge shows the percentage of distinct linked
nodes that are ready, including 0% and 100%. Shared nodes count only once;
not-applicable blocks add no nodes, and an all-not-applicable entry displays N/A.
Adding nodes can lower the percentage. These percentages count nodes, not proof
difficulty or effort, and depend on the current block mappings for coverage.

Node `review` records store target hashes and timestamps written by
`review --accept --node <id>` or `review --accept --nodes-from-entry <id>`.
`--retract` with these selectors clears those records without changing verification evidence. Fresh checks
compare the current targets to those hashes; changed targets show **Review outdated**.
The command records a maintainer's decision rather than providing authentication.
AI proposals require review before merge; future agents must keep approved targets fixed. Editorial status
remains independent of formal readiness.

`review --accept --entry <id>` records a separate maintainer review of mathematical
correctness, rendered presentation, and complete, nonredundant block coverage. It
validates the corpus and requires every block to have a mapping (possibly empty)
and every linked node to name a declaration. It changes editorial `status` from
`draft` to `final`; the Draft badge and review note disappear. It leaves node
approvals and Lean evidence unchanged, allowing unfinished proofs and unapproved
nodes. `review --retract --entry <id>` restores `draft`. Both actions support
`--dry-run` and never run Lean. Entry status is not hash-bound: substantive changes
to text, assets, mappings, or linked statements need retraction and renewed review.

## Sources and access

The entry header displays a compact **Based on:** citation with additional sources
collapsed. Citation authors identify the cited work. Formal sources retain their
upstream attribution. A maintainer decides what is included.

The read-only formal API exposes `/api/formal/nodes/` and
`/api/formal/nodes/<id>/`, including `description`, derived `status`, `status_label`, dependencies, source,
node-page links, `target_sha256`, `review_current`, and `review_matches_last_check`. It does not load the human
corpus. Node pages show the mathematical description, current checked signature, proof
prerequisites, and escaped source with line links. Descriptions are included in
correspondence review hashes but excluded from Lean evidence fingerprints. Human-corpus APIs,
search, write endpoints, and autonomous workers remain future work.

`verification_complete` indicates valid Lean evidence with no direct or transitive
`sorry`, independently of declaration review and the manually declared dependency
statuses. `checked_on` records when a valid check ran for the node's verification
group (its project module or the shared Mathlib audit),
even if it found an unfinished proof; checks of unrelated modules do not change
this date. The node page uses `verification_complete` for **Verified on …** / **Not
verified**, and `review_matches_last_check` for **Reviewed on …** / **Under review**.
If evidence is stale and the description and binding still match the last checked
target, its recorded review stays visible alongside **Not verified**.
`review_current` requires fresh evidence, and `target_sha256` remains
unavailable while stale; the historical comparison cannot certify current source
or complete a node. The API and overall badge retain the detailed derived statuses.

Agents can also read files directly. Formal dependencies are distinct from human
citations: an explanatory link need not occur in a proof term, and a formal helper
may be absent from the exposition. Declared node edges are not a complete extracted
proof graph. Git commits and content hashes identify reproducible inputs without
per-entry version fields. Statement writing and theorem proving will be measured
separately in the [experiment plan](formalization-experiments.md).
