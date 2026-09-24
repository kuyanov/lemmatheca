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
are never identifiers. Local links show the derived label; cross-entry links show
the result's name. Both return to the citing block, reopening an answer when needed.
Equations and figures have their own local labels. Tables and images belong to
the human source; assets stay inside the entry folder.

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

A node is ready only with a reviewed statement, valid verification evidence, and
ready declared dependencies. Other nodes have explicit statuses for missing
declarations, review, verification, unfinished proofs, or dependencies. Missing proofs,
including transitive `sorry`, cannot count as ready. Definitions can use existing
Lean definitions; questions map their answers or counterexamples.

Entry badges show Not started when every block is unmapped, and Partial when
some blocks are unmapped but others have mappings (including empty ones). Once
every block has a mapping, the badge shows the percentage of distinct linked
nodes that are ready, including 0% and 100%. Shared nodes count only once;
not-applicable blocks add no nodes, and an all-not-applicable entry displays N/A.
Adding nodes can lower the percentage. These percentages count nodes, not proof
difficulty or effort, and depend on the current block mappings for coverage.

Committing a mapping, including an empty one, records the maintainer's coverage
review. Node `review` records store target hashes and timestamps written by
`review --accept`, for individual nodes or all linked nodes in an entry.
`review --retract` clears those records without changing verification evidence. Fresh checks
compare the current targets to those hashes; changed targets show **Review outdated**.
The command records a maintainer's decision rather than providing authentication.
AI proposals require review before merge; future agents must keep approved targets fixed. Editorial status
remains independent of formal readiness.

## Sources and access

The entry header displays a compact **Based on:** citation with additional sources
collapsed. Citation authors identify the cited work. Formal sources retain their
upstream attribution. A maintainer decides what is included.

The read-only formal API exposes `/api/formal/nodes/` and
`/api/formal/nodes/<id>/`, including `description`, derived `status`, `status_label`, dependencies, source,
node-page links, `target_sha256`, and `review_current`. It does not load the human
corpus. Node pages show the mathematical description, current checked signature, proof
prerequisites, and escaped source with line links. Descriptions are reviewed through
Git and excluded from Lean evidence and target review hashes. Human-corpus APIs,
search, write endpoints, and autonomous workers remain future work.

`verification_complete` indicates valid Lean evidence with no direct or transitive
`sorry`, independently of declaration review and the manually declared dependency
statuses. `checked_on` records when a valid check ran, even if it found an unfinished
proof. The node page uses `verification_complete` for **Verified on …** / **Not
verified**, and `review_current` for **Reviewed on …** / **Under review**. The API
and overall badge retain the detailed derived statuses.

Agents can also read files directly. Formal dependencies are distinct from human
citations: an explanatory link need not occur in a proof term, and a formal helper
may be absent from the exposition. Declared node edges are not a complete extracted
proof graph. Git commits and content hashes identify reproducible inputs without
per-entry version fields. Statement writing and theorem proving will be measured
separately in the [experiment plan](formalization-experiments.md).
