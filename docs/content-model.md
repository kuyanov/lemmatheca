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
blocks can link multiple nodes, and nodes can be shared. A node without a
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

Entry badges show Not started, Partial, or Complete without a percentage.
Their counts include distinct linked nodes only once. Unmapped blocks keep an
entry Partial even when every linked node is ready. Not-applicable blocks are
excluded, and an all-not-applicable entry displays N/A. Block percentages count
nodes, not proof difficulty or effort; they do not measure entry-wide coverage.

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
`/api/formal/nodes/<id>/`, including derived `status`, `status_label`, dependencies, source,
node-page links, `target_sha256`, and `review_current`. It does not load the human corpus. Node pages show escaped
source with an inferred declaration line where possible. Human-corpus APIs,
search, write endpoints, and autonomous workers remain future work.

Agents can also read files directly. Formal dependencies are distinct from human
citations: an explanatory link need not occur in a proof term, and a formal helper
may be absent from the exposition. Declared node edges are not a complete extracted
proof graph. Git commits and content hashes identify reproducible inputs without
per-entry version fields. Statement writing and theorem proving will be measured
separately in the [experiment plan](formalization-experiments.md).
