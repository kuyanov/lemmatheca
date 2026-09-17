# Content and machine access

## Mathematical objects

An entry is a short paper: a title, abstract, and an ordered sequence of definitions,
lemmas, theorems, questions, proofs, and explanatory material. The entry is the
reading unit; each mathematical block is an independently addressable object.

Keep a statement separate from its proofs. Two beautiful arguments for the same
theorem deserve two proof records, separate authorship, and separate grades.

| Entity | Important fields and relations |
| --- | --- |
| Area | Stable ID, title, parent, aliases, display order |
| Entry | Stable ID, kind `article`, slug, title, abstract, areas, ordered mathematical blocks |
| Entry revision | Immutable block order and revisions, human text, assets, attribution |
| Mathematical block | Stable ID within its entry, kind (`definition`, `lemma`, `theorem`, `question`), title, hypotheses, prerequisites, formal binding |
| Proof | Stable ID, exact statement revision, human argument, Lean declaration, argument alignment |
| Formalization | Source and environment hashes, exact elaborated type, bindings, dependency graph, axiom report |
| Submission | Proposer, target entry/proof, immutable revisions, workflow state |
| Verification run | Exact revision/environment/policy inputs, result, diagnostics, resource use, artifacts |
| Review | Reviewer identity/type, target revision, rubric version, dimension grades, rationale |
| Decision | Human maintainer, immutable revision/manifest hash, outcome, reason, timestamp |
| Release | Corpus commit, complete manifest, verification artifact, publication timestamp |
| External lemma | Precise declaration/source revision, mathematical statement, verification status, reason and authorization |

A definition has a formal definition and a human explanation, rather than a fake
proof field. A construction may additionally require existence or well-definedness
theorems; store those as linked statements. State whether a mathematical object is
bundled, a predicate, or a typeclass when this matters to the human/formal mapping.

Definitions and statements can link to explanatory examples, illustrations,
references, equivalent formulations, and related results. Expository text itself
is not mechanically certified; mathematical claims inside it must be backed by
linked statements or clearly identified as motivation or conjecture. Do not put
unchecked conjectures in the accepted-theorem collection.

## Numbering, citations, and questions

Number blocks by kind within each entry: Definition 1, Definition 2, Lemma 1,
Lemma 2, Theorem 1, Question 1. The renderer derives numbers from their order;
neither a display number nor an area's position is an identifier.

Use a stable pair `(entry_id, block_id)` to identify a target. A canonical reader
link ends in a descriptive fragment such as `#sumset-lower-bound`. Within an entry,
show “Lemma 2”; across entries, show the linked name “Sumset lower bound”. A title
hint can identify its containing entry when names coincide. Moving or renumbering
blocks must preserve their IDs, or leave an explicit alias for old anchors.

Questions may have a native HTML `details` answer, collapsed initially. An open
question may have no answer. An answer and its formalization are distinct from the
question; conjectures must never acquire a theorem verification badge. The demo
uses answered questions with Lean-checked counterexamples. Publication remains an
entry/revision decision, while formal verification attaches to specific results.

In the prototype, `examples/sumsets/entries.json` records article order, block IDs,
titles, kinds, references, and trusted HTML templates. Existing mathematical JSON
records remain separate and are linked through a block's `record` field. The old
web IDs and URLs are retained for compatibility. Article references are explicitly
block-scoped; legacy statement/proof prerequisites still identify mathematical
records. This distinguishes the reading structure from the proof dependency graph.

## Navigation versus dependencies

Use a hierarchy for browsing, with additional category memberships for subjects
that overlap. For example:

```text
Combinatorics
├── Additive combinatorics
│   ├── Sumsets
│   └── Additive energy
├── Enumerative combinatorics
│   ├── Binomial coefficients
│   └── Generating functions
└── Graph theory
```

“Binomial coefficients” is a topic, not a theorem and not the definition's ID.
An entry can appear in more than one topic while keeping one canonical URL. Areas
need not all have the same depth. IDs do not encode the taxonomy, so moving an
entry does not break links. Old slugs redirect.

Mathematical dependencies form a separate directed graph. Use typed edges:
`uses_definition`, `uses_statement`, `formal_dependency`, `explains`, and
`equivalent_to`. Only logical dependency edges must be acyclic at the accepted
revision level; explanatory cross-links can form cycles.

Keep human-declared prerequisites separate from dependencies extracted from Lean.
A proof can require a formal helper that is pedagogically invisible. Conversely,
a suggested background reading link need not occur in the proof term. Every edge
names a revision or an immutable external declaration, not “whatever is latest.”

## Revisions and authorship

Published revisions never change in place. A change to a theorem's hypotheses,
definition, proof, illustration affecting its argument, or formal source produces
a new revision. Reviews and verification reports belong to the revision that was
actually examined. Formal success may be reused when formal inputs are identical,
but an editorial change still needs approval of the new human text.

Use opaque IDs in production. Friendly seed IDs in `examples/` make this proposal
easier to read and still remain independent of category paths. A release snapshot
and content hashes identify exact bytes. A proof pins its statement revision; do
not carry it forward automatically after the statement changes.

Record original human authors, submitters, formalizers, AI assistance, source
references, and license. AI-generated seed text must not be attributed to a human
maintainer. Preserve the original argument when proposing edits. A materially
different AI proof is a separate proposal, not an unannounced replacement.

The repository currently has an Apache-2.0 license. These examples inherit it.
Document the contribution terms before accepting public submissions; an external
source citation does not by itself grant permission to copy that source's prose
or figures. Preserve any required upstream attribution for imported formal code.

## Formal bindings and review alignment

Each accepted definition or proof points to a declaration in `formal/`. Store:

- module, declaration name, and exact toolchain/library revisions;
- elaborated statement, including implicit parameters and typeclass hypotheses;
- mapping of human notation to formal objects and quantifier domains;
- source locations linking major human proof steps to Lean lemmas or subproofs;
- kernel verification, foundational axioms, full dependency closure, and external
  dependency set as separate fields;
- maintainer judgment that the formalization expresses the human mathematics.

For example, a finite sumset must distinguish a `Finset` from a potentially
infinite `Set`. A cardinality operator that returns zero for infinite sets must
not silently replace the finite notion used by the human author. Equality of
formal targets alone does not establish that the same argument was formalized.

## AI-friendly interface

Provide a read-only, versioned API with stable identifiers, pagination, and explicit
release selection. The routes below are proposed contracts, not existing endpoints.

| Endpoint | Purpose |
| --- | --- |
| `GET /api/v1/releases` | Available immutable corpus snapshots |
| `GET /api/v1/entries?release=...&area=...&q=...&cursor=...` | Search and enumerate accepted entries |
| `GET /api/v1/entries/<id>?release=...` | Article, abstract, ordered blocks and revisions |
| `GET /api/v1/entries/<id>/blocks/<block_id>?release=...` | Individual definition/result/question, hypotheses, proofs, and formal bindings |
| `GET /api/v1/proofs/<id>?release=...` | A particular argument, Lean source, review and verification records |
| `GET /api/v1/entries/<id>/dependencies?release=...` | Direct edges and paginated transitive closure |
| `GET /api/v1/external-lemmas?release=...` | External assumptions/dependencies and their users |
| `GET /api/v1/exports/<release>` | JSONL, Markdown, Lean sources, and asset manifest |

Reports use machine-readable enums and explicit `null`/`not_started` values.
Do not equate absent evidence with a successful check. Return both human and Lean
representations; neither should have to be recovered by scraping a web page.
Assets include captions, alt text, hashes, and source references.

An agent can download the whole accepted snapshot or retrieve a bounded
prerequisite closure for a target theorem. This makes the entire *local corpus*
available without requiring it to fit into one model context. It does not mean
the project contains everything known to mathematics. Keep strict results,
approved external dependencies, drafts, and conjectures distinguishable in every
export and search filter.

Start with lexical search, declaration-name lookup, and graph traversal. Add
embeddings or formal type search only after real retrieval failures justify them.
Agents may suggest missing prerequisites privately; public additions remain a
manual human action followed by normal review.

## Example scope

The records under [`examples/`](../examples/README.md) illustrate the on-disk
shape using JSON plus Markdown. They are not a production schema or a published
release. Some blocks have checked Lean bindings; missing verification remains
explicit and does not become success just because another block is checked. The
prototype resolves block references and checks local Lean builds. Production JSON
Schema validation, immutable releases, and the complete dependency audit remain
requirements before publication.
