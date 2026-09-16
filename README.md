# Lemmatheca

A mathematical library for people to read, Lean to check, and AI agents to explore.
Readers browse areas and subareas, follow definitions and prerequisites, and enjoy
explanatory proofs. Contributors submit human mathematics. AI assists with
formalization and review; a selected human maintainer decides what is published.

**Current status: design proposal and draft examples.** There is no web application,
Lean project, verification service, or accepted mathematical corpus yet. Nothing in
`examples/` claims to have been checked by Lean or approved by a maintainer.

The proposed starting point is a small Django application, PostgreSQL, Markdown
with LaTeX rendered by MathJax, and isolated Lean 4 workers. Keep published
mathematics in a versioned Git corpus and operational data in PostgreSQL.

Start with these documents:

| Document | What it specifies |
| --- | --- |
| [Architecture](docs/architecture.md) | Tools, folders, website, storage, deployment, and implementation order |
| [Content model](docs/content-model.md) | Definitions, statements, multiple proofs, revisions, taxonomy, and AI access |
| [Verification and review](docs/verification-and-review.md) | Lean checks, external lemmas, translation, beauty grading, and maintainer authority |
| [Mathematical baseline](docs/baseline.md) | A small starting collection, explicit hypotheses, human proofs, and dependency plans |
| [Example records](examples/README.md) | Concrete draft JSON and Markdown for sumsets and a cardinality bound |

Three distinctions shape the project:

1. Lean checks a formal statement. A maintainer must also check that this is the
   intended statement and that its proof follows the submitted human argument.
2. A Lean-checked proof can still depend on external mathematical theorems. Track
   those dependencies independently from foundational axioms.
3. Correctness is a publication requirement. Beauty is a reasoned editorial
   judgment; AI grades never grant publication permission.

Build one complete path first: **sumset definition → cardinality bound → human
proof → faithful Lean proof → dependency report → maintainer approval → readable
page and JSON export**. Expand the mathematical coverage after that path works.
