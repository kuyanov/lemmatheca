# Documentation

Start with the [project overview and setup](../README.md), then follow
[CONTRIBUTING.md](../CONTRIBUTING.md) to write, review, or formalize an entry.

| Guide | Contents |
| --- | --- |
| [Corpus](corpus.md) | Entry metadata, HTML, references, assets, block-to-node mappings, taxonomy, and validation |
| [Formalization](formal.md) | Node records, Lean bindings, proof planning, verification, and generated results |
| [Web app](app.md) | Architecture, reader and authoring APIs, derived index and bounded text cache, tests, deployment, and scaling |
| [Vendor assets](vendor.md) | Bundled KaTeX provenance, license, and update procedure |
| [Contribution workflow](../CONTRIBUTING.md) | The six authoring stages and links to their executable Markdown prompts |
| [Source errors](../corpus/source-errors/index.json) | Individually addressable publication reviews and findings, indexed by entry and publication URL |
| [Reference backlog and planning](../corpus/reference-planning/index.json) | Focused JSON records indexed by entry, area, kind, and URL; upcoming references remain one logical collection |

Command examples use the repository root unless stated otherwise. Component
guides live here; the root README provides onboarding and `prompts/` holds the
instructions for individual authoring stages. Update these contracts and prompts
together when changing the corpus format or contribution workflow. Follow the
[stage responsibilities](../CONTRIBUTING.md#stage-responsibilities) and
[change-based checks](../CONTRIBUTING.md#validation-and-submission) rather than
repeating all audits in every stage.

Entries should have no major dependencies on substantial theory missing from the
corpus. Familiar background facts, including standard real-number facts, may be
used without a reference. For new or changed mathematical coverage, step 2 owns
[reference integration](../CONTRIBUTING.md#reference-integration), including the
single `upcoming-reference` collection in [reference planning](../corpus/reference-planning/index.json)
and useful incoming links from existing consuming entries. Step 3 checks relevant
integration changes and proposes corrections. Wording and layout revisions check
affected links only. Preserve precise current consuming entry/block IDs and remove
only fulfilled locations. Keep other integration, expansion, correspondence, and
scope notes in separate record kinds in the same registry or in the
handoff. Planning records track outstanding work only; preserve unfinished
scope and its needed prerequisites and sources. Substantial missing prerequisites must
be developed, or the dependent material narrowed or deferred; merely recording them does not
make an entry ready.

Source checks maintain [Source errors](../corpus/source-errors/index.json), with serious
mathematical defects distinguished from local slips and valid compressed proofs.
Record exact versions and reviewed passages; an inspected passage does not certify
an entire publication. See the [maintenance contract](corpus.md#source-errors).

Formal verification uses classical Lean with Choice permitted by default. See the
[verification rules](formal.md#build-and-verification) for the supported axioms and
badge criteria.
