# Documentation

Start with the [project overview and setup](../README.md), then follow
[CONTRIBUTING.md](../CONTRIBUTING.md) to write, review, or formalize an entry.

| Guide | Contents |
| --- | --- |
| [Corpus](corpus.md) | Entry metadata, HTML, references, assets, block-to-node mappings, taxonomy, and validation |
| [Formalization](formal.md) | Node records, Lean bindings, proof planning, verification, and generated results |
| [Web app](app.md) | Architecture, routes, local reads, tests, benchmarks, deployment, and scaling |
| [Vendor assets](vendor.md) | Bundled KaTeX provenance, license, and update procedure |
| [Contribution workflow](../CONTRIBUTING.md) | The six authoring stages and links to their executable Markdown prompts |
| [Source errors](../corpus/source-errors.md) | Confirmed mathematical defects in cited publications, checked repairs, affected entry blocks, and source-review coverage |
| [Reference backlog and planning](../corpus/reference-planning.md) | One four-column [upcoming-reference table](../corpus/reference-planning.md#upcoming-references), plus separate sections for existing-target integration, future-entry plans, correspondences to establish, and deferred extensions |

Command examples use the repository root unless stated otherwise. Component
guides live here; the root README provides onboarding and `prompts/` holds the
instructions for individual authoring stages. Update these contracts and prompts
together when changing the corpus format or contribution workflow.

Entries should have no major dependencies on substantial theory missing from the
corpus. Familiar background facts, including standard real-number facts, may be
used without a reference. Audit and update the single four-column
[upcoming-reference table](../corpus/reference-planning.md#upcoming-references) when drafting;
audit it and propose corrections when reviewing. Preserve precise current
consuming entry/block IDs. Add links when the future areas supply suitable target
blocks, then remove only fulfilled locations. Keep other integration, expansion,
correspondence, and scope notes in separate sections of the same authoritative
document or in the handoff. Substantial missing prerequisites must be developed,
or the dependent material narrowed or deferred; merely recording them does not
make an entry ready.

Source checks maintain [Source errors](../corpus/source-errors.md), with serious
mathematical defects distinguished from local slips and valid compressed proofs.
Record exact versions and reviewed passages; an inspected passage does not certify
an entire publication. See the [maintenance contract](corpus.md#source-errors).

Formal verification uses classical Lean with Choice permitted by default. See the
[verification rules](formal.md#build-and-verification) for the supported axioms and
badge criteria.
