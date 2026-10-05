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
| [Reference backlog](reference-backlog.md) | Familiar background awaiting useful corpus references, with entry/block locations and future targets |

Command examples use the repository root unless stated otherwise. Component
guides live here; the root README provides onboarding and `prompts/` holds the
instructions for individual authoring stages. Update these contracts and prompts
together when changing the corpus format or contribution workflow.

Entries should have no major dependencies on substantial theory missing from the
corpus. Familiar background facts, including standard real-number facts, may be
used without a reference. Keep useful future links in the reference backlog and
add them when suitable entries become available. Substantial missing prerequisites
must instead be developed, or the dependent material narrowed or deferred; merely
recording them does not make an entry ready.

Formal verification uses classical Lean with Choice permitted by default. See the
[verification rules](formal.md#build-and-verification) for the supported axioms and
badge criteria.
