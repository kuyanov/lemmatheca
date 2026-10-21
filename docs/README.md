# Documentation

See the [build guide](build.md) for commands, flags, and generated outputs.
The [project overview](../README.md) covers setup, and
[CONTRIBUTING.md](../CONTRIBUTING.md) covers authoring and required checks.

| Guide | Contents |
| --- | --- |
| [Build](build.md) | Build stages, generated outputs, flags, command combinations, and failure behavior |
| [Corpus](corpus.md) | Entry metadata, HTML, references, assets, mappings, taxonomy, and source/planning records |
| [Formalization](formal.md) | Node records, Lean bindings, proof planning, verification, and generated results |
| [Web app](app.md) | Reader and authoring APIs, derived index, bounded text cache, tests, deployment, and scaling |
| [Vendor assets](vendor.md) | Bundled KaTeX provenance, license, and update procedure |
| [Prompts](../prompts/) | Root-owned area planning and delegated entry stages; see the [area pipeline](../CONTRIBUTING.md#running-an-area-pipeline) |
| [Source errors](../corpus/source-errors/index.json) | Publication reviews and findings, indexed by entry and publication URL |
| [Reference planning](../corpus/reference-planning/index.json) | Pending references and development records, indexed by entry, area, kind, and URL |

Use the [targeted registry workflow](corpus.md#navigating-source-and-planning-records)
to read focused source/planning records.

Reports and migrated snapshots under the ignored `artifacts/` directory preserve
historical commands, module paths and verification results. Use the guides above
for current conventions.
