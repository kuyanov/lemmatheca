# Reference planning

This registry tracks pending references and their development context. Start with
the [catalog](index.json), filter by entry, area, kind or publication URL, then open
the selected files in `records/`. Read the
[registry workflow](../../docs/corpus.md#navigating-source-and-planning-records)
for API queries and record fields.

## Scope

The `upcoming-reference` kind is the single collection of links from current
entry blocks to future mathematical areas. Other kinds separate outstanding
integration work, correspondences, source research and development plans:

| Kind | Pending work |
| --- | --- |
| `upcoming-reference` | Future coverage to reference from existing consuming blocks |
| `integration` | Useful links to targets that already exist; inspect their exact statements and assumptions before adding them |
| `correspondence` | Comparisons to establish in the appropriate area before using them as references |
| `planned-entry` | Proposed entries with their scope, prerequisites and useful existing targets |
| `area-plan` | Focused development context and reading plans for an area |
| `source-plan` | Source research needed for proposed coverage |
| `deferred` | Extensions and optional branches awaiting further development |

Proposed titles suggest coverage; they do not authorize new entries or certify
prerequisites. Follow the
[prerequisite and scope rules](../../CONTRIBUTING.md#prerequisites-and-scope).
Existing targets may supply only a foundation for a fuller future treatment.
Planned entries have no drafted block IDs: identify their actual consuming blocks
during drafting and add links only where the stated facts help the argument.
Scheduling batches are not additional prerequisites; each plan records its own
requirements.

## Maintenance

Follow the [reference-integration rules](../../CONTRIBUTING.md#reference-integration).
When new coverage supplies a planned target, update the existing source entries
as well as the new entry. Inspect target statements and assumptions, apply the
links, then remove or narrow fulfilled planning records. Retain only outstanding
facts and consuming locations; completed work and completion narratives do not
belong here. Source-review history belongs in [Source errors](../source-errors/README.md).

Keep stable record IDs and use `entry_refs` for existing entry/block locations;
use `planned_entry_ids` for future entries without inventing anchors. Markdown
links inside JSON records resolve relative to `corpus/`; links in this README
resolve relative to this directory.

After record edits, run `uv run python app/manage.py build --no-lean` under the
[shared publication rules](../../CONTRIBUTING.md#validation-and-submission).
The build validates records and refreshes the catalog; it does not insert links
or decide whether planned mathematics has been covered. The README is
documentation, not an input to the registry API or build.
