# Entry folders and authoring format

This is the recommended next storage layout, not a completed migration. The
prototype still reads `examples/sumsets/entries.json` and Django HTML fragments.

## Human entries: one folder per stable ID

Use `corpus/entries/<entry-id>/`, independent of the browsing taxonomy:

```text
corpus/
├── taxonomy.json
├── reading-order.json
├── external-lemmas.json
└── entries/
    ├── thm-sumset-lower-bound/
    │   ├── entry.json
    │   ├── entry.html
    │   └── assets/
    │       ├── sumset-translation.svg
    │       └── sources/                 # Editable diagram sources, when needed
    └── thm-triple-sumset-lower-bound/
        ├── entry.json
        └── entry.html

formal/
└── Lemmatheca/
    └── Combinatorics/
        └── Additive/
            ├── Sumsets.lean
            └── FiniteSumsets.lean
```

`corpus/` groups the mathematical content separately from the application; the
important choice is the flat `entries/<entry-id>/` layer inside it. Existing seed
IDs are retained for compatibility even though their `thm-` prefix predates the
paper-like entries. New IDs should identify an entry, not a theorem or category.
Once assigned, an ID stays fixed when its title or subject classification changes.

| Layout | Benefit | Cost |
| --- | --- | --- |
| `entries/<entry-id>/` | One stable home; works with multiple subject memberships | Subject browsing needs an index |
| `entries/Combinatorics/Additive/…/<entry-id>/` | Convenient initial browsing in an editor | Forces a primary physical location; reclassification moves files and relative links |

The website already supplies subject browsing. Put `primary_area` and additional
area memberships in `entry.json`; generate category indexes from those fields.
Do not copy an entry into each subject folder. A generated index can also make
the corpus convenient to browse from an editor.

Store the editorial reading order separately as ordered entry IDs per area in
`reading-order.json`. It controls category listings and “Next entry”; filesystem
enumeration and alphabetical titles should not determine a mathematical reading
sequence. Reading order is distinct from formal prerequisites. At present the
prototype uses the order in its existing `entries.json`, within each primary area.

## Sources: HTML, LaTeX, and a small JSON sidecar

Use **HTML as the canonical human source**, with `\(...\)` and `\[...\]` for
mathematics, plus JSON for structured metadata. Keep one editable source for the
prose rather than parallel HTML and Markdown versions.

- `entry.html` contains the whole mathematical note: exposition, definitions,
  statements, proofs, figures, and questions with native `details` answers. It
  contains content only; the application supplies the page shell and navigation.
- `entry.json` contains the stable ID, title, abstract, categories, authorship,
  revision, references, and block/proof bindings to Lean declarations. Proofs have
  their own identities so alternative arguments can be reviewed independently.
- `assets/` contains the entry's images and supplementary files. Keep editable
  diagram sources here too. Images use relative paths such as
  `assets/sumset-translation.svg`, with captions, alt text, and dimensions.
- Add `parts/` with HTML fragments only when an entry becomes inconvenient to edit
  as one file; entry-local includes would need an explicit importer convention.
  Start with a single `entry.html`.

Give each mathematical block a stable local anchor. The source's block order
determines reading order and display numbers; do not maintain a second manually
ordered list in JSON. Metadata bindings are keyed by block ID. Validation should
reject duplicate anchors, dangling references, missing assets, and bindings to
nonexistent blocks. The exact HTML markers can be settled with the importer;
authors should not need to reproduce the site's layout or CSS classes.

For portable source links, use relative HTML links such as
`../thm-sumset-lower-bound/entry.html#sumset-lower-bound`. The importer can resolve
the folder ID and fragment, check the target, and rewrite it to the canonical web
route, including contextual return navigation. Cross-entry link text stays a
readable result name; local result numbers are derived when rendering. Published
reference metadata pins the target revision separately from the source link.

Keep Django page templates in `app/templates/` and mathematical source in the
entry folders. The current trusted `{% math_ref %}` tags can remain during the
transition; the eventual corpus importer should resolve references and assets
without executing contributor HTML as a Django template. A JSON export can expose
the parsed block structure and formal bindings to agents alongside the original
HTML and assets. A new browser framework is unnecessary.

## Lean: organize a reusable library, bind it to entries

Keep Lean code under **`formal/Lemmatheca/`**, using stable, descriptive module
paths such as `Combinatorics/Additive/FiniteSumsets.lean`. These are library module
names, not a mirror of the website's taxonomy. Use consistent Lean module naming
without spaces. A website category rename should not trigger a Lean module move.

There need not be one Lean file per entry. Both current notes use definitions and
results from `FiniteSumsets.lean`; keeping those together is reasonable. Split
modules when their size or import dependencies justify it, not merely because a
new article cites them. Put a shared definition in one module and import it from
others rather than creating an entry-specific copy.

Each block/proof binding records the module and fully qualified declaration, for
example:

```json
{
  "block_id": "sumset-lower-bound",
  "module": "Lemmatheca.Combinatorics.Additive.FiniteSumsets",
  "declaration": "Lemmatheca.sumset_card_lower_bound"
}
```

This relationship can be many-to-many: an entry may need several modules, and a
module may support several entries. Formal source remains solely in the Lean
project; an entry folder does not hold a second editable `.lean` copy. Release
manifests tie the human source, assets, formal sources, and check reports to exact
revisions and hashes. Local lemma numbers are never Lean declaration identities.

## Migration scope

First move each note's HTML, mathematical records, and illustration into its own
entry folder and adapt the catalog loader and asset serving together. Preserve
existing entry IDs, block anchors, public routes, and citation return behavior.
Then consolidate the small fragments into `entry.html` and add validation and
exports. These should be separate, reviewable changes; the “Next entry” button
does not require a storage migration or Lean module renaming.
