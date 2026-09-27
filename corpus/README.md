# Corpus

The Django app reads these files directly. There is no database.

- `entries/<id>/entry.json`: title, summary, sources, area, reading time, and generated formalization summary.
- `entries/<id>/entry.html`: trusted HTML sections with an `id`, `data-kind`, and heading.
- `entries/<id>/assets/`: figures referenced as `assets/filename.svg` in the HTML.
- `nodes/<id>.json`: mathematical description, Lean binding, dependencies, and status.
- `taxonomy.json`: area hierarchy.
- `area_entries.json`: each area's entry IDs in reading order.

File and directory names must match their record's `id`.
Add each entry to its primary area's list in `area_entries.json`; this index drives
area listings, counts, the featured entry, and next-entry links. Unlisted entries
can still be opened by ID but do not appear in navigation. The server does not scan
entry directories to discover or append unlisted entries.

`python app/manage.py build` generates the `formalization` object in each entry's
metadata from its HTML block bindings and the new node verification results. It
contains the counts, status, and display labels needed for the entry-list badge.
Do not edit it by hand. Area pages read only this metadata, without parsing entry
HTML or loading nodes. Run the build after changing an entry's HTML or node bindings
and commit the refreshed metadata. Failed builds leave existing summaries intact.

Link a section to nodes with space-separated IDs in `data-formal`:

```html
<section id="two-inclusions" data-kind="lemma"
         data-formal="set-equality-iff-two-inclusions set-subset-transitive">
  <h2>Proving equality by two inclusions</h2>
  <p>...</p>
</section>
```

Use `#section-id` for a local reference or `entry-id#section-id` for another
entry. Empty link text is filled from the target heading or figure/table label.
Write inline mathematics between `\(` and `\)`, and display mathematics between
`\[` and `\]`. The reader uses bundled KaTeX.

A node looks like this:

```json
{
  "id": "set-subset-transitive",
  "description": "Inclusion of sets is transitive.",
  "module": "Mathlib.Data.Set.Basic",
  "declaration": "Set.Subset.trans",
  "dependencies": ["set-subset"],
  "verified": true
}
```

`verified` is the only stored status flag and is written by `python app/manage.py build`.
It is true only when the Lean declaration checks without `sorry`, directly or
indirectly, and uses only Lean's usual logical axioms. New nodes start with
`verified: false` and may have a null module/declaration until formalized.
Unbound nodes are not verified. An unsuccessful build leaves all node JSON untouched.
Results describe the last successful build; rerun it after changing Lean code or bindings.
Reviews of entries and nodes happen on GitHub, with no review fields in the corpus.

`module` is the Lean module that defines the declaration. The build imports it
and updates it to the defining module reported by Lean. The node page uses the
same field for its source browser.

The build also saves `signature` and `declaration_line` for the node page's
checked statement and source links. Failed builds preserve these fields along with
the verification flag and module binding.

The reader labels nodes **Verified** or **Not verified**. Entry and block badges
summarize verification progress; entries have no separate status.

The `dependencies` list is for navigation and proof planning. Lean determines
actual proof dependencies when computing proof status.
