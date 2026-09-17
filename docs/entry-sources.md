# Entry folders and authoring format

The app reads both mathematical notes directly from `corpus/`. Each note owns its
HTML, JSON metadata, and supplementary assets. There is no parallel Markdown copy
or entry-specific Django template.

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
    │       └── sumset-translation.svg
    └── thm-triple-sumset-lower-bound/
        ├── entry.json
        └── entry.html

formal/Lemmatheca/Combinatorics/Additive/
├── Sumsets.lean
└── FiniteSumsets.lean
```

The entry ID matches its folder name and remains stable when the title or category
changes. Existing `thm-` IDs predate the paper-like entries; they now identify whole
notes. Category paths are metadata, not filesystem paths. Keep an entry's images,
attachments, and editable diagram sources inside its own `assets/` directory.

## Writing an entry

`entry.html` is an HTML fragment containing an ordered series of sections:

```html
<section id="translation" data-kind="definition">
  <h2>Translation</h2>
  <p>For a fixed \(b\in G\), translate by \(x\mapsto x+b\).</p>
</section>

<section id="sumset-lower-bound" data-kind="lemma">
  <h2>Sumset lower bound</h2>
  <p>Use <a href="#translation">Translation</a> to construct an injection.</p>
</section>
```

Every top-level section needs a stable `id`, a `data-kind` (`definition`, `lemma`,
`theorem`, or `question`), and one direct `h2` title. The application supplies the
outer layout, contents, block numbers, permalinks, and verification disclosures.
Numbers follow HTML source order, separately for each kind. Metadata bindings are
keyed by block ID and do not duplicate titles, kinds, or ordering.

Write inline mathematics as `\(...\)` and display mathematics as `\[...\]`.
Use normal HTML escaping: `&lt;` for less-than signs and `&amp;` for ampersands,
including alignment separators in LaTeX. Close non-void HTML elements explicitly;
malformed nesting is rejected. Ordinary format-on-save whitespace is fine.

The existing presentation classes are optional tools: `statement-box` for a result,
`math-display` for a scrollable equation, and `proof-figure` for an illustration.
Questions use `<details class="question-answer">`; the examples show the small
Show/Hide answer labels. Answers start collapsed and reopen when returning from a
citation within them. Source trees are never mutated by a reader's answer state.

Give separately identified proofs their own HTML anchors. A `proofs` object in a
block's metadata maps proof IDs to authorship, method, revision, Lean binding, and
human-to-Lean step alignment. Both main sumset proofs illustrate this convention.

## References and assets

Source links are ordinary HTML links:

```html
<a href="#nonempty-triple-sumset">Nonempty triple sumsets</a>
<a href="../thm-sumset-lower-bound/entry.html#sumset-lower-bound">Sumset lower bound</a>
<img src="assets/sumset-translation.svg" alt="A translation injection" width="720" height="280">
<a href="assets/supplement.pdf">Supplement</a>
```

The renderer derives local reference labels such as “Lemma 1”. Cross-entry links
show the target's title and are rewritten to the public route with the exact
source block recorded for the return link. Cross-entry references must target a
mathematical block; ordinary local links can target figures or proof anchors.

Each block's `references` metadata lists those same mathematical targets and pins
their revisions. The loader rejects missing, extra, or stale recorded citations.
For example:

```json
{
  "references": [
    {
      "entry_id": "thm-sumset-lower-bound",
      "block_id": "sumset-lower-bound",
      "revision": "draft-2"
    }
  ]
}
```

Only entry `assets/` directories are registered with Django's static-file system,
under `entries/<entry-id>/`. `collectstatic` collects these alongside KaTeX and the
site stylesheet. HTML and JSON source files are not exposed as static assets.
Missing assets and paths escaping the entry's asset directory fail validation.
Restart the development server after adding a new entry's asset directory so
Django registers the new static directory.

## Metadata and reading order

`entry.json` has `format_version: 1`, the entry ID, revision, title, abstract,
summary, reading time, primary area, attribution, license, publication state, and
`blocks`, an object keyed by the HTML section IDs. The loader validates IDs,
category memberships, block bindings, proof anchors, references, and Lean paths.
Additional area memberships can be recorded, but the current reader lists entries
and orders them by their primary area.

`reading-order.json` explicitly lists entry IDs in each populated primary area.
Every entry must appear exactly once. This order controls category listings and
“Next entry”; it is independent of filenames and mathematical dependencies.

```json
{
  "format_version": 1,
  "areas": {
    "sumsets": ["thm-sumset-lower-bound", "thm-triple-sumset-lower-bound"]
  }
}
```

The catalog cache invalidates when corpus files change. Editing an existing HTML
or JSON file therefore does not require a server restart. Both examples are
editorial drafts, not maintainer-approved publications. New published revisions
and immutable releases remain future work.

## Lean bindings

Lean modules remain in `formal/Lemmatheca/`, organized as a reusable mathematical
library. Both notes use `Combinatorics/Additive/FiniteSumsets.lean`; website entries
and Lean modules need not correspond one-to-one. A website category rename should
not trigger a Lean module move. There is one editable copy of each formal source.

A block's `formalization` identifies its module and declaration:

```json
{
  "status": "checked",
  "module": "Lemmatheca.Combinatorics.Additive.FiniteSumsets",
  "source": "formal/Lemmatheca/Combinatorics/Additive/FiniteSumsets.lean",
  "declaration": "Lemmatheca.sumset_card_lower_bound",
  "verification_report": "formal/checks/sumsets.json"
}
```

Formal source and report paths are repository-relative. The loader checks the
module/source correspondence and that a checked declaration appears in its report.
This structural check does not execute Lean or replace a fresh build, dependency
audit, or maintainer review. The local development report records the migrated
entry/block revisions and hashes of the exact checked sources.

## Validation and trust boundary

```sh
uv run python app/manage.py validate_corpus
uv run python app/manage.py test catalog
cd formal && lake build
```

The corpus consists of trusted repository-owned HTML. It is parsed and rendered
as content, never executed as a Django template. This parser is not an upload
sanitizer: public submissions still require the planned validation, sanitization,
and review pipeline. No registration or submission endpoint was added by this
storage migration. The source folder and JSON bindings are available directly to
local tools; the versioned public API and exports remain future work.
