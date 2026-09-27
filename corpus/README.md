# Mathematical corpus

Entries, nodes, and navigation are repository files. The Django app reads them
directly. Human review happens in GitHub pull requests, without approval fields
or an editorial status in the corpus.

## Layout and navigation

```text
corpus/
  entries/<entry-id>/
    entry.json
    entry.html
    assets/                 # Optional figures and supplementary files
  nodes/<node-id>.json
  taxonomy.json
  area_entries.json
```

File and directory names must match their record's `id`. Entry and node IDs start
with a letter or digit and use letters, digits, hyphens, or underscores. Keep them
stable when changing titles or subject categories.

`taxonomy.json` defines areas with `id`, `title`, `parent`, and `description`.
`area_entries.json` maps primary area IDs to ordered entry-ID lists under `areas`.
Add each entry once to its primary area's list. This index controls listings,
navigation counts, the featured entry, and the next-entry link. An unlisted entry
can still be opened by ID but is not added to navigation by directory scanning.
`additional_areas` is metadata; current listings use the primary-area index.

## Entry metadata

Authors maintain these fields in `entry.json`:

```text
id, title, based_on, primary_area, additional_areas,
reading_time, summary, abstract
```

`reading_time` is an estimated positive integer number of minutes, allowing time
for the arguments and questions. `summary` is the short listing description;
`abstract` introduces the entry on its own page. Write original exposition and
credit inspected sources in `based_on`.

`based_on` is a list of citations with `authors` (names) and `title`. Optional
publication details include `year`, `venue`, `volume`, `issue`, `pages`, `doi`, and
`url`. Store a bare DOI, not a DOI URL; use an HTTP(S) URL where available. Print-only
citations are supported. Use `[]` for original material with no external sources.
Citation authors identify the cited work, not the entry's contributor.

The build generates an additional `formalization` object containing the counts,
status, percentage when applicable, label, and description for the entry-list badge.
Do not edit it by hand. Area pages read only this metadata, without parsing entry
HTML or loading nodes. Rerun `uv run python app/manage.py build` after changing HTML,
bindings, or proofs and commit the refreshed entry and node JSON. Failed checks or
invalid entry summaries leave the previous generated data intact.

Block structure, human references, and formal-node mappings belong in HTML, not
in extra metadata lists. Keep prompts, proof attempts, and experiment logs outside
entry metadata. There are no stored review records or entry approval flags.

## HTML and references

Use trusted HTML fragments with explicitly closed elements. Every top-level block
is a `section` with a stable `id`, a `data-kind`, and one direct, nonempty `h2`:

```html
<section id="translation" data-kind="definition">
  <h2>Translation</h2>
  <p>Translate by \(x\mapsto x+b\).</p>
</section>
```

Supported kinds are `definition`, `lemma`, `theorem`, and `question`. The reader
generates numbering separately for each kind, as well as headings, the contents
sidebar, badges, and navigation. Do not include a document shell or Django template
instructions in the entry. The parser handles repository-owned HTML; it is not an
upload sanitizer.

Use `href="#block-id"` for a local block and `href="entry-id#block-id"` for another
entry. Cross-entry references must target mathematical blocks. The renderer resolves
IDs to URLs and loads referenced entries on demand. Do not use area paths, `../`,
`entry.html`, or rendered reader URLs in these references.

Empty local links receive generated block, figure, or table labels. Empty cross-entry
links receive the target heading. Existing link text and inline formatting are
preserved. Prefer empty local links for numbering and meaningful cross-entry text
that fits the sentence. Block and figure/table references carry contextual return
links, including returning to an expanded question answer.

For collapsible answers, use:

```html
<section id="translation-inverse" data-kind="question">
  <h2>Undoing a translation</h2>
  <p>How can you undo \(x\mapsto x+b\)?</p>
  <details class="question-answer">
    <summary><span class="answer-show">Show answer</span><span class="answer-hide">Hide answer</span></summary>
    <div class="answer-body"><p>Apply \(y\mapsto y-b\).</p></div>
  </details>
</section>
```

## Mathematics, figures, and assets

Use `\(...\)` for inline mathematics and `\[...\]` for display mathematics.
Escape HTML characters such as `<` and `&` as `&lt;` and `&amp;`, including LaTeX
alignment separators. KaTeX is bundled with the app.

The renderer numbers labelled equations and resolves entry-local `\eqref` references:

```html
<div class="math-display">\[ f(x)=x+b. \label{eq:translation} \]</div>
<p>Use \eqref{eq:translation} to compute the image.</p>
```

Put one label in one plain `div` or `p` with class `math-display`, containing one
display formula. Omit explicit `\tag` numbering. Labels must be unique and references
must resolve. These labels and ordinary element IDs share the entry's anchor space;
`<block-id>-title` is reserved for the generated block heading.

Figures and tables each receive numbering in source order. Give each a stable ID
and exactly one direct `figcaption` or `caption`, written without a number. Images
need useful alternative text. Wide tables receive a keyboard-focusable scrolling
container automatically; use appropriate table headings and `scope` attributes.

Store images and supplements in the entry's `assets/` directory and reference them
as `assets/filename.svg` or `assets/supplement.pdf`. Paths must remain inside that
directory. The reader maps them to static URLs. Restart the development server when
adding an asset directory so Django registers it; `collectstatic` includes these
assets for deployment.

## Block-to-node mapping

Human exposition can be written before formalization. Use `data-formal` to record
coverage when preparing bindings:

| Attribute | Meaning |
| --- | --- |
| Absent | Formalization has not been planned for the block |
| `data-formal=""` | The block has nothing to formalize |
| `data-formal="node-a node-b"` | The listed nodes collectively cover the block |

Each linked ID must exist in `corpus/nodes/` and occur only once in a block's list.
A definition can link to a Lean definition; a question maps its answer or
counterexample. Include examples and distinct claims within prose. Reuse a node
across blocks and entries when it expresses the same mathematics. Do not use an
empty mapping to hide unfinished work.

Badges count distinct verified nodes, so shared nodes count once per entry. With
all blocks mapped, they display the verified proportion, or N/A if every mapping
is empty. Wholly unplanned entries display Not started; partly unplanned entries
display Partial. These are formalization summaries, not GitHub review decisions.
Node pages themselves display only Verified or Not verified.

The [Lean guide](../formal/README.md#formal-nodes) defines node records, descriptions,
bindings, and the distinction between proof-planning hints and actual Lean dependencies.

## Authoring and checks

Use the [authoring prompts](../prompts/README.md). Review the human mathematics and
the description-to-declaration correspondence separately on GitHub; a passing Lean
check does not establish that the intended statement was formalized.

From the repository root, after making changes:

```sh
uv run python app/manage.py build
uv run python app/manage.py test catalog
```

The build checks declarations, parses entries, and refreshes node data and entry-list
summaries. Reader tests also exercise rendering and references. Inspect the edited
pages for mathematical layout, working links, questions, and figures. CI checks
that the generated JSON matches the committed files. See [app/README.md](../app/README.md)
for serving and deployment.
