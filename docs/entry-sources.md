# Writing entries

Each entry has a stable folder under `corpus/entries/<id>/` containing `entry.html`,
`entry.json`, and an optional `assets/` directory. Lean sources live under
`formal/Lemmatheca/`; existing mathlib declarations can be used directly.

## Metadata

The required entry fields are exactly:

```text
id, title, based_on, primary_area, additional_areas,
status, reading_time, summary, abstract
```

`status` is the editorial state: `draft` or `final`, independent of formalization.
New entries start as drafts. Record the review of correctness, rendering, and
block coverage with `review --accept --entry <id>` to set `final`; use `--retract`
to return to `draft`. Only drafts show an editorial badge and review note. Entry
review allows unfinished proofs and leaves node approvals unchanged; see the
[review workflow](../README.md#recording-reviews) for requirements and re-reviewing edits.
`reading_time` is a positive integer number of minutes. The entry page displays its
title and a bibliography labelled **Based on:**.

`based_on` is a list of citations. Use an empty list for original material without
an external source; the page then omits the bibliography. Each citation requires
`authors` (a nonempty list of names) and `title`. Optional fields are `year` (a
positive integer), `venue`, `volume`, `issue`, `pages`, `doi`, and `url` (nonempty
strings). Store a bare DOI and an HTTP(S) URL, if available. The reader generates
the DOI link; a URL links the title. Citations can also describe print-only sources.
The compact header shows authors, linked title, and year for the first citation;
additional citations sit in a collapsed **more sources** disclosure. The title
links to the DOI when no URL is supplied. Full publication details stay in JSON.
For example:

```json
"based_on": [
  {
    "authors": ["A. Seidenberg"],
    "title": "A Simple Proof of a Theorem of Erdös and Szekeres",
    "year": 1959,
    "venue": "Journal of the London Mathematical Society",
    "volume": "s1-34",
    "issue": "3",
    "pages": "352",
    "doi": "10.1112/jlms/s1-34.3.352"
  }
]
```

Top-level `authors`, `license`, and `source` fields are not part of the contract.
Citation authors identify the cited work, not the writer of the entry. JSON also
has no `blocks`, `references`, or formalization fields: HTML is the single source
of block structure and human links. Git records history.

## Optional formal nodes

A human-only submission needs no Lean work. Leave `data-formal` absent for blocks
whose formalization has not started. After planning and human review, use:

```html
<section id="two-inclusions" data-kind="lemma" data-formal="example-subset-antisymm example-set-ext">
  <h2>Equality from two inclusions</h2>
  <p>Human statement and proof…</p>
</section>
```

Every listed ID must resolve to `formal/nodes/<id>.json`; IDs must be distinct.
Use `data-formal=""` only after reviewing that the block has nothing to formalize.
A definition can link to an existing Lean definition, and a question links its
answer or counterexample. A block may link to several nodes from different modules.

The badge next to the title shows concise derived progress. For linked blocks,
it expands into node IDs, each linked to a node page with status and Lean source.
Nodes and verification evidence belong to the [formal layer](../formal/README.md#formal-nodes),
not entry JSON. The [corpus README](../corpus/README.md#block-to-node-mapping)
explains aggregation and the review convention. Every block of sets-and-maps now
has a mapping: the notation-and-conventions block has nothing to formalize, and
the mathematical blocks link definitions, statements, examples, and question answers.
Node reviews are recorded with `review --accept --node <id>` or
`review --accept --nodes-from-entry <id>`; neither changes editorial status.
Use `--retract` instead of `--accept` to withdraw approval for the same selection.
See the [formal README](../formal/README.md) for the current node inventory and
verification workflow. Statement writing and proving remain separate measurement
tasks.

## HTML, equations, and tables

Use ordinary HTML fragments with explicitly closed elements. Each top-level
mathematical block is a section with one direct `h2` heading:

```html
<section id="translation" data-kind="definition">
  <h2>Translation</h2>
  <p>Translate by \(x\mapsto x+b\).</p>
</section>
```

Supported kinds are `definition`, `lemma`, `theorem`, and `question`. Display
numbers follow source order separately for each kind. The application provides
the page shell, contents, numbered headings, badges, and navigation. Use
`<details class="question-answer">` for collapsible answers.

These labels have the same meaning across the library: a definition fixes a term
or symbol, a theorem states a proved result, and a lemma is a result used in another
argument. A question poses a problem; its answer may contain a proof or a
counterexample. Do not repeat this glossary in individual entries.

Inline math uses `\(...\)`; display math uses `\[...\]`. HTML entities such as
`&lt;` and `&amp;` preserve less-than signs and LaTeX alignment separators. Aligned
expressions, arrays, matrices, fractions, and cases are rendered by self-hosted
KaTeX. Its [support table](https://katex.org/docs/support_table.html) describes the
supported LaTeX subset; this is not a full LaTeX document processor.

Labelled display equations are automatically numbered across the entry:

```html
<div class="math-display">\[ |A|\leq |A+B|. \label{eq:left-bound} \]</div>
<p>Now use \eqref{eq:left-bound}.</p>
```

The source renderer resolves `\label` and `\eqref`, which KaTeX itself does not
support. Use one label in one plain `math-display` element. Do not combine it with
an explicit `\tag`; the renderer generates the tag. Labels must be unique, and
missing references fail validation. Forward references work. Prose references and
standalone `\(\eqref{...}\)` become clickable `(1)` links. References embedded in a
larger formula become the parenthesized number within that formula. Equation
references are local to the entry and need no JSON record.

Give each table a stable ID and exactly one caption. Tables are numbered
**Table 1**, **Table 2**, … in source order within each entry, separately from
figures and equations. Write the caption without its number:

```html
<table id="addition-table">
  <caption>A small addition table</caption>
  <thead><tr><th scope="col">\(a\)</th><th scope="col">\(a+1\)</th></tr></thead>
  <tbody><tr><td>\(0\)</td><td>\(1\)</td></tr></tbody>
</table>
<p>The values in <a href="#addition-table"></a> illustrate addition by one.</p>
```

The empty reference becomes **Table 1**, including when it precedes the table.
Explicit link text and inline formatting are preserved; prefer empty table links
for automatic numbering. References are local to the entry and provide a return
link to the citing block, reopening an answer when needed. Missing targets,
duplicate IDs, and missing or multiple captions fail validation.

Tables receive a keyboard-focusable scrolling container, keeping wide tables
inside the reading column. Math works in cells and captions. The first example
in `corpus/backup/` contains a table and a labelled equation as rendering baselines.

## Figures

Give each figure a stable ID and one caption. The reader inserts **Figure 1**,
**Figure 2**, … in source order; do not write a number in the source:

```html
<figure id="map-picture" class="proof-figure">
  <div class="figure-image">
    <img src="assets/map.svg" alt="A map from three inputs to two outputs" width="720" height="300">
  </div>
  <figcaption>Every input has one output.</figcaption>
</figure>
<p>The map in <a href="#map-picture"></a> misses one element of its codomain.</p>
```

The empty link becomes **Figure 1** automatically, including in forward references.
Non-empty link text is preserved, but prefer empty local figure references so their
numbers stay current. Do not use "Figure" as placeholder text or hardcode a number.
A missing target fails validation. Figure references stay within the entry and
need no separate JSON record. They provide
a return link to the citing block, just like mathematical references.

## Links, assets, and reading order

Reference another entry by its stable ID and the target block ID, using
`href="entry-id#block-id"`. Same-entry references use `href="#block-id"` or a local
figure, table, or equation anchor. Entry references are resolved through the catalog when
rendering; do not include area paths, `../`, `entry.html`, or reader URLs in source
references. Unknown entry IDs and missing blocks fail validation.

```html
<a href="#nonempty-triple-sumset"></a>
<a href="thm-sumset-lower-bound#sumset-lower-bound">Sumset lower bound</a>
<img src="assets/figure.svg" alt="A translation injection" width="720" height="280">
<a href="assets/supplement.pdf">Supplement</a>
```

Non-empty link text and inline formatting are preserved. Only empty or whitespace-only
links receive generated labels: local mathematical links show the block kind and number,
local figure/table links show their number, and cross-entry links show the target heading.
Prefer empty same-entry links for automatic
numbering and explicit cross-entry text that fits the sentence, such as
`<a href="sets-and-maps#pairs-and-relations">binary relation</a>`.
Both kinds record the source block for the return link. IDs stay fixed when titles
or categories change. The renderer currently generates `/entries/<id>/` URLs, so
moving an entry between subareas needs no edits to references.
Direct visits have no top back button. Following a block reference, including one
within the same entry, or a figure/table reference shows the sticky return bar;
bottom navigation remains available in either case.

Only active entry `assets/` directories are registered with Django's static-file system.
`collectstatic` includes them without exposing source HTML/JSON. Restart the server
when adding a new asset directory; edits to existing corpus files invalidate the
catalog cache automatically. `corpus/reading-order.json` controls category order
and “Next entry”, with each entry listed once in its primary area. Additional area
memberships are stored but the current reader lists entries by primary area.

Keep inactive examples in `corpus/backup/`, outside `entries/`. They are not served,
validated, or included in formalization checks. `taxonomy_complete.json` is a
reference copy; only `taxonomy.json` controls browsing and area validation.

## Formal nodes and checks

Local nodes name a `Lemmatheca.*` module; mathlib nodes name a `Mathlib.*` module.
The source path is inferred from that module. Each node needs a concise plain-text
description stating its theorem or describing its defined object, including the
necessary hypotheses and domains. The node page renders this description's math
above the checked signature, with expandable proof prerequisites and source.
Description edits change the correspondence approval hash immediately, while
preserving Lean evidence. See the [node schema](../formal/README.md#formal-nodes).

The source browser shows the full escaped source, line anchors, and a highlighted
declaration line. Clicking a line link also opens the source browser. Current check
reports supply the checked signature and Lean's source locations, including
anonymous instances. The defining module may differ from the node's import module,
including a bundled Lean module. Generated declarations may have a differently
named source origin; use the checked signature to identify the actual target.
Without current evidence, the reader falls back to inferring lines for ordinary
named declarations; generated declarations may then have no line. Node links preserve
a return to the referring block and reopen question answers when appropriate.

Source is displayed on the node page; there is no separate file viewer.
A file alone has no verification status. Missing pinned mathlib sources
have a GitHub fallback when registered by a node. Missing local sources invalidate
affected module evidence and show a missing-source message. No Lean process runs
while serving a page.

```sh
uv run python app/manage.py check_formalizations
uv run python app/manage.py validate_corpus
uv run python app/manage.py test catalog
```

The checker reads nodes independently of entries, reuses current module records,
builds stale modules, checks declarations and transitive axioms, and writes
`formal/checks/nodes.json`. Evidence covers each module's transitive local imports
and a shared mathlib/Lake-package revision fingerprint. Installed packages are assumed
immutable; changing their revision or the environment pins invalidates checks using
that environment. Unrelated local edits leave it intact. Failed modules do not discard other successful
checks, though the command exits with an error.
A declaration using `sorry`, including through another theorem, remains pending.
An empty registry skips Lean; the current registry covers the two formalized entries.
Ordered sets awaits formal bindings. See
[verification and review](verification-and-review.md) for evidence and limitations.

The corpus contains trusted repository-owned HTML, parsed as content rather than
executed as Django templates. This parser is not an upload sanitizer. Public
submissions, full proof-dependency extraction, and autonomous proving remain
future work. The formal API is read-only.
