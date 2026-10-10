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
  reference-planning.md     # Upcoming references and expansion planning
  source-errors.md          # Confirmed source defects and review coverage
  statistics.json           # Generated home-page counts and change history
```

Entry and node file and directory names must match their record's `id`. Their IDs
start with a letter or digit and use letters, digits, hyphens, or underscores. Keep
them stable when changing titles or subject categories.

[Reference backlog and planning](../corpus/reference-planning.md) records future
links and expansion context. Its [upcoming-reference table](../corpus/reference-planning.md#upcoming-references)
uses current consuming entry/block IDs; existing-target integration, future-entry
plans, correspondences to establish, and deferred extensions belong in the other
sections of the same document. This authoring document is separate from entry,
node, and navigation metadata.

`taxonomy.json` defines areas with `id`, `title`, `parent`, and `description`.
`area_entries.json` maps primary area IDs to ordered entry-ID lists under `areas`.
Add each entry once to its primary area's list. This index controls listings,
navigation counts and the next-entry link. The validator rejects missing,
duplicated, unlisted, or incorrectly assigned entries.
Every parent must exist, and the area hierarchy must be acyclic.
`additional_areas` is metadata; current listings use the primary-area index.

## Entry metadata

Authors maintain these fields in `entry.json`:

```text
id, title, based_on, primary_area, additional_areas,
reading_time, summary, abstract
```

The entry's `title` must be plain text, with no LaTeX commands or math delimiters.
Describe mathematical notation in words in the title; put formulas in the entry
body.

`reading_time` is an estimated positive integer number of minutes, allowing time
for the arguments and questions. `summary` is the short listing description;
`abstract` introduces the entry on its own page. It should stand on its own for
readers new to the topic or who have not read the entry. Consult the cited sources'
explanations and motivating examples, then check the abstract against the entry's
actual scope and assumptions. Write original exposition and credit inspected
sources in `based_on`.

Begin with a concrete problem, example, or familiar fact that gives readers a
reason to follow the rigorous arguments. Use simple language and familiar
mathematical vocabulary, briefly explaining essential new terms; vague substitutes
for standard terms can make the prose harder to understand. Avoid notation that
requires the entry's definitions. Develop one connected paragraph, with each
sentence building on the previous one. Select a few central results, preserve
their necessary conditions, and explain their significance and relationships.
Avoid proof-technique inventories and section itineraries. Read the paragraph as
an introduction, checking that its objects, comparisons, and conclusions make
sense without consulting the entry.

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

The [statistics workflow](../.github/workflows/statistics.yml) writes
`corpus/statistics.json` after pushes to `main`, using saved metadata and Git
authors. Contribution branches should leave this file unchanged; the proof build
does not update it. Its schema is validated when present, without requiring
freshness during authoring.
Its `history` has four lists: `entries`, `nodes`, `areas`, and `contributors`.
Entry and node points pair the total and verified counts as
`{ "at": "…", "count": …, "verified": … }`; area and contributor points use
`{ "at": "…", "count": … }`. Timestamps are UTC. A point is added when either
count changes; unchanged refreshes add nothing. Validation checks chronological order,
changed counts, current endpoints, and verified totals. Existing snapshots without
history remain valid until the next statistics refresh fills it in.
See the [statistics guide](app.md#home-page-statistics) for Git backfill and contributor counting.

Block structure, human references, and formal-node mappings belong in HTML.

## Source errors

[Source errors](../corpus/source-errors.md) is the permanent register of confirmed
mathematical defects in external books, papers, and notes used by the corpus.
Prioritize false statements, missing necessary hypotheses, invalid constructions,
and deductions that fail as written. Distinguish these from local mathematical
slips whose arguments survive. Do not register missing explanations, legitimate
compression, different conventions, or uncertainty as confirmed errors.

Whenever inspecting a source, consult its existing records and maintain its
coverage row: publication and edition or revision, URL, checked passages, consuming
entries, check date, findings, and any access limits. Consolidate duplicate URLs
for the same publication without merging different editions. Record no defect
found only for the inspected scope; do not claim a whole-book audit.
Keep check dates attached to their actual scope; a new partial review does not
redate previously inspected passages.

Give each confirmed defect a stable ID and precise page, section, or theorem
location. Supply a counterexample or failed inference, a checked correction or
explicit unresolved status, and actual consuming `entry-id#block-id` links.
Distinguish a source still containing an error from a corpus entry already using
a repair. Identify adjacent inspected material that the entry does not use.
Preserve records when the upstream source is corrected, recording the new version
and resolution; never infer an upstream correction from our repaired exposition.

All six pipeline steps maintain this register when source checks reveal new
defects or extend reviewed coverage. Steps 1, 3, and 5 may update this document
only; their entry, node, proof, and generated-data work remains read-only.
Save confirmed findings before the handoff rather than leaving them solely in a
chat or pull request. Entry editorial findings and formal correspondence findings
stay in their review handoffs. This register has no approval flags or effect on
verification badges, and its updates require link checks, not a Lean build.

## HTML and references

Use trusted HTML fragments with explicitly closed elements. Every top-level block
is a `section` with a stable `id`, a `data-kind`, and one direct, nonempty `h2`.
The `h2` contains plain text (including math notation), without attributes or
nested markup, since the reader generates the heading and its anchor:

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

Reserve accent green blocks (`class="statement-box"`) for the entry's main results.
Select the central conclusions rather than boxing every theorem or lemma. Include
the result's hypotheses and conclusion inside the box; keep definitions, supporting
lemmas, routine facts, examples, questions, proof steps, and proofs outside it.

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
Node pages display Verified or Not verified, the mathematical description, Lean
declaration, dependencies, and source.

The [Lean guide](formal.md#formal-nodes) defines node records, descriptions,
bindings, and the distinction between proof-planning hints and actual Lean dependencies. Formal verification permits `propext`,
`Classical.choice`, and `Quot.sound` by default, without asserting their mathematical
necessity. Human ZF-only arguments and claims about weaker choice principles need
separate assessment; the Verified badge does not certify their axiom strength.

## Authoring and checks

Use the [contribution workflow](../CONTRIBUTING.md) and its per-step prompts.
Review the human mathematics and
the description-to-declaration correspondence separately on GitHub; a passing Lean
check does not establish that the intended statement was formalized.

From the repository root, at any stage of authoring:

```sh
uv run python app/manage.py validate_corpus
```

The validator checks the complete corpus without rendering HTML, running Lean, or
writing files. It reports the first failure with its file path. It validates
metadata types and IDs, citations, HTML structure, anchors and equations, local
assets, cross-entry block links, formal bindings, node dependency references and
cycles, area parents and
cycles, and the primary-area reading index. Entry links
may be cyclic; node dependency hints and area parents may not. Deeply nested HTML
is rejected before it can exhaust the reader's recursive renderer.

Missing `data-formal`, unbound nodes, and absent generated summaries/signatures are
valid. Existing generated data is checked for shape, not freshness, so this command
does not force a build during drafting. Unknown metadata fields are rejected to
catch typos. Lean bindings are checked for shape; declaration existence and proof
verification belong to `build`. For deployment, `validate_corpus --check-sources`
also checks that each bound module's local source is readable UTF-8, once per
module. This option needs installed sources but still does not invoke Lean.
Use `--corpus <directory>` to check a separate corpus.

After adding an entry or changing its block inventory, formal mappings, node
bindings, or Lean declarations and proofs, refresh generated data:

```sh
uv run python app/manage.py build
```

The build checks declarations, parses entries, and refreshes node data and entry-list
summaries. Prose or figure edits that preserve the block inventory and mappings
need corpus validation and a rendering check, without a proof rebuild. Run relevant
catalog tests when reader or build-tooling code changes, or to investigate a
rendering or integration failure. Inspect edited pages for mathematical layout,
working links, questions, and figures. CI checks that generated JSON matches the
committed files. See the [app guide](app.md) for serving and deployment.
