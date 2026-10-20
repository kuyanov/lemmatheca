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
  reference-planning/
    index.json             # Compact navigation by entry, area, kind, and URL
    records/<id>.json       # One focused pending reference or development record
    policy.json            # Shared planning scope and interpretation
  source-errors/
    index.json             # Compact navigation by entry and publication URL
    sources/<id>.json       # One publication/version and its scoped reviews
    findings/<id>.json      # One serious defect or local slip, with stable ID
    policy.json            # Register scope, classification, and maintenance
  statistics.json           # Generated home-page counts and change history
```

Entry and node file and directory names must match their record's `id`. Their IDs
start with a letter or digit and use letters, digits, hyphens, or underscores. Keep
them stable when changing titles or subject categories.

[Reference planning](../corpus/reference-planning/index.json) records future
links and expansion context. The `upcoming-reference` kind is one logical
collection using current consuming entry/block IDs. Separate kinds hold
existing-target integration, future-entry plans, correspondences to establish,
source plans, and deferred extensions. These authoring records are separate from
entry and node metadata.
Keep every record limited to outstanding reference or development work. For new
or changed mathematical coverage, step 2 owns
[reference integration](../CONTRIBUTING.md#reference-integration): inspect existing
consuming entries across areas, add useful links, and remove related fulfilled
tasks, completed roadmap rows and outlines, and completion notes. Step 3 reviews
the entry's references and relevant integration changes without repeating the
broad discovery search; steps 4–6 do not own this audit. Wording and layout edits
check affected links only. Retain only the unfulfilled part of a mixed task. Existing
coverage and source details may remain as prerequisites or supporting context for
a concrete future task; completed source-review records belong in `source-errors/sources/`.

`taxonomy.json` defines areas with `id`, `title`, `parent`, and `description`.
`area_entries.json` maps primary area IDs to ordered entry-ID lists under `areas`.
Add each entry once to its primary area's list. This index controls listings,
navigation counts and the next-entry link. The validator rejects missing,
duplicated, unlisted, or incorrectly assigned entries.
Every parent must exist, and the area hierarchy must be acyclic.
Reader area listings use the primary-area index. Authoring API area filters also
match `additional_areas`.

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
HTML or loading nodes. Refresh this data at delivery after adding entries or
changing block inventory, mappings, node bindings, or Lean declarations/proofs,
following the [shared build rules](../CONTRIBUTING.md#validation-and-submission).
Include the refreshed entry and node JSON with the change. Failed checks or
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

[Source errors](../corpus/source-errors/index.json) is the permanent register of confirmed
mathematical defects in external books, papers, and notes used by the corpus.
Prioritize false statements, missing necessary hypotheses, invalid constructions,
and deductions that fail as written. Distinguish these from local mathematical
slips whose arguments survive. Do not register missing explanations, legitimate
compression, different conventions, or uncertainty as confirmed errors.

Whenever inspecting a source, consult its existing records and maintain its
source record: publication and edition or revision, URLs, checked passages, consuming
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

Reuse applicable source assessments; moving to another pipeline stage does not
require inspecting unchanged source passages again or duplicating their coverage
records. All six steps maintain this register when actual source checks reveal new
defects or extend reviewed coverage. Steps 1, 3, and 5 may update these records
only; their entry, node, proof, and generated-data work remains read-only.
Save confirmed findings before the handoff rather than leaving them solely in a
chat or pull request. Entry editorial findings and formal correspondence findings
stay in their review handoffs. This register has no approval flags or effect on
verification badges, and its updates require catalog refresh and record/link checks,
not a Lean build.

## Navigating source and planning records

Read relevant records rather than loading either collection in full. Each has a
stable ID and predictable path. Compact `index.json` catalogs contain IDs and
lookup relationships, without copying review or planning prose. Source catalogs
provide `by_url`, `by_entry`, and finding-to-source relationships. Planning catalogs
provide `by_entry`, `by_area`, `by_kind`, and `by_url`; `by_entry` includes planned
entry IDs as well as current consumers.

With the reader running, use the
[source and planning API](app.md#source-and-planning-api):

```sh
curl 'http://127.0.0.1:8000/api/source-errors/sources/?entry_id=first-incompleteness'
curl 'http://127.0.0.1:8000/api/source-errors/findings/?source_id=avigad-computability-incompleteness&severity=serious'
curl 'http://127.0.0.1:8000/api/source-errors/findings/AVIGAD-CI-02/'
curl 'http://127.0.0.1:8000/api/reference-planning/?entry_id=second-incompleteness'
curl 'http://127.0.0.1:8000/api/reference-planning/?area=mathematical-logic&kind=upcoming-reference'
```

Lists return compact summaries; fetch selected IDs for full reviews, evidence,
repairs or plans. Publication lookup ignores URL fragments such as `#page=167`;
aliases and different inspected editions remain explicitly identified. Prioritize
`serious` findings; inspect `local` slips only when relevant.

Without the API, filter the compact catalog and open the selected files:

```python
import json
from pathlib import Path

root = Path("corpus/reference-planning")
catalog = json.loads((root / "index.json").read_text())
for record_id in catalog["by_entry"].get("second-incompleteness", []):
    print(root / "records" / f"{record_id}.json")
```

Source records hold `publication`, `urls`, `reviews`, `entry_refs`, and
`finding_ids`. Reviews preserve checked passages, consumer context, outcomes,
dates and access limits. Historical reviews with several scoped dates retain
those qualifications; migration does not create a new whole-publication audit.
Findings hold `source_ids`, `severity`, `title`, `details`, `entry_refs`, and
`related_findings`; details retain the mathematical evidence and repair.

Planning records share `id`, `kind`, `title`, `areas`, `entry_refs`, and `urls`,
plus focused fields for their task or source plan. `entry_refs` names existing
entries or blocks; `planned_entry_ids` names future entries without inventing
anchors. Area tags may identify future areas not yet in the taxonomy. Markdown
links in record strings resolve relative to `corpus/`, independent of file depth.

After record changes, regenerate the catalogs and validate:

```sh
uv run python app/manage.py index_authoring_records
uv run python app/manage.py validate_corpus
```

Catalog generation writes only changed catalogs. Validation checks shapes, IDs,
source/finding relationships, existing entry/block references and exact catalog
contents. Catalogs are committed navigation files; the entry/node index under
`artifacts/` remains a separate disposable cache. Neither command invokes Lean.
Do not maintain a second Markdown copy of these registries.

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

Introduce proofs with the shared italic label, on its own paragraph:

```html
<p class="proof-label">Proof</p>
<p>The argument begins here.</p>
```

Use this markup consistently; do not use bold or inline `Proof.` labels.
The reader's stylesheet supplies the italic styling.

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
Enclose each display formula in a `div` or `p` with class `math-display`, including
unlabelled formulas, statement boxes, and question answers. This provides the
formula's scrolling container. Keep surrounding prose in separate paragraphs.

Lay out display formulas to fit the normal desktop content column without
horizontal scrolling. Split independent claims into separate displays when a
combined row would overflow; do not shrink the font to make it fit.
Keep a single equation, implication, or equivalence on one horizontal line when
it reads naturally; in
particular, write `P(...) \Longleftrightarrow Q(...)` together rather than stacking
the two sides with the relation on a line of its own. Do not insert line breaks
solely to make a formula fit a phone screen. Horizontal scrolling within a
`math-display` is acceptable on narrow screens, including inside statement boxes;
check that the entire formula is reachable without making the whole page scroll
sideways. Use multiple lines where the mathematics benefits from them, such as
aligned derivation steps, separate identities, cases, matrices, and proof trees.
Short chains of equalities or equivalences should also stay horizontal when they
read comfortably on desktop; having several steps alone does not justify wrapping.
The same applies to lists of identities: combine short items into compact rows
rather than giving every identity its own line. When auditing line breaks,
enumerate every explicit break, including those in aligned lists and derivations.
Keep structural breaks in cases, matrices, proof trees, and multiline subscripts;
justify other retained breaks by readability at the normal desktop column width.
Break an exceptionally long single statement at meaningful mathematical boundaries
when needed to fit the desktop column. Preserve readable font sizes and spacing.

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

Match diagrams to nearby figures and `app/static/css/site.css`: prefer SVG,
serif mathematical labels, muted green accents, thin lines, and subdued fills.
Use `class="proof-figure"` on a figure and `class="figure-image"` on its image
wrapper, with the caption directly inside the figure. Give images intrinsic width
and height. Check typography at normal desktop zoom: labels should be proportionate
to the surrounding text, with clear space around legends and notes. Use original
figures or establish the basis for reuse and credit their sources.

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
In node descriptions, enclose mathematical notation in `\(...\)` or `\[...\]`
and escape LaTeX backslashes for JSON. Check the rendered node page as well as
the entry; raw symbols and ASCII formulas outside these delimiters display as
ordinary text. See the [node-description contract](formal.md#formal-nodes).

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

By default, the validator checks the complete corpus without rendering HTML,
running Lean, or writing files. It reports the first failure with its file path. It validates
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

Add `--write-index` to publish the disposable structural index used by the
[authoring API](app.md#authoring-api), without invoking Lean. The index does not
copy entry prose or node metadata; API queries read those from the corpus, with
a bounded cache for parsed entry text. See the [index lifecycle](app.md#corpus-index)
for output paths, refresh rules, and memory limits. Ordinary reader pages and
direct-file reviews do not require this index.

After adding an entry or changing its block inventory, formal mappings, node
bindings, or Lean declarations and proofs, refresh generated data at delivery:

```sh
uv run python app/manage.py build
```

Use the [shared check and batching rules](../CONTRIBUTING.md#validation-and-submission)
for standalone handoffs and multi-stage tasks; do not repeat a successful build
without subsequent relevant changes or unresolved diagnostics.
The build checks declarations, parses entries, refreshes node data and entry-list
summaries, then regenerates the configured index. Prose or figure edits that preserve the block inventory and mappings
need corpus validation and a rendering check, without a proof rebuild. Run relevant
catalog tests when reader or build-tooling code changes, or to investigate a
rendering or integration failure. Inspect edited pages for mathematical layout,
working links, questions, and figures. CI checks that generated JSON matches the
committed files. See the [app guide](app.md) for serving and deployment.
