# Mathematical corpus

Entries, nodes, and navigation are repository files. The Django app reads them
directly. Independent reviews are reported in the task discussion or a pull
request, without approval fields or an editorial status in the corpus.

The [exposition contract](#exposition-and-formalization) defines what belongs in
entry blocks and how thoroughly their mathematics must be explained.

## Layout and navigation

```text
corpus/
  entries/<entry-id>/
    entry.json
    entry.html
    assets/                 # Optional figures and supplementary files
  nodes/<node-id>.json
  taxonomy.json
  reading_order.json
  index.json                # Generated, committed authoring index
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
In an [area pipeline](../CONTRIBUTING.md#running-an-area-pipeline), the entry agent
owns the step-2 integration assessment. The root applies shared edits to consuming
entries, reading order and registries and identifies the applied files/blocks
before assigning step 3. Later changes need focused rereview; proposed edits alone
do not establish that integration was reviewed.

`taxonomy.json` defines areas with `id`, `title`, `parent`, and `description`.
`reading_order.json` maps primary area IDs to ordered entry-ID lists under `areas`.
Add each entry once to its primary area's list. This index controls listings,
navigation counts and the next-entry link. The validator rejects missing,
duplicated, unlisted, or incorrectly assigned entries.
Every parent must exist, and the area hierarchy must be acyclic.
Reader area listings use the primary-area index. Authoring API area filters also
match `additional_areas`.
Reading order is local to each area; follow linked cross-area prerequisites before
continuing when an entry needs material from another area.

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
for the arguments and questions. Unless the user specifies otherwise, normally
target about 30–40 minutes. A cohesive topic may use up to about 50 minutes when
splitting would hurt the exposition; 50 is an allowance, not a default. Split or
narrow material that needs substantially more space rather than rushing its
arguments or understating the estimate. Existing entries are not subject to a
new hard length limit.

`summary` is the short listing description;
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

Corpus-wide aggregate totals and history are stored solely in
`corpus/statistics.json`. The [statistics workflow](../.github/workflows/statistics.yml)
writes it after pushes to `main`, using saved metadata and Git
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
and refresh the derived data required by that source-register maintenance using
`build --no-lean`; authored entry/node fields and Lean sources remain read-only.
In a coordinated batch, entry agents and delegated reviewers send shared record
changes to the root unless exclusive ownership was assigned. The root applies
shared changes and refreshes catalogs at a coordinated checkpoint or final build;
workers do not run competing writing builds.
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

After record changes, run `uv run python app/manage.py build --no-lean`.
It validates the records and their relationships and refreshes the committed
catalogs with the other derived data. For read-only review,
`build --no-lean --check` tolerates absent or stale catalogs. See the
[shared build modes](../CONTRIBUTING.md#validation-and-submission).
The generated, committed `corpus/index.json` is a separate authoring index.
Do not maintain a second Markdown copy of these registries.

## Exposition and formalization

### Rigorous mathematical blocks

Only rigorous mathematical content belongs in the entry body. Every block must
define a mathematical object, state and justify a result, or pose a precise
mathematical question with a justified answer. Use the supported kinds according
to that purpose:

| Kind | Required mathematical content |
| --- | --- |
| `definition` | Clearly identified terms in bold, with precise objects, domains, notation and conventions; justify existence or well-definedness where needed. |
| `lemma`, `theorem` | A clear statement before the proof, identifying the hypotheses and conclusion, supported by a proof or precise links to established results. |
| `question` | A genuine mathematical problem and a justified answer, construction or counterexample, normally in the collapsible answer. |

Every definition block must identify what it defines. Mark each newly defined
term with `<strong>` at its defining occurrence in the body, for example
`a <strong>singleton</strong> is a set with exactly one element`. Bold each term
when several notions are introduced; one unrelated bold phrase or the block's
heading does not suffice. Italics alone do not mark a defined term under this
convention. For a named construction or notation, give its descriptive name in
bold and its precise defining rule. If a block defines nothing, merge it into the
mathematical block it supports or use the appropriate result/question kind;
do not invent a term merely to add bold text.

Every lemma and theorem must have a recognizable statement in the body before
its proof. Identify the objects, assumptions, quantifiers and claimed conclusions,
using explicit local hypotheses or precise references to standing assumptions.
A reader arriving through a block reference must be able to locate the result
without reconstructing it from the heading, proof or an informal plan. State all
distinct conclusions and specify any claimed witness, map or construction. Use
ordinary paragraphs and displays for supporting results; statement boxes remain
reserved for main results under the [emphasis rules](#html-and-references).

Worked examples belong within the appropriate kind above; `example` is not a
separate block kind. State the assumptions and explain the calculation or argument
that establishes the example.

Use clear explanatory prose within these blocks to introduce notation, explain a
construction, clarify a proof step or connect a result to its examples. Intuition
may accompany an argument but cannot replace its justification. Definitions and
results may build on earlier material through precise references; they need not
repeat established proofs.

Put general motivation and an accessible overview in the
[abstract](#entry-metadata). Do not create blocks devoted solely to motivation,
reading roadmaps, historical context, source surveys, editorial commentary or Lean
implementation status. A rhetorical question does not turn such a passage into a
mathematical question block. Keep development plans in reference planning and
review findings in their handoffs; do not insert narrative-only paragraphs between
blocks to bypass this content rule.

Human rigor is required whether formal mappings are absent, empty, unfinished or
verified. A verification badge does not supply a missing argument, and an empty
`data-formal` mapping does not permit a block without mathematical content.

### Exposition depth and formalization

Give substantive constructions enough space to reconstruct their arguments.
For an internal algorithm, state its defining recurrence, the induction predicate
with its parameters, the invariant, and the required syntax or freshness
conditions. Work through a representative case and explain how the common
argument handles the remaining cases. Uniform totality or numerical correctness
alone does not justify additional algebraic or proof-preservation identities.
Routine Lean reindexing, bookkeeping and repeated field calculations need no
separate prose; the mathematical reasoning they implement must still be clear.

If an added entry has much more formal code than human text, check for compressed
or missing constructions, intermediate results, invariants and proof arguments.
Explain that substantive mathematics locally or through links to earlier entries.
When fuller treatment would exceed the entry's reading-time scope, split the
material at mathematical boundaries into coherent entries. Update prerequisites,
reading order and references, and review the affected exposition and mappings
through the pipeline. Code volume is a diagnostic, not a fixed numerical threshold;
padding prose or removing necessary formal code does not repair an exposition gap.

Material may be developed in more than one area when different perspectives help
readers. Follow the [area-fit policy](../CONTRIBUTING.md#area-fit-and-continuity)
and reuse suitable formal nodes and Lean declarations even when explanations differ.

## HTML and references

Use trusted HTML fragments with explicitly closed elements. Every top-level block
is a `section` with a stable `id`, a `data-kind`, and one direct, nonempty `h2`.
The `h2` contains plain text (including math notation), without attributes or
nested markup, since the reader generates the heading and its anchor:

```html
<section id="translation" data-kind="definition">
  <h2>Translation</h2>
  <p>For \(b\in\mathbb R\), the <strong>translation by \(b\)</strong> is the map
    \(T_b:\mathbb R\to\mathbb R\) given by \(T_b(x)=x+b\).</p>
</section>
```

Use the [mathematical block kinds](#rigorous-mathematical-blocks) above. The reader
generates numbering separately for each kind, as well as headings, the contents
sidebar, badges, and navigation. Do not include a document shell or Django template
instructions in the entry. The parser handles repository-owned HTML; it is not an
upload sanitizer.

Reserve accent green blocks (`class="statement-box"`) for the entry's main results.
Select the central conclusions rather than boxing every theorem or lemma. Include
the result's hypotheses and conclusion inside the box; keep definitions, supporting
lemmas, routine facts, examples, questions, proof steps, and proofs outside it.

Put each proof in its own `<div class="proof">`. The reader's stylesheet
automatically adds the italic “Proof” label and a closing square:

```html
<div class="proof">
  <p>The argument begins here.</p>
  <p>This establishes the conclusion.</p>
</div>
```

Keep the statement before the proof container and include the whole argument
inside it. A section may contain several separate proofs, but proof containers
must not nest or be empty. The final direct child must be a nonempty concluding
paragraph. If an argument ends with a list or display, add a concluding paragraph
after it so that the square follows text outside scrollable mathematics.

Do not write labels, squares, `proof-label`/`qed` elements or spacing for these
markers in the HTML. CSS supplies both markers, including the space before the
green square. The square follows the concluding text in normal inline flow; it
must not float, overflow its container or overlap following content.
Check long conclusions and proofs ending in lists or displays at desktop and
phone widths. A result justified only by a precise reference needs no empty proof
container.

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
Review the human mathematics and description-to-declaration correspondence
separately, following the independent-review rules. A passing Lean check does not
establish that the intended statement was formalized.

Use the [shared build modes and check matrix](../CONTRIBUTING.md#validation-and-submission)
from the repository root. `build --no-lean --check` validates canonical inputs
without writing, running Lean, or requiring up-to-date derived data. It checks
metadata, citations, HTML structure, anchors and equations, assets, block links,
bindings, dependency and area cycles, reading-order listings, and source/planning
records.
Entry references may be cyclic; node hints and area parents may not. Unknown
metadata fields and excessively nested HTML are rejected. Missing mappings,
unbound nodes, and absent generated summaries/signatures remain valid. Structural
checks do not establish declaration existence or current proof validity. Installed Lean
source availability is checked only with `--check-sources`.

Prerequisite direction, mathematical reading-order coherence and Lean module
ownership require the root's planning and integration review; structural
validation does not establish them.

Finish authored corpus edits other than statistics-only updates with the writing
`build --no-lean`, and commit changed generated data, including `corpus/index.json`.
This includes prose-only and whitespace-only changes. Use the full `build` for
changes to bindings, Lean declarations or proofs under the
[shared rules](../CONTRIBUTING.md#validation-and-submission). In an area pipeline,
the root also performs [index checkpoints](../CONTRIBUTING.md#index-checkpoints)
with corpus writes paused so agents can discover earlier additions. These no-Lean
refreshes do not replace the final full build after worker edits are frozen.
Inspect edited pages for mathematical
layout, links, hidden answers and figures. Corpus checks do not render pages or
establish that a formal statement matches its exposition. See the
[formal guide](formal.md#build-and-verification) for verification and the
[app guide](app.md) for serving and deployment.
