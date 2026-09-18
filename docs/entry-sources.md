# Writing entries

Each entry has a stable folder under `corpus/entries/<id>/` containing `entry.html`,
`entry.json`, and an optional `assets/` directory. Lean sources live under
`formal/Lemmatheca/`; existing mathlib declarations can be used directly.

## Metadata

The required entry fields are exactly:

```text
id, title, authors, license, primary_area, additional_areas,
status, reading_time, summary, abstract, blocks
```

`authors` is a list of display names, for example `["Codex (AI)"]`. `license` is an
SPDX identifier, such as `Apache-2.0`. `status` is the editorial state, currently
`draft` for both examples; it is independent of formalization. `reading_time` is
an integer number of minutes. Titles, authors, linked licenses, and editorial
status appear on the entry page.

If the human material comes from another source, add the optional provenance field:

```json
"source": {
  "title": "Original lecture notes",
  "url": "https://example.org/notes"
}
```

This produces a visible source credit. Omit it for original material. This entry
source is distinct from a formalization's Lean source path. A source citation does
not change the entry's license or grant permission to reproduce material.

`blocks` is keyed by the stable IDs in the HTML. Every block has exactly
`formalization` and `references`:

```json
"nonempty-sumset": {
  "formalization": {
    "status": "complete",
    "declaration": "Finset.Nonempty.add",
    "source": "Mathlib/Algebra/Group/Pointwise/Finset/Basic.lean",
    "verification_report": "formal/checks/sumsets.json",
    "module": "Mathlib.Algebra.Group.Pointwise.Finset.Basic",
    "unformalized_dependencies": []
  },
  "references": []
}
```

A reference has only `entry_id` and `block_id`. Its target must exist and match a
mathematical citation in the HTML. There are no entry, proof, or reference version
fields; Git records change history. Block kinds, titles, and order live in HTML.

Formalization statuses are `not_started`, `partial`, and `complete`. Unfinished
bindings may use `null` for missing declaration, module, source, and report fields.
A complete binding requires all four, its declaration must occur in a passing
report, and `unformalized_dependencies` must be empty. A nonempty list with
`status: "complete"` is a validation error, including when regenerating reports.

`unformalized_dependencies` links to Lean statements whose proofs are unfinished.
Each item has exactly `declaration`, `module`, and `source`, identifying a local
Lean declaration with the same module/path conventions as a block binding. Names
must be unique within the list. Free-text statements are no longer accepted.
The website links each declaration to the shared Lean file viewer with a return
link to the citing block. Completed formalizations use the same viewer. No Lean
compiler runs during page requests.

For a partial proof plan without a main Lean declaration yet, use:

```json
"formalization": {
  "status": "partial",
  "declaration": null,
  "source": null,
  "verification_report": null,
  "module": null,
  "unformalized_dependencies": [
    {
      "declaration": "Lemmatheca.Pending.increasing_list_length_le_card",
      "module": "Lemmatheca.Combinatorics.Additive.Pending.IncreasingListCard",
      "source": "formal/Lemmatheca/Combinatorics/Additive/Pending/IncreasingListCard.lean"
    }
  ]
}
```

The example helper has an explicit type and an unfinished proof:

```lean
theorem increasing_list_length_le_card (S : Finset ℤ) (chain : List ℤ)
    (hincreasing : chain.Pairwise (· < ·))
    (hmem : ∀ z ∈ chain, z ∈ S) :
    chain.length ≤ S.card := by
  sorry
```

Keep pending helpers in dedicated source files so that a link shows just the
relevant statement and its imports. The examples use `Additive/Pending/` modules,
which are not imported by the main library. The check command builds them
explicitly and records their axiom dependencies separately. `sorry` permits Lean
to check the statement's type; it does not prove the statement.

An existing, checked mathlib result can discharge an obligation. It does not
belong on this list merely because its proof lives outside Lemmatheca. The list is
author-maintained, not automatically extracted from a proof term.

The list can also accompany `not_started`; a nonempty list always prevents
completion, but an empty list alone never establishes it. Removing obligations
still requires a complete binding and a passing check before setting `complete`.
The integer bound in **Adding three sets** demonstrates a partial block with two
pending statements with `sorry`; the main theorem has no complete Lean proof.

The entry badge is derived from **all** blocks, including definitions and question
answers: all complete → complete; all not started → not started; every other
combination → partial. A question's status describes its answer or counterexample.
A complete formalization does not imply editorial publication or human approval.

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
references are local to the entry; they do not belong in block `references`.

Ordinary tables, captions, headers, lists, emphasis, and images are supported:

```html
<table>
  <caption>A small addition table</caption>
  <thead><tr><th scope="col">\(a\)</th><th scope="col">\(a+1\)</th></tr></thead>
  <tbody><tr><td>\(0\)</td><td>\(1\)</td></tr></tbody>
</table>
```

Tables receive a keyboard-focusable scrolling container, keeping wide tables
inside the reading column. Math works in cells and captions. The first example
contains a real table and a labelled equation as rendering baselines.

## Links, assets, and reading order

```html
<a href="#nonempty-triple-sumset">Nonempty triple sumsets</a>
<a href="../thm-sumset-lower-bound/entry.html#sumset-lower-bound">Sumset lower bound</a>
<img src="assets/figure.svg" alt="A translation injection" width="720" height="280">
<a href="assets/supplement.pdf">Supplement</a>
```

Local mathematical links receive local numbers; cross-entry links show the result
name and record the source block for the return link. IDs stay fixed when titles
or categories change. Reader URLs use `/entries/<id>/`.

Only entry `assets/` directories are registered with Django's static-file system.
`collectstatic` includes them without exposing source HTML/JSON. Restart the server
when adding a new asset directory; edits to existing corpus files invalidate the
catalog cache automatically. `corpus/reading-order.json` controls category order
and “Next entry”, with each entry listed once in its primary area. Additional area
memberships are stored but the current reader lists entries by primary area.

## Lean bindings and checks

For local code, use a `Lemmatheca.*` module and a repository-relative source such as
`formal/Lemmatheca/Combinatorics/Additive/FiniteSumsets.lean`. For existing mathlib
code, use a `Mathlib.*` module and a mathlib-relative source such as the example
above. No local wrapper proof is required. Source links open the general viewer
at `/lean/<source>/`, using the metadata's source path unchanged. Examples:

- `/lean/formal/Lemmatheca/Combinatorics/Additive/FiniteSumsets.lean/`
- `/lean/Mathlib/Algebra/Group/Pointwise/Finset/Basic.lean/`

Any `.lean` file under the local `formal/` tree (excluding hidden directories) or
the pinned `Mathlib/` tree can be viewed without an entry binding. The viewer
displays the whole file. Entry-generated links add `from`, `at`, and `declaration`
parameters; a matching binding supplies that declaration's status and return link.
Standalone views do not assign a verification status to the file. The viewer also
links mathlib source to the exact commit pinned in `formal/lake-manifest.json`.

The ignored mathlib checkout is optional on a read-only web server. For complete
mathlib bindings, catalog validation checks the declaration and source path
against the committed verification report. If a referenced mathlib source is not
installed, its viewer offers the pinned GitHub link. Local Lemmatheca files are
still required. The verification command itself compiles the pinned dependencies
and requires the source files before writing a new report.

```sh
uv run python app/manage.py check_formalizations
uv run python app/manage.py validate_corpus
uv run python app/manage.py test catalog
```

`check_formalizations` builds the Lean project, imports the bound modules, checks
every complete declaration and its transitive axioms. It also type-checks pending
dependencies, recording them separately with their axioms (including `sorryAx`). It writes the reports named in the metadata, with source hashes
and the pinned environment. Incomplete blocks are not certified or promoted. Rerun after
changing bound code, metadata, or mathematical content. A report is a local
check record, not a maintainer approval or proof of agreement with the human text.

The corpus contains trusted repository-owned HTML, parsed as content rather than
executed as Django templates. This parser is not an upload sanitizer. Public
submissions, full dependency extraction, and the public AI API remain future work.
