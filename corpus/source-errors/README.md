# Source errors

This register records confirmed mathematical defects in external publications
used by the corpus. Start with the [publication and finding catalog](index.json),
select relevant IDs, then open `sources/<id>.json` or `findings/<id>.json`.
The [registry workflow](../../docs/corpus.md#navigating-source-and-planning-records)
describes filtered API queries and record fields.

## Scope and classification

Coverage includes publications cited in entries' `based_on` fields and the named
results those citations identify, together with explicitly scoped supporting,
adjacent and entry- or area-planning passages. Record dates and access limits
with each reviewed scope. Group duplicate URLs and chapter extracts of the same
edition without merging different editions or source versions.

Prioritize **serious defects**: false statements, missing necessary hypotheses,
invalid constructions and deductions that fail as written. Each finding needs
mathematical evidence and a checked repair. **Local slips** have lower priority:
a formula or index is wrong, but a local correction preserves the underlying
argument. Missing explanation, valid compression, different conventions and
uncertainty are not confirmed errors.

A no-defect outcome applies only to the inspected passages. Some planning
reviews inspect metadata, contents or statements rather than proofs; distinguish
those outcomes. This register is not a line-by-line audit of entire books, a
verification of every exercise solution, or a claim that a publication's remaining
content is error-free. Citation metadata mistakes are corpus issues, not source
errors. Page numbers mean printed pages unless marked otherwise.

An error remains present in the inspected source version unless an upstream
correction is explicitly recorded. **Already handled in the corpus** means our
entry uses a correct version; it does not mean the source was corrected.
Distinguish adjacent inspected defects from arguments actually used by an entry.

## Maintenance

Follow the [source-error contract](../../docs/corpus.md#source-errors). Before
reusing a cited argument, read its existing records. Save new confirmed findings
and extensions of checked coverage during the same pipeline step, rather than
leaving them only in chat or a pull request. Keep stable finding IDs, exact source
versions and locations, evidence, repairs and actual consuming entry/block links.
Keep unsupported suspicions in the task handoff, clearly marked as uncertain.

When a publication changes, record the inspected revision. Preserve previous
findings and add the upstream resolution rather than deleting their history.
Keep every check date attached to its reviewed scope when extending coverage.
Entry editorial issues and Lean correspondence findings belong in their own
review handoffs.

Markdown links inside JSON records resolve relative to `corpus/`; links in this
README resolve relative to this directory. After record edits, run
`uv run python app/manage.py build --no-lean` under the
[shared publication rules](../../CONTRIBUTING.md#validation-and-submission).
The build validates records and refreshes the catalog. The README is
documentation, not an input to the registry API or build.
