# Building the corpus

Run from the repository root:

```sh
uv run python app/manage.py build
```

`build` validates the corpus, checks its Lean declarations, and refreshes the
generated data used by the reader and authoring API. It is the single command for
these tasks; there is no separate validation command.

## What a normal build does

1. **Validate authored inputs.** Check JSON metadata, entry HTML and formulas,
   citations, assets, anchors, internal links, node bindings, dependency cycles,
   reading order, and source/planning records. Missing or stale generated data is
   allowed at this stage because the build will regenerate it.
2. **Run Lean.** Build `Lemmatheca` and all bound non-core modules, then inspect
   each registered declaration and its transitive kernel axioms. Compilation
   errors and missing declarations fail the command. Unfinished proofs or
   unsupported axioms produce `verified: false`; they do not by themselves fail
   the build. See the [verification rules](formal.md#build-and-verification).
3. **Prepare generated data.** Refresh node proof metadata, entry formalization
   summaries, source/planning catalogs, and the structural authoring index.
4. **Validate the proposed result, then save it.** Authored prose, descriptions,
   mathematical statements, and proof sources are not rewritten.

The generated outputs are:

| Output | Location | Git |
| --- | --- | --- |
| Node verification, declaration signatures, source lines, and defining modules | Generated fields in `corpus/nodes/*.json` | Commit with the inputs |
| Entry formalization summaries | `formalization` in each `entry.json` | Commit with the inputs |
| Source-error and reference-planning catalogs | `corpus/source-errors/index.json` and `corpus/reference-planning/index.json` | Commit with the records |
| Structural authoring index | `corpus/index.json` by default | Commit with the inputs |

Unchanged node/entry records and catalogs are left untouched. The structural
index is replaced on every writing build.

The index stores lookup relationships, with no `counts` field. Corpus-wide totals
and their history belong solely in `corpus/statistics.json`. Validation counts
printed by `build` are computed in memory, not saved in the index.

Corpus JSON and HTML use LF line endings so the index revision is consistent
across checkouts. If the generated index has a merge conflict, resolve its input
files first and regenerate it with the appropriate writing build: `build --no-lean`,
or full `build` when bindings, declarations, or proofs changed.

## Flags and combinations

The two main flags control different parts of the command:

- **`--no-lean`** skips Lean and reuses saved proof results. Missing results count
  as unverified. Nodes without a declaration are reset to unverified, with stale
  signatures and source lines removed. Saved results for bound nodes do not
  establish that edited declarations or bindings are still valid.
- **`--check`** publishes no corpus data. With Lean enabled, it regenerates data
  in memory and fails if saved node proof metadata, entry summaries, or authoring
  catalogs differ, or if the selected index is missing, invalid JSON, or differs
  from regeneration, including its revision. Combined with `--no-lean`, it stops
  after structural validation; it does **not** compare generated-data freshness.

In this table, `build` abbreviates `uv run python app/manage.py build`:

| Command | Lean | Result |
| --- | --- | --- |
| `build` | Run | Validate, regenerate, and save all outputs |
| `build --no-lean` | Skip | Validate and save derived data using saved proof results |
| `build --check` | Run | Validate and require saved generated data to match regeneration; save nothing to the corpus |
| `build --no-lean --check` | Skip | Validate authored inputs only; allow missing or stale generated data; save nothing |

For example, suppose a node is saved as verified but its proof now contains
`sorry`. A normal build saves `verified: false` and can succeed.
`build --check` instead fails because the saved result differs. After running
`build` and committing the refreshed data, the check can pass even with that node
unverified. **The check requires accurate saved results, not complete proofs for
every node.**

The full check requires a current saved index at the selected path. The structural
`build --no-lean --check` permits missing or stale generated outputs, including
the index. Lean-enabled commands may update local compiler caches even with
`--check`.

### Additional flags

| Flag | Effect |
| --- | --- |
| `--check-sources` | Also require each bound module's installed `.lean` source file to exist and be readable as UTF-8. Useful for source browsing. It does not run Lean or check proofs by itself, and can be combined with any mode. |
| `--index PATH` | Override the structural index output or checked path for this invocation. It does not change the reader's configured path or suppress other generated outputs. Full `--check` compares the index at this path; `--no-lean --check` only validates the destination. Check modes write no index. |

The default index path comes from `DJANGO_CORPUS_INDEX_PATH`, falling back to
`corpus/index.json`. Set that environment variable when both the reader and build
should use another path. Inside `corpus/`, only the reserved `corpus/index.json`
destination is allowed; other destinations must be outside the corpus. The default
`corpus/index.json` is generated and committed; a one-off override does not refresh
that file. See the [index lifecycle](app.md#corpus-index) for its contents and
caching behavior.

## Which command to use

| Task | Command |
| --- | --- |
| Finish corpus edits other than statistics-only updates | `build --no-lean`, or full `build` for formal changes |
| Quickly check authored inputs without changing files | `build --no-lean --check` |
| Validate a clean, CI-checked deployment without rewriting corpus data | `build --no-lean --check` |
| Finish changes to bindings, declarations, or proofs | `build` |
| Verify committed generated data in CI, including source-file availability | `build --check --check-sources` |
| Write the index elsewhere without rerunning Lean | `build --no-lean --index /tmp/corpus-index.json` |
| Check generated data against an index at another path | `build --check --index /tmp/corpus-index.json` |

Corpus finalization includes prose-only and whitespace-only edits: their raw
bytes affect the index revision. Commit changed generated files, including
`corpus/index.json`. For a multi-stage batch, one writing build at its final
mutating stage is sufficient; a read-only check does not replace it.

If a full check reports stale generated data, run `build`, inspect the changed
results and Lean diagnostics, and include the generated JSON changes with their
inputs. For required rendering, correspondence, and test checks, follow the
[contribution check matrix](../CONTRIBUTING.md#validation-and-submission).

## Failures and scope

Input validation, Lean checking, and validation of proposed outputs happen before
publication. Each output file is replaced atomically, but the complete save is
not a single filesystem transaction: an I/O failure during publication can leave
some files updated. Resolve the failure and rerun the build.

The command does not render pages, review the mathematics or its correspondence
with Lean, run the test suite, collect static assets, or restart the reader.
It validates the shape of `corpus/statistics.json` when present but does not
regenerate it. Statistics are excluded from the index revision, so statistics-only
updates do not require rebuilding the index or affect its full-check freshness.
The [statistics workflow](../.github/workflows/statistics.yml) updates and commits
only the statistics file.
Focused `lake build` or `lake env lean` commands do not refresh corpus metadata.
