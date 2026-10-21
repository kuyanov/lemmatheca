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
   reading-order listings, and source/planning records. Missing or stale generated
   data is allowed at this stage because the build will regenerate it.
2. **Run Lean.** Build `Lemmatheca` and all bound non-core modules, then inspect
   each registered declaration and its transitive kernel axioms. Compilation
   errors and missing declarations fail the command. Unfinished proofs or
   unsupported axioms produce `verified: false`; they do not by themselves fail
   the build. See the [verification rules](formal.md#build-and-verification).
3. **Prepare generated data.** Build the corpus index, including node proof
   results, entry formalization counts and Lean line counts. Refresh the
   source/planning catalogs.
4. **Validate the proposed result, then save it.** Authored prose, descriptions,
   mathematical statements, entry metadata, and proof sources are not rewritten.

The generated outputs are:

| Output | Location | Git |
| --- | --- | --- |
| Source-error and reference-planning catalogs | `corpus/source-errors/index.json` and `corpus/reference-planning/index.json` | Commit with the records |
| Node proof results, entry results and structural relationships | `corpus/index.json` by default | Commit with the inputs |

Builds never rewrite entry or node files. Unchanged catalogs are left untouched;
the index is replaced on every writing build.

Each `index.nodes[node_id]` stores the authored `binding` pair
`[module, declaration]` and `verified`, with optional `signature` and `declaration_line`.
If Lean reports a different source module, `defining_module` records it for source
browsing without changing the authored import module. Unbound nodes store only
`binding: [null, null]` and `verified: false`.

Each `index.entries[entry_id]` stores `lean_line_count` and exactly three
`formalization` counts:

| Field | Meaning |
| --- | --- |
| `complete` | Distinct mapped nodes whose saved verification flag is true |
| `total` | Distinct mapped nodes |
| `unmapped_blocks` | Blocks without a specified `data-formal` mapping |

An explicitly empty `data-formal=""` mapping means nothing needs formalization;
it does not count as unmapped. The build collects mappings during validation,
without parsing HTML again for summaries. The reader and API derive status,
percentage, label and description from these counts and the indexed block count.
Unmapped blocks prevent a completed badge even when every mapped node is verified.

Each entry's `lean_line_count` sums physical lines in all `.lean` files recursively
under its `formal/Lemmatheca/<PascalCaseEntryId>/` directory. Blank lines and
comments count, as does a final line without a newline. Imported code outside that
directory is excluded; a missing directory gives zero. Counts are recomputed from
source files even with `--no-lean`, without running the Lean compiler.

The index stores lookup relationships, with no `counts` field. Corpus-wide totals
and their history belong solely in `corpus/statistics.json`. Validation counts
printed by `build` are computed in memory, not saved in the index.

Corpus JSON and HTML use LF line endings so the index revision is consistent
across checkouts. If the generated index has a merge conflict, resolve its input
files first, then run full `build` to replace the invalid snapshot. A no-Lean
refresh requires a valid saved snapshot to preserve its proof results.

## Flags and combinations

The two main flags control different parts of the command:

- **`--no-lean`** skips Lean and reuses indexed proof results only when their
  saved binding exactly matches the current authored module and declaration.
  An existing unreadable, invalid or incompatible snapshot fails the writing
  build before any generated files are changed; run full `build` to replace it.
  If no saved snapshot is available, the build can proceed with unverified
  results and warns when bound nodes are affected. Missing results, new or
  changed bindings, and unbound nodes give `verified: false` without a signature
  or source line. Run a full build to recover those results. Reused results do
  not verify edited Lean code.
  Entry counts use these results and current block mappings; Lean line counts
  are refreshed from source files.
- **`--check`** publishes no corpus data. With Lean enabled, it regenerates data
  in memory and fails if authoring catalogs differ, or if the selected index is
  missing, invalid JSON, or differs from regeneration, including its entry/node
  results and revision. Combined with `--no-lean`, it stops
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
| `--index PATH` | Override the index output or checked path for this invocation. It does not change the reader's configured path or suppress catalog outputs. A no-Lean writing build reuses results from this snapshot; only if it does not exist can it use the normal snapshot. An existing unreadable, invalid or incompatible snapshot fails the command without falling back or writing generated files. Full `--check` compares the selected index; `--no-lean --check` only validates the destination. Check modes write no index. |

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
bytes affect the index revision. Generated node and entry results also affect it,
so proof-result or Lean line-count changes require an index refresh even without
corpus source edits. Commit changed generated files, including
`corpus/index.json`. Normally publish at the final mutating stage of a batch;
a read-only check does not replace the writing build. In a
[coordinated area pipeline](../CONTRIBUTING.md#running-an-area-pipeline), the root
alone publishes generated data and also runs `build --no-lean` at coherent
[index checkpoints](../CONTRIBUTING.md#index-checkpoints) with all corpus writes
paused. These make earlier additions discoverable to agents without rerunning
Lean; the final full build remains required for proof verification.

Checkpoint counts are provisional: if a binding changes, a no-Lean checkpoint
discards the old binding's saved result. Reverting the binding afterward cannot
recover that result from the new snapshot; run a full build to restore it.

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
with Lean, establish prerequisite order or module ownership, run the test suite,
collect static assets, or restart the reader.
It validates the shape of `corpus/statistics.json` when present but does not
regenerate it. Statistics are excluded from the index revision, so statistics-only
updates do not require rebuilding the index or affect its full-check freshness.
The [statistics workflow](../.github/workflows/statistics.yml) updates and commits
only the statistics file.
Focused `lake build` or `lake env lean` commands do not refresh corpus metadata.
