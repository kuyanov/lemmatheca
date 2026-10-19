# Web app

A read-only Django reader with server-rendered templates, plain CSS and JavaScript,
and bundled KaTeX. Repository files are the storage layer; there is no database,
migration step, frontend build, or review system in the app.

## Development

Run from the repository root using the Python version range in
[pyproject.toml](../pyproject.toml):

```sh
uv sync --locked
uv run python app/manage.py validate_corpus
uv run python app/manage.py build
uv run python app/manage.py test catalog
uv run python app/manage.py runserver
```

The build assumes the pinned Lean environment is installed. It updates node
verification, precomputes entry-list badges, and refreshes the derived corpus
index. Run it after adding an entry or changing its block inventory, formal
mappings, node bindings, or Lean code, and include the generated JSON in the change.
See the [corpus guide](corpus.md) and [Lean guide](formal.md).

Open <http://127.0.0.1:8000/>. Restart the server when adding an entry's
asset directory, since Django registers those directories at startup. Python edits
also require a restart when running with `--noreload`.

## Code layout and reads

The backend is a single Django app, `catalog`. Paths in this table are relative
to `app/`:

| File | Responsibility |
| --- | --- |
| `catalog/urls.py`, `catalog/views.py` | Entry, area, node, and API requests |
| `catalog/api.py`, `catalog/queries.py` | Read-only authoring API validation and queries |
| `catalog/index_reader.py` | Schema-checked, per-process index loading and replacement detection |
| `catalog/entry_text.py` | On-demand HTML text extraction and a bounded, per-process LRU cache |
| `catalog/entry_files.py` | Direct entry and metadata reads, navigation files, local assets, summary writes |
| `catalog/node_files.py` | Direct node reads, installed Lean sources, proof-result preparation and writes |
| `catalog/files.py` | Shared JSON reading, request ID guards, atomic replacement of individual JSON files |
| `catalog/content.py` | Reader data, navigation, and block badges |
| `catalog/sources.py`, `catalog/equations.py` | Trusted HTML parsing, references, equation labels, and rendering |
| `catalog/progress.py` | Shared entry/block verification summaries |
| `catalog/proofs.py` | Lean build, declaration checks, and entry-summary generation |
| `catalog/statistics.py` | Saved-metadata totals, count history, and Git backfill; direct snapshot read for the home page |
| `catalog/validation.py` | Offline metadata, HTML, reference, and hierarchy validation |
| `catalog/corpus_index.py` | Optional derived index collection and publication |
| `catalog/management/commands/` | Independent `validate_corpus`, Lean `build`, and `update_statistics` commands |
| `catalog/tests/` | Reader, locality, summary, and Lean-build checks |

`app/config/` contains settings, URL inclusion, middleware, and the WSGI entry point.
`app/templates/` and `app/static/` contain presentation and
[local vendor assets](vendor.md).

Requests use `read_entry(id)`, `read_entry_metadata(id)`, and `read_node(id)`.
Home reads only taxonomy, reading order, and `corpus/statistics.json`. Area listings
and next-entry navigation use JSON metadata. In particular,
area pages use the saved `formalization` summary: they open neither entry HTML nor
node JSON. The small taxonomy and `area_entries.json` index provide area navigation
and reading order.

An entry page parses its own HTML and loads its linked nodes. It resolves referenced
entries only as needed for headings, anchors, and contextual return links, reusing
them within that request. Node pages load the requested node, its direct dependency
hints, and the defining source file. The single-node API reads only that node.
The full node API and build command enumerate nodes because they cover the collection.
HTML page requests never launch Lean or write corpus data. They trust corpus structure
validated offline; metadata ID matching, HTML consistency, reference existence, and
asset filesystem checks do not run in the reader. Checks on user-supplied record IDs
and area URLs still protect filesystem access and return 404 for invalid routes.
The authoring API additionally checks requested records and the structure of
entries it parses against the index, as described below.

## Routes

| Route | Purpose |
| --- | --- |
| `/` | Area browsing, corpus counts, and entry/node verification totals |
| `/areas/<path>/` | Subareas and entries listed for the area |
| `/entries/<id>/` | Mathematical entry, references, questions, and block badges |
| `/nodes/<id>/` | Description, verification, Lean signature, dependencies, and source |
| `/api/nodes/` | All node records as JSON |
| `/api/nodes/<id>/` | One node record as JSON |
| `/api/entries/` | Compact, filtered entry listing |
| `/api/entries/<id>/context/` | Selected entry context and related records |
| `/api/search/blocks/` | Filtered block text search |
| `/api/search/nodes/` | Node text and binding search |
| `/api/references/` | Incoming/outgoing entry or anchor references |
| `/api/coverage/` | Block mappings and saved verification coverage |
| `/api/nodes/<id>/consumers/` | Consuming blocks and authored dependency hints |

Reader and API routes accept GET and HEAD. The API adds reader URLs and source paths to the saved node fields. Verification comes from the saved `verified` flag.

### Authoring API

The seven authoring endpoints use the [derived corpus index](#corpus-index).
Requests never rebuild it, write files, or invoke Lean. Ordinary HTML pages and
the existing `/api/nodes/` and `/api/nodes/<id>/` endpoints retain their direct
file reads and work without the index.

| Endpoint | Query parameters |
| --- | --- |
| Entry listing | Optional `area`, `include_descendants=true` and `fields`. Results follow `(primary_area, reading_position, id)` order. |
| Entry context | `include=blocks,nodes,references,coverage,navigation` selects components; default `blocks,navigation`. Optional `block_ids` selects local block IDs. `include_answers=true` by default. |
| Block search | `q`, optional `area` and `kind`; `include_answers=false` by default. All whitespace-separated literal terms must match, ignoring case, across title/body and optionally answers. Area includes descendants and entries assigned through additional areas. |
| Node search | Optional `q`, `area`, `include_descendants=true`, `usage` (`any`, `mapped`, `unmapped`), and `fields`. `q` searches ID, description, module, declaration, and saved signature. `module` and `declaration` are exact filters; `verified=true` or `false` filters saved results. |
| References | Required `target` is an entry ID or `entry#anchor`; `direction=incoming`, `outgoing`, or `both` (default). Encode `#` as `%23` in URLs. |
| Coverage | Required comma-separated `entry_ids`, up to 20 entries. |
| Node consumers | Node ID comes from the path; results distinguish prose consumers from authored node dependency hints. |

Entry, search, reference, and consumer result lists use `limit` (default 20, maximum
100) and nonnegative `offset`. These controls also page the block, node, and
reference components in entry context. Coverage returns all mappings for its
selected entries. Omitting `q` lists the nodes matching the other filters.
Search `q` is limited to 200 characters per value. Every endpoint
accepts optional `revision=<expected>`; a different cached index revision returns
HTTP 409. Responses identify `index_revision` and
`metadata_source="live_corpus"`.

For entry context, `block_ids=local-id-a,local-id-b` selects up to 100 nonempty
block IDs within that entry. Repeated IDs are deduplicated, and selected blocks
follow entry order, regardless of selector order. Selection happens before
pagination. It limits blocks, their deduplicated mapped nodes, coverage and
references; metadata and navigation still describe the whole entry. References
are the union of incoming and outgoing links for the selected blocks, including
their nested anchors, with each link returned once even when both ends are
selected. The selector also works with `include=nodes,coverage` without fetching
block text. At least one of `blocks`, `nodes`, `coverage` or `references` must be
included when using `block_ids`.
Component counts and coverage summaries describe the selection. Coverage
includes every selected block, independently of pagination.

An empty selector, empty CSV item, malformed block ID (including `#`) or repeated
`block_ids` parameter returns 400. Unknown IDs, IDs belonging to another entry,
and nested-anchor IDs that are not themselves blocks return 404. The response
echoes the normalized selection in `block_ids`. Selection reduces the response
payload; parsing and structural validation still cover the whole entry HTML.

Entry listing returns `id`, `title`, `primary_area`, `additional_areas`,
`reading_position`, `block_count` and `url` by default. Its comma-separated
`fields` selector can choose those fields and `abstract`, `summary`, `reading_time`,
`based_on` or the saved `formalization` summary. Node search preserves its full
record response when `fields` is omitted; use `fields` to request a smaller
subset of `id`, `description`, `module`, `declaration`, `dependencies`, `verified`,
`signature`, `declaration_line`, `url`, `source_path` and `matched_queries`.
Both selectors always include `id`; optional fields absent from the record are
omitted. Unknown fields are rejected. Field selection changes the response,
not the fields searched or the matching rules. Node results follow lexical ID order.
Entry listings and node searches read JSON metadata and indexed
relationships, without opening entry HTML.

For entry listing and node search, `area` matches entries assigned through either
their primary or additional areas. Descendants are included unless
`include_descendants=false`. A node matches an area when at least one block in a
matching entry consumes it. Shared nodes appear once in each relevant query;
unmapped nodes have no consuming entry and do not match any area. Area membership
does not follow node dependency hints or Lean dependencies. `usage=mapped` keeps
nodes with an indexed consumer, `usage=unmapped` keeps nodes without one, and
`usage=any` is the default. Area filtering combines with the other node filters.

Only node search accepts repeated `q` parameters, with up to ten nonempty groups.
All whitespace-separated terms within one group must match; a match in any group
includes the node. The response counts and paginates the deduplicated union, not
each group separately. Full multi-query results include `matched_queries`, the
zero-based indices of the matching query groups. An explicit
`fields=matched_queries` requests this field even for a single query.
Other repeated parameters are rejected. A single empty `q` retains the
unfiltered-list behavior.

For example, with the local server running:

```sh
curl 'http://127.0.0.1:8000/api/entries/?area=mathematical-logic&fields=id,title,reading_position'
curl 'http://127.0.0.1:8000/api/entries/propositional-logic/context/?include=blocks,nodes,coverage&limit=10'
curl 'http://127.0.0.1:8000/api/entries/arithmetic-representability/context/?block_ids=recursive-relations,numeralwise-versus-uniform&include=blocks,nodes,coverage'
curl 'http://127.0.0.1:8000/api/search/blocks/?q=truth%20table&area=mathematical-logic'
curl 'http://127.0.0.1:8000/api/search/nodes/?area=mathematical-logic&q=compactness&q=elementary%20embedding&fields=id,description,module,declaration'
curl 'http://127.0.0.1:8000/api/search/nodes/?usage=unmapped&fields=id,description'
curl 'http://127.0.0.1:8000/api/references/?target=propositional-logic&direction=incoming'
```

Incoming references to a block include its nested anchors. Outgoing references
for a non-block anchor come from its owning block.

Entry context includes internal and external links with their targets and reader
URLs. Empty block-link labels are resolved as in the reader: numbered labels
within the entry and target headings across entries. Figure, table and equation
anchors receive numbered labels too. These labels also appear in the returned
prose. `include_answers=false` omits answer text and answer-only links.

Relationships come from the indexed snapshot. Entry text is parsed on demand
from current HTML, and JSON metadata is read from current corpus files, including
saved proof results. A response can therefore combine snapshot relationships
with newer text or metadata. `index_revision` does not certify that these live
files match the snapshot or that Lean has checked current sources. Text-only
edits become visible without regenerating the index. Whenever the API parses an
entry's HTML, it checks block structure, formal mappings and the complete internal-link
sequence against the index. Coverage and context node results validate their
selected entries too. Outgoing-reference queries check their source even when
the indexed result or requested page is empty. Structural changes require an
index refresh; detected mismatches return 409 `index_outdated`. Incoming-reference
queries still use the snapshot to find sources, so a new link from an entry that
the request does not load is visible only after an index refresh.
Node area and usage filters likewise use indexed block mappings, combined with
live entry area metadata. They do not parse HTML or detect new or removed
consumers until the index is refreshed. Entry-list block counts and reading
positions also come from the snapshot; requested `formalization` values and node
verification flags are saved build results, not fresh Lean checks.

Malformed or unknown query parameters return 400; unknown IDs return 404.
A selected record missing from the current files returns 409 `index_outdated`.
A missing, invalid, or schema-incompatible index returns 503 with regeneration
instructions. Lean inspection, check planning, browser previews, source assessment,
and batch writes are not exposed by these endpoints.

Node pages render plain-text descriptions with math, escape the Lean source,
and link declaration lines into the local source
browser. The server is expected to
have project, dependency, and pinned toolchain sources installed; there is no
upstream-source fallback. Login is a presentation placeholder; the contribution
dialog links to the GitHub repository and explains how to get involved.

### Home-page statistics

The [statistics workflow](../.github/workflows/statistics.yml) refreshes
`corpus/statistics.json` after pushes to `main`. It records entry and node totals,
verified totals, all taxonomy areas (including subareas), and the contributor count.
The proof build does not modify this file, so parallel contributions do not produce
competing statistics changes. New authors are counted after their commits reach
`main`.

The workflow runs `uv run --locked python app/manage.py update_statistics` using
the committed entry summaries and node verification flags. This command reads one
metadata record at a time and needs neither Lean nor entry HTML. It validates the
snapshot before replacing the file atomically and leaves unchanged files untouched.
For maintenance, run the same command locally or manually dispatch the workflow on
`main`; contributors normally leave statistics generation to automation.

Runs are serialized and commit only the statistics file. If `main` advances before
the push, the workflow fetches it and recomputes, retrying up to three times without
force-pushing. The workflow uses `GITHUB_TOKEN` with `contents: write`; repository
rules must permit this automatic commit to `main`.

`history` contains four series: `entries`, `nodes`, `areas`, and `contributors`.
Each point has a UTC `at` timestamp and a nonnegative `count`. Entry and node
points also have a `verified` count, so both chart lines share the same timestamps.
A successful refresh appends a point when either count changes, including decreases.
Unchanged refreshes preserve the history exactly; failed refreshes publish neither new
counts nor history. Graphs use their legends in place of card titles to leave more
room for the plot.

When history is absent, the first refresh imports the local Git history through
`HEAD`. Use a full, up-to-date clone of the GitHub repository. The import follows
mainline commits and reads only changed metadata blobs, retaining compact counts
and proof flags rather than historical HTML or complete records. Legacy
`formal/nodes` files contribute to node totals. Verified counts include only saved
proof flags and entry summaries, starting at zero before these records exist; old
review approvals are not proof results. Contributor history includes authors from
merged branches. Later refreshes append the current results without replaying Git
history, preserving any manual trimming of historical points. The command itself
does not fetch GitHub or rebuild old Lean projects.

Contributors are distinct author names from `git shortlog --summary HEAD`, which
respects `.mailmap`, excluding names ending in `[bot]` so automation does not count
as a contributor. They are repository commit authors, not the authors of cited
sources; uncommitted work is not part of Git history. The statistics workflow
checks out full history for this calculation.
Shallow checkouts and source archives preserve existing history and contributor
counts; without a saved snapshot, contributors remain unknown and other series
start at the first successful refresh. Serving pages needs neither Git nor network
access. Before the first snapshot, unavailable statistics display a dash.

## Checks

Run `uv run python app/manage.py validate_corpus` while editing. It is independent
of the build, writes no files by default, and permits missing or stale generated
results. The optional `--check-sources` checks installed source files without
invoking Lean.

### Corpus index

Validation can collect an authoring index during the same corpus scan:

```sh
uv run python app/manage.py validate_corpus --write-index
uv run python app/manage.py validate_corpus --write-index /tmp/corpus-index.json
uv run python app/manage.py validate_corpus --check-sources --write-index
```

The command validates the configured corpus. The bare flag writes to
`CORPUS_INDEX_PATH`, which defaults to `artifacts/corpus-index.json` under the
repository root. Set `DJANGO_CORPUS_INDEX_PATH` to override this location
for commands and the API. An explicit `--write-index PATH` selects
a different destination outside the corpus directory; cache output cannot
overwrite corpus inputs. `--check-sources` composes with index generation and
still does not invoke Lean.

The index keeps block structure and node mappings, backlinks, node consumers,
declaration/module lookups, entry block IDs and inverse reading positions. It
stores no entry headings, statements, answers or link labels, and avoids copying
entry/node metadata, taxonomy and reading-order records. Internal references are
stored once with their source-link positions; sparse outgoing/incoming maps
contain their edge IDs. Non-block anchors map to their owning blocks.

The main schema fields are:

| Field | Contents |
| --- | --- |
| `schema_version`, `revision` | Format version and an aggregate fingerprint of the input snapshot |
| `entries`, `blocks` | Entry relationships, block kinds/numbers/order and formal mappings, keyed by `entry#block` |
| `references`, `outgoing`, `incoming` | Structural link records with source-link positions and sparse maps of edge IDs |
| `node_consumers`, `nodes_by_declaration`, `module_nodes` | Reverse block mappings and declaration/module lookups |

Block `formal_ids` preserves all three states: `null` for unplanned mappings,
`[]` for explicitly nothing to formalize, and node IDs for mapped blocks.
Any indexed node dependency edges are authored hints, not Lean's dependency graph.

Metadata stays available through `read_node`, `read_entry_metadata`, `read_areas`,
and `read_area_entries`. Known-path record reads are constant in corpus record
count, with a cost proportional to the requested record's bytes. Node descriptions,
signatures, and verification flags are not copied into the index. Unfiltered node
description searches scan and read node files; exact declaration/module and area
filters narrow those reads. Area membership is derived on demand from live entry
metadata and indexed mappings, without a separate node-area index. A node listing
without text or verification filters reads only the requested page's node records
after selecting candidate IDs.

The revision covers the exact indexed input files, including node metadata and
uncommitted edits. It identifies that snapshot, not the current Lean proof state
or whether the working tree has since changed. Per-file hashes are used only
during generation and are not exported; identifying changed files requires
another scan.

Corpus HTML and JSON remain the Git-tracked source of truth. The index is a
disposable, ignored artifact required only by the authoring API. Each process
caches its parsed index and checks the file's stat information to detect atomic
replacement; it does not rescan the corpus or cache live metadata between
requests. Refresh the index explicitly after edits; there is no corpus freshness
watcher. Read-only reviews using direct corpus files do not need to generate it.

Parsed entry text has a separate LRU cache. By default each worker retains at
most **8 MiB of accounted Python-object memory** and **128 entries**, including
headings, statement/answer text and link labels. It retains no raw HTML or parsed
HTML trees. File stat checks detect edits and atomic replacements; a same-size
in-place edit that preserves the observed timestamps can escape detection. Old
versions are discarded, least recently used entries are evicted, and entries
larger than the byte budget are returned without being cached.

Set `DJANGO_CORPUS_TEXT_CACHE_BYTES` and `DJANGO_CORPUS_TEXT_CACHE_ENTRIES` to
change those limits; setting either to `0` disables retention. Limits apply per
worker and cover retained cache data, not temporary parsing or response memory.
Block searches process entries one at a time and retain only the requested
result page. Cold searches parse candidate entries; searches exceeding the cache
budget can require reparsing on later requests. Coverage validates HTML for its
selected entries through the same bounded cache. Node searches do not parse
entry HTML.

Validation publishes the index through atomic replacement only after all input
checks succeed, so invalid input leaves an existing cache untouched. The Lean
`build` command refreshes the configured index after publishing node results and
entry summaries. Index-only generation does not check Lean freshness. A build can
fail during index export after proof metadata has already been refreshed; the
entire build is not one transaction.

### Tests

The [CI workflow](../.github/workflows/ci.yml) validates the corpus before installing
Lean, checks installed sources, runs the tests and `app/manage.py build`, and rejects
changes to committed node data or entry summaries. Tests run the current proof
checker and its axiom cases in one invocation of the pinned Lean toolchain.
Build/publication tests use subprocess fixtures to exercise persistence and
failures without repeatedly compiling temporary Lake projects. Reader behavior
uses small fixtures alongside representative real-corpus pages. Locality tests
prevent area and detail views from loading unrelated content. Whole-corpus
validation runs through `validate_corpus`, separately from fixture-based tests.

Reader tests check response data, navigation targets, source anchors, disclosure
behavior, and accessibility. Keep assertions independent of CSS classes, exact
copy, icons, whitespace, and attribute ordering; use the test HTML helper when
checking rendered links or structure. Locate labelled sections using stable
`aria-labelledby` relationships and require nonempty headings without fixing their
wording. Check displayed data within the relevant section, using response context
or corpus records for expected values. Verification expectations should come from
controlled fixtures or saved node data, not the corpus's current completion rate.

To run only the build and kernel-checker tests:

```sh
uv run python app/manage.py test catalog.tests.test_build
```

### Response benchmark

To measure response times and corpus file reads:

```sh
uv run python app/manage.py shell -c 'from catalog.tests.benchmark_reader import benchmark; benchmark()'
```

This measures 50 responses per route after five warmup requests, with `DEBUG=False`.
It reports median and p95 milliseconds through Django's request handler, including
file reads and template rendering but excluding HTTP transport and static assets.

## Deployment

Validate the deployed corpus with `validate_corpus --check-sources --write-index`
before serving it. The authoring APIs require the generated index; ordinary reader
pages and legacy node APIs also work without it.
For deployment, set `DJANGO_DEBUG=0`, `DJANGO_SECRET_KEY`, and explicit
`DJANGO_ALLOWED_HOSTS`. Serve `config.wsgi:application` from `app/` with a production
WSGI server and run `uv run python app/manage.py collectstatic` to collect assets.
Serve the collected `staticfiles/` directory at `/static/`. Keep the corpus and
installed Lean sources available to the server. Entry source HTML and JSON are
read as content, not published as static files; only entry `assets/` directories
are registered for static serving.

For the Ubuntu deployment where Nginx serves `/var/www/lemmatheca/static/` and
systemd runs `lemmatheca.service`, run the root-level
[`update_static.sh`](../update_static.sh) after each pull:

```sh
git pull
./update_static.sh
```

Run it as your normal deployment user. It validates the corpus and refreshes the
index without Lean using the existing `.venv/bin/python`, then collects current
assets and mirrors them into the Nginx static directory with readable permissions.
It removes obsolete assets and restarts the application so Python, templates, and
registered entry asset directories are refreshed. It asks
for sudo access to publish files and manage the service. Install `rsync` first
if needed (`sudo apt install rsync`). Runtime dependency updates are a separate
deployment step when requirements change.

## Scaling

Default validation takes O(B + R) time, where B is the input byte count and R is
the number of references. Each entry JSON, entry HTML, and node JSON is opened once. It keeps
one HTML tree/record at a time, plus compact area parents, entry block IDs,
cross-entry links, and node hint edges. Memory therefore grows with these indexes
and the largest record, rather than all prose, signatures, or HTML trees. Graph
checks use iterative traversal, including for long chains and shared dependencies.
Optional source checks add the bytes of each distinct bound source file.

Index generation retains structural relationships and temporary revision inputs
during that pass, rather than all entry prose or HTML trees.
Collection, hashing, and output are linear in input bytes and indexed
relationships; sorting K indexed keys for deterministic serialization adds
O(K log K) work. There is no second full corpus scan to collect the index.

This removes validation from response time and keeps corpus checks suitable for a
growing collection. It does not make every other pipeline stage independent of
corpus size:

- Navigation reloads the taxonomy and area index. Subtree counts currently walk
  ancestor chains; a deep taxonomy can make this quadratic in the number of areas.
- Area pages load all listed metadata without pagination. Entry pages parse their
  HTML and directly referenced entries, and load their bound nodes. Node pages
  load direct hints and render the entire defining Lean source file.
- The full node API returns every record. Large consumers will need pagination.
- The build holds the registry, results, and pending summaries in memory and
  checks all declarations. Per-file writes are atomic, but publication of the
  entire corpus is not a single atomic operation.
- Static asset directories are scanned at process startup. Lean builds and the
  Python-version CI matrix remain more expensive than corpus validation.

The next steps at larger scale are dedicated text-search indexes, pagination for the
legacy full-node API and area listings, and staged build output published as one snapshot.
Reader tests use representative pages; exhaustive corpus checks do not render the
whole collection. Keep the corpus immutable while validating and publishing it,
since validation checks the files it reads, and a saved index is a snapshot rather
than an automatically refreshed runtime cache.
