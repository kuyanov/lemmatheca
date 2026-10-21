# Web app

A read-only Django reader with server-rendered templates, plain CSS and JavaScript,
and bundled KaTeX. Repository files are the storage layer; there is no database,
migration step, frontend build, or review system in the app.

## Development

Run from the repository root using the Python version range in
[pyproject.toml](../pyproject.toml):

```sh
uv sync --locked
uv run python app/manage.py build --no-lean
uv run python app/manage.py runserver
```

This setup reuses saved verification without Lean. Use the full build after
changing proofs or bindings; see the [shared build modes and checks](../CONTRIBUTING.md#validation-and-submission).
The [corpus guide](corpus.md) and [Lean guide](formal.md) describe the content and
verification contracts.

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
| `catalog/authoring_records.py` | Targeted source/planning record reads, independent catalogs, and catalog rebuilding |
| `catalog/authoring_validation.py` | Offline source/planning schema, relationship, link, and catalog checks |
| `catalog/index_reader.py` | Schema-checked, per-process index loading and replacement detection |
| `catalog/entry_text.py` | On-demand HTML text extraction and a bounded, per-process LRU cache |
| `catalog/entry_files.py` | Direct authored entry and metadata reads, navigation files, local assets |
| `catalog/node_files.py` | Authored node reads and installed Lean sources |
| `catalog/node_results.py` | Binding-matched indexed proof results and reader joins |
| `catalog/files.py` | Shared JSON reading, request ID guards, atomic replacement of individual JSON files |
| `catalog/content.py` | Reader data, indexed entry results, navigation, and live block badges |
| `catalog/sources.py`, `catalog/equations.py` | Trusted HTML parsing, references, equation labels, and rendering |
| `catalog/progress.py` | Verification counts and runtime badge formatting |
| `catalog/build.py` | Build orchestration, generated-data comparison and publication |
| `catalog/proofs.py` | Lean build, declaration checks, and proof-result preparation |
| `catalog/statistics.py` | Indexed entry/node totals, count history, and Git backfill; home-page snapshot reads |
| `catalog/validation.py` | Offline metadata, HTML, reference, and hierarchy validation |
| `catalog/corpus_index.py` | Derived relationships, entry/node results, and index publication |
| `catalog/management/commands/` | Unified `build` and separate `update_statistics` commands |
| `catalog/tests/` | Reader, locality, summary, and Lean-build checks |

`app/config/` contains settings, URL inclusion, middleware, and the WSGI entry point.
`app/templates/` and `app/static/` contain presentation and
[local vendor assets](vendor.md).

Requests use `read_entry(id)`, `read_entry_metadata(id)`, and `read_node(id)`.
Home reads only taxonomy, reading order, and `corpus/statistics.json`. Area listings
with entries and next-entry navigation join authored JSON metadata with generated
entry results from the corpus index. Parent-area pages with navigation only do
not load the index. Area pages open neither entry HTML nor node JSON and do
not scan Lean files. The entry header uses the same indexed line count. See the
[build guide](build.md#what-a-normal-build-does) for stored fields and counting rules.
The small taxonomy and `reading_order.json` provide area navigation and reading order.

An entry page parses its own HTML and computes progress from its linked nodes and
their matching indexed proof results.
If the index is missing or invalid, or a draft has no indexed record, ordinary
pages remain readable: listings omit the saved badge and line count, while entry
pages show unverified progress for nodes without matching results. An entry resolves referenced
entries only as needed for headings, anchors, and contextual return links, reusing
them within that request. Node pages load the requested node, its direct dependency
hints, matching indexed results, and the defining source file. The single-node API
reads only that node's authored file and joins its indexed result.
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
| `/api/source-errors/sources/` and `/<id>/` | Filtered publication summaries and one scoped review record |
| `/api/source-errors/findings/` and `/<id>/` | Filtered finding summaries and one finding's evidence and repair |
| `/api/reference-planning/` and `/<id>/` | Filtered pending development summaries and one planning record |

Reader and API routes accept GET and HEAD. Node responses combine authored fields
with binding-matched indexed proof results and add reader URLs and source paths.
The cached defining module, when present, supplies the source path and response
`module`; it does not rewrite the authored import module.

### Authoring API

The entry, node-search, reference, coverage and consumer authoring endpoints use
the [derived corpus index](#corpus-index).
Requests never rebuild it, write files, or invoke Lean. Ordinary HTML pages remain
readable without indexed results; `/api/nodes/` and `/api/nodes/<id>/` retain
their direct authored-file reads and return unverified nodes if no matching
indexed result is available.

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
`metadata_source="live_corpus_and_index"`.

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
`based_on`, the formatted indexed `formalization` summary or `lean_line_count`. Node search
preserves its full record response when `fields` is omitted; use `fields` to request a smaller
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
curl 'http://127.0.0.1:8000/api/search/nodes/?area=model-theory&q=compactness&q=elementary%20embedding&fields=id,description,module,declaration'
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

Relationships and generated entry/node results come from the indexed snapshot.
Entry text is parsed on demand from current HTML; authored metadata comes from
current JSON files. Coverage uses live block mappings and matching indexed proof
results after checking their structure against the index. A response can
therefore combine snapshot results with newer text or metadata. `index_revision`
does not certify that these live
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
positions also come from the snapshot. Requested entry `formalization` values
are formatted from indexed counts. Node proof results are joined only when the
current authored module and declaration match the saved binding; otherwise the
node is unverified without a signature or source line. Neither result is a fresh
Lean check.

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

### Source and planning API

These endpoints read the structured source register and reference plans through
their own compact committed catalogs. They work without the entry/node index and
never invoke Lean or rebuild catalogs during requests.

| Endpoint | Filters |
| --- | --- |
| `/api/source-errors/sources/` | `entry_id`, publication `url`, `q` |
| `/api/source-errors/findings/` | `source_id`, `entry_id`, `severity=serious` or `local`, `q` |
| `/api/reference-planning/` | `entry_id`, `area`, `kind`, `url`, `q` |

Append `<id>/` to a collection URL for a full record. Exact ID requests read one
file and do not need a catalog. List responses contain compact summaries and use
`limit` (default 20, maximum 100) and `offset`. Filters combine by intersection;
whitespace-separated `q` terms all match case-insensitively. Source search checks
the publication field; finding and plan searches check their record text.
Use `entry_id` for
either a current entry or a planned entry's ID. Area tags are exact and may name
future areas; they do not implicitly include taxonomy descendants. URL lookup
drops fragments and uses explicitly recorded aliases.

Filters narrow catalog IDs before records are opened. A text search reads the
candidate records but returns summaries. Catalogs contain no review or plan
prose. An unfiltered listing without `q` opens only its requested page. Unknown
or repeated parameters and malformed values return 400; missing records return
404; unavailable catalogs return 503. These endpoints have no `revision`,
`fields`, or entry-context `include` parameters. Refresh the catalogs with
`build --no-lean` after edits. The build validates authored record relationships;
full `build --check` also checks that committed catalogs match regeneration. See
the [record contract](corpus.md#navigating-source-and-planning-records) for paths,
maintenance, and direct-file fallback.

### Home-page statistics

The [statistics workflow](../.github/workflows/statistics.yml) refreshes
`corpus/statistics.json` after pushes to `main`. It records entry and node totals,
verified totals, all taxonomy areas (including subareas), and the contributor count.
The proof build does not modify this file, so parallel contributions do not produce
competing statistics changes. New authors are counted after their commits reach
`main`.

The workflow runs `uv run --locked python app/manage.py update_statistics` using
indexed entry counts and binding-matched node results. It requires a valid built
index whose entry and node IDs match the corpus, and refuses to publish otherwise. The
command needs neither Lean nor entry HTML. It validates the snapshot before
replacing the file atomically and leaves unchanged files untouched.
For maintenance, run the same command locally or manually dispatch the workflow on
`main`; contributors normally leave statistics generation to automation.

Runs are serialized and commit only the statistics file, without rebuilding the
structural index. If `main` advances before the push, the workflow fetches it and
recomputes, retrying up to three times without force-pushing. The workflow uses
`GITHUB_TOKEN` with `contents: write`; repository
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
mainline commits and reads changed metadata and index blobs, retaining compact
counts, binding pairs and proof flags rather than historical HTML or complete records. Legacy
`formal/nodes` files contribute to node totals. Verified counts include only saved
proof flags and entry summaries, starting at zero before these records exist.
Backfill accepts legacy entry summaries and node flags, then uses indexed results
when available, matching node results against their historical authored bindings.
It applies each commit as a whole, so migrating results into the index introduces
no false dip and index-only proof updates are counted.
Old review approvals are not proof results. Contributor history includes authors from
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

See the [build guide](build.md) for stages and flags, and the
[contribution check matrix](../CONTRIBUTING.md#validation-and-submission) for required checks.
`build --no-lean --check` checks canonical inputs without writes or a Lean
installation and tolerates missing or stale derived data. Add `--check-sources`
when installed source-file availability matters.

### Corpus index

Both writing build modes regenerate the index and authoring catalogs without
rewriting entry or node files. A full build checks Lean; `--no-lean` reuses only
binding-matched results from a valid compatible index. An existing unreadable,
invalid or incompatible snapshot fails a no-Lean writing build before publication.
If no snapshot is available, it records unverified nodes without signatures or
source lines and warns when bound nodes are affected. A full build restores these
results or replaces a bad snapshot. For example, to refresh derived data
without Lean at a one-off destination:

```sh
uv run python app/manage.py build --no-lean --index /tmp/corpus-index.json
```

`CORPUS_INDEX_PATH` defaults to the reserved `corpus/index.json`. Set
`DJANGO_CORPUS_INDEX_PATH` to change the path used by both the reader and build
by default. `--index PATH` selects the output or checked path for only that build
invocation. Other paths inside `corpus/` are rejected to protect canonical inputs.
The reserved index is generated and committed, but excluded from corpus input
discovery. Check modes write no index. Full `build --check` requires the selected
index to exist, parse as JSON, and equal regeneration, including its revision;
`build --no-lean --check` permits an absent or stale index.

The index keeps block structure and node mappings, backlinks, node consumers,
declaration/module lookups, entry block IDs and inverse reading positions. It
stores generated entry and node results alongside these relationships, but no
entry headings, statements, answers or link labels. Titles, abstracts, node
descriptions, taxonomy and reading-order records remain in authored files.
It has no corpus-wide `counts` field;
aggregate totals and history are stored only in `corpus/statistics.json`.
Internal references are stored once with their source-link positions; sparse
outgoing/incoming maps contain their edge IDs. Non-block anchors map to their
owning blocks.

The main schema fields are:

| Field | Contents |
| --- | --- |
| `schema_version`, `revision` | Schema 7 and an aggregate fingerprint of source inputs and generated entry/node results |
| `entries`, `blocks` | Entry relationships and generated results; block kinds/numbers/order and formal mappings, keyed by `entry#block` |
| `nodes` | Proof results keyed by node ID: checked `binding: [module, declaration]`, `verified`, optional `signature`/`declaration_line`, and `defining_module` when different from the authored module |
| `references`, `outgoing`, `incoming` | Structural link records with source-link positions and sparse maps of edge IDs |
| `node_consumers`, `nodes_by_declaration`, `module_nodes` | Reverse block mappings and declaration/module lookups |

Block `formal_ids` preserves all three states: `null` for unspecified mappings,
`[]` for explicitly nothing to formalize, and node IDs for mapped blocks.
Any indexed node dependency edges are authored hints, not Lean's dependency graph.

Metadata stays available through `read_node`, `read_entry_metadata`, `read_areas`,
and `read_reading_order`. Known-path record reads are constant in corpus record
count, with a cost proportional to the requested record's bytes. Node descriptions
stay in authored files; proof results live only in the index. Unfiltered node
description searches scan and read node files; exact declaration/module and area
filters narrow those reads. Area membership is derived on demand from live entry
metadata and indexed mappings, without a separate node-area index. A node listing
without text or verification filters reads only the requested page's node records
after selecting candidate IDs.

The revision covers exact indexed source bytes, including node metadata and
uncommitted edits, plus generated entry/node results. A proof-result or Lean
line-count change therefore changes the revision even if corpus sources are
unchanged. It excludes `statistics.json`; statistics-only updates leave the index
and its full-check freshness unchanged. The revision identifies that
snapshot, not the current Lean proof state or whether the working tree has since
changed. Per-file hashes are used only
during generation and are not exported; identifying changed files requires
another scan.

Authored corpus HTML and JSON remain the source of truth. The index is a
generated, committed snapshot used by the authoring API, reader entry/node results
and statistics generation. Each process
caches its parsed index and checks the file's stat information to detect atomic
replacement; it does not rescan the corpus or cache live metadata between
requests. Refresh the index explicitly after edits; there is no corpus freshness
watcher. Read-only reviews using direct corpus files do not need to generate it.
During an area pipeline, the root maintains this snapshot through coordinated
[index checkpoints](../CONTRIBUTING.md#index-checkpoints); entry agents request
refreshes rather than running concurrent writing builds.

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

The [build guide](build.md#failures-and-scope) describes publication guarantees.
No-Lean regeneration reuses saved proof results and does not establish proof freshness.

### Tests

With the pinned Lean environment installed, run all catalog tests with
`uv run python app/manage.py test catalog`.

The [CI workflow](../.github/workflows/ci.yml) runs structural
`build --no-lean --check` before installing Lean, runs the tests, and finishes
with `build --check --check-sources`.
The final check compares authoring catalogs and the selected index, including
entry/node results and revision, without modifying them. Kernel-checker
tests cover complete and unfinished declarations, transitive axioms and missing
declarations. Build/publication tests use subprocess fixtures; reader tests use
small representative corpora and check locality. Whole-corpus structural checking
is separate from those fixtures.

Reader tests check response data, navigation targets, source anchors, disclosure
behavior, and accessibility. Keep assertions independent of CSS classes, exact
copy, icons, whitespace, and attribute ordering; use the test HTML helper when
checking rendered links or structure. Locate labelled sections using stable
`aria-labelledby` relationships and require nonempty headings without fixing their
wording. Check displayed data within the relevant section, using response context
or corpus records for expected values. Verification expectations should come from
controlled fixtures or indexed results, not the corpus's current completion rate.

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

Deploy a clean revision whose CI full `build --check` passed. Before serving it,
run `uv run python app/manage.py build --no-lean --check` for read-only structural
validation. This leaves the committed corpus data unchanged and does not check
generated-data freshness; deployment relies on CI for that check.
Add `--check-sources` if installed Lean source-file availability should be checked.
Entry/node authoring queries and saved reader entry/node results use the committed
generated index. Source/planning queries use their independent committed catalogs;
ordinary reader pages and direct node APIs remain readable without it, with nodes
shown as unverified and no saved signatures or source lines.
For deployment, set `DJANGO_DEBUG=0`, `DJANGO_SECRET_KEY`, and explicit
`DJANGO_ALLOWED_HOSTS`. Serve `config.wsgi:application` from `app/` with a production
WSGI server and run `uv run python app/manage.py collectstatic` to collect assets.
Serve the collected `staticfiles/` directory at `/static/` and keep the corpus
available to the server. Install the pinned Lean sources to provide declaration
source browsing; the deployment check itself does not require Lean. Entry HTML and JSON are
read as content, not published as static files; only entry `assets/` directories
are registered for static serving.

For the Ubuntu deployment where Nginx serves `/var/www/lemmatheca/static/` and
systemd runs `lemmatheca.service`, run the root-level
[`update_static.sh`](../update_static.sh) after each pull:

```sh
git pull
./update_static.sh
```

Run it as your normal deployment user. It runs the read-only
`build --no-lean --check` using the existing `.venv/bin/python`, then collects
current assets and mirrors them into the Nginx static directory with readable permissions.
It removes obsolete assets and restarts the application so Python, templates, and
registered entry asset directories are refreshed. It asks
for sudo access to publish files and manage the service. Install `rsync` first
if needed (`sudo apt install rsync`). Runtime dependency updates are a separate
deployment step when requirements change.

## Scaling

Core entry/node validation takes O(B + R) time, where B is the input byte count and
R is the number of references. Each entry JSON, entry HTML, and node JSON is opened
once. It keeps one HTML tree/record at a time, plus compact area parents, entry
block IDs, cross-entry links, and node hint edges. Memory grows with these indexes
and the largest entry/node record, rather than all entry prose, signatures, or HTML
trees. Graph checks use iterative traversal, including for long chains and shared dependencies.
Optional source checks add the bytes of each distinct bound source file.

Source/planning registry validation also reads each JSON record once and retains
the structured registry records while checking cross-record relationships and
catalog contents. Its memory cost therefore includes those registries' total
record bytes. These records are not copied into the entry/node index.

Index generation retains structural relationships, proof results and temporary
revision inputs during that pass, rather than all entry prose or HTML trees.
Collection, hashing, and output are linear in input bytes and indexed
relationships; sorting K indexed keys for deterministic serialization adds
O(K log K) work. The validator collects index relationships during its input scan.

This removes validation from response time and keeps corpus checks suitable for a
growing collection. It does not make every other pipeline stage independent of
corpus size:

- Navigation reloads the taxonomy and area index. Subtree counts currently walk
  ancestor chains; a deep taxonomy can make this quadratic in the number of areas.
- Area pages load all listed metadata without pagination. Entry pages parse their
  HTML and directly referenced entries, and load their bound nodes. Node pages
  load direct hints and render the entire defining Lean source file.
- The full node API returns every record. Large consumers will need pagination.
- The build holds the registry, proof results, and generated index in memory and
  checks all declarations. Per-file writes are atomic, but publication of the
  entire corpus is not a single atomic operation.
- Static asset directories are scanned at process startup. Lean builds and the
  Python-version CI matrix remain more expensive than corpus validation.

The next steps at larger scale are dedicated text-search indexes, pagination for the
legacy full-node API and area listings, and publishing staged build output as one snapshot.
Reader tests use representative pages; exhaustive corpus checks do not render the
whole collection. Keep the corpus immutable while validating and publishing it,
since validation checks the files it reads, and a saved index is a snapshot rather
than an automatically refreshed runtime cache.
