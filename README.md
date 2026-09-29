# Lemmatheca

Lemmatheca aims to bring mathematics together in a connected library of readable
explanations and computer-checked results. An **entry** develops a topic through
definitions, theorems, proofs, examples, and questions. A **node** records one
reusable mathematical definition or claim and connects it to a declaration in
[Lean](https://lean-lang.org/), a language that checks formal mathematical proofs.
Different entries can share the same nodes.

The website lets readers browse mathematical areas, follow references between
entries, and inspect the formal statements and proofs behind an entry's blocks.
The content lives in HTML and JSON files, so writing, reviewing, and changing it
uses the same Git workflow as the application code.

## Plan

Grow the library topic by topic: choose sources, write clear exposition, review
the mathematics, connect its claims to formal nodes, review those connections,
and complete the proofs. Human exposition can be contributed before its
formalization is ready.

The long-term aim is broad mathematical coverage with reusable results across
subjects. The project keeps one shared Lean library, favors existing results in
mathlib (Lean's community mathematics library), and keeps the reader simple as the
corpus grows. Human review takes place on GitHub; Lean verification is a separate
check. A correct formal proof still needs review to establish that it expresses
the intended mathematics.

## Main components

| Location | Purpose |
| --- | --- |
| [`corpus/`](corpus/) | Entries, figures, node records, mathematical areas, and reading order; see the [corpus guide](docs/corpus.md) |
| [`formal/`](formal/) | One Lean project containing local definitions and proofs, with pinned mathlib dependencies; see the [formalization guide](docs/formal.md) |
| [`app/`](app/) | A Django reader, templates, CSS, JavaScript, and commands for validation and builds; see the [app guide](docs/app.md) |
| [`prompts/`](prompts/) | Six independently runnable Markdown instructions for authors and AI agents |
| [`docs/`](docs/README.md) | Detailed documentation and maintenance guides |

There is no database, migration step, or frontend build. The server reads local
files; the build precomputes verification summaries so listing pages need only
entry metadata. KaTeX, used to display mathematical notation, is bundled locally.

## Setup

Clone this repository and open a terminal in its root directory. You need Git,
Python 3.12–3.14, [uv](https://docs.astral.sh/uv/getting-started/installation/) for
Python dependencies, and Lean for proof builds, node source browsing, and the full
test suite. Commands below run from the repository root unless they explicitly
change directory.

### Python environment

Install uv using its linked platform instructions. On macOS or Linux:

```sh
curl -LsSf https://astral.sh/uv/install.sh | sh
```

Open a new terminal if needed so `uv` is on your `PATH`. Then install a supported
Python and the locked project dependencies:

```sh
uv python install 3.12
uv sync --locked --python 3.12
uv run python app/manage.py validate_corpus
```

uv creates a local `.venv/`; `uv run` uses it without manual activation.
`validate_corpus` checks content structure and references without Lean, a prior
build, or any file writes, so it is also useful while drafting an entry.

### Lean environment

Install [Elan, Lean's version manager](https://github.com/leanprover/elan#installation).
On macOS or Linux:

```sh
curl https://elan.lean-lang.org/elan-init.sh -sSf | sh
```

For Windows, use the installer on the linked Elan page. Open a new terminal after
installation so `elan`, `lean`, and `lake` are on your `PATH`. Lake is Lean's build
and dependency tool; Elan selects the version pinned by this repository when run
inside `formal/`.

From the repository root:

```sh
cd formal
lake --version
lake exe cache get
cd ..
uv run python app/manage.py build
uv run python app/manage.py validate_corpus --check-sources
uv run python app/manage.py test catalog
```

The first Lake command installs the pinned toolchain if it is missing.
`lake exe cache get` fetches dependencies and cached mathlib build files, avoiding
compiling the whole library locally. Initial setup needs network access and can
take time. Keep [lean-toolchain](formal/lean-toolchain),
[lakefile.toml](formal/lakefile.toml), and [lake-manifest.json](formal/lake-manifest.json)
unchanged during ordinary authoring; `lake update` is for dependency upgrades.

The Django `build` command compiles Lean and refreshes node verification,
declaration signatures, source lines, and entry summaries. **Verified** means
the declaration uses no unfinished proof (`sorry`), including through its actual
dependencies, and no unsupported axioms. A build can succeed with unfinished
nodes marked **Not verified**. A compilation or declaration-check failure leaves
previous saved results intact. See the [verification rules](docs/formal.md#build-and-verification).

### Run the reader

```sh
uv run python app/manage.py runserver
```

Open <http://127.0.0.1:8000/>. Browse an area to open an entry, then use its
formalization badges to inspect nodes and their Lean sources. Verification badges
reflect the last successful build; requests do not run Lean. After changing
content mappings or proofs, rerun `build` and include the generated JSON changes.
Stop the development server with Ctrl+C.

For production settings, the read-only API, and performance details, see the
[app guide](docs/app.md).

## Contributing

Start with [CONTRIBUTING.md](CONTRIBUTING.md). It describes the complete six-step
pipeline, what each step produces, how to run an individual step with an AI agent,
and which checks to run before submitting changes. The [documentation index](docs/README.md)
links to the content contracts, proof rules, and app maintenance guide.
