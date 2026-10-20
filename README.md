# Lemmatheca

See the [build guide](docs/build.md) for corpus builds, validation, flags, and
generated files.

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

## Main components

| Location | Purpose |
| --- | --- |
| [`corpus/`](corpus/) | Entries, figures, node records, mathematical areas, reading order, reference planning, and source errors; see the [corpus guide](docs/corpus.md) |
| [`formal/`](formal/) | One Lean project containing local definitions and proofs, with pinned mathlib dependencies; see the [formalization guide](docs/formal.md) |
| [`app/`](app/) | A Django reader, templates, CSS, JavaScript, and commands for validation and builds; see the [app guide](docs/app.md) |
| [`prompts/`](prompts/) | Six independently runnable Markdown instructions for authors and AI agents |
| [`docs/`](docs/README.md) | Detailed documentation and maintenance guides |

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
uv run python app/manage.py build --no-lean
```

uv creates a local `.venv/`; `uv run` uses it without manual activation.
This setup works without Lean. Choose other build and check modes from the
[build guide](docs/build.md#flags-and-combinations).

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
uv run python app/manage.py build --check-sources
uv run python app/manage.py test catalog
```

The first Lake command installs the pinned toolchain if it is missing.
`lake exe cache get` fetches dependencies and cached mathlib build files, avoiding
compiling the whole library locally. Initial setup needs network access and can
take time. Keep [lean-toolchain](formal/lean-toolchain),
[lakefile.toml](formal/lakefile.toml), and [lake-manifest.json](formal/lake-manifest.json)
unchanged during ordinary authoring; `lake update` is for dependency upgrades.

### Run the reader

```sh
uv run python app/manage.py runserver
```

Open <http://127.0.0.1:8000/>. Browse an area to open an entry, then use its
formalization badges to inspect nodes and their Lean sources. Stop the
development server with Ctrl+C.

For production settings, the read-only API, and performance details, see the
[app guide](docs/app.md).

## Contributing

Follow [CONTRIBUTING.md](CONTRIBUTING.md) for the six-step authoring pipeline,
scope rules, source reviews, and required checks. Entries can be contributed
before their formalization is complete; human review and Lean verification are
separate responsibilities. The [documentation index](docs/README.md) links to
the content contracts, proof rules, registries, and app maintenance guide.
