# Lemmatheca

A mathematical library for people to read, Lean to check, and AI agents to explore.
The first goal is to measure AI formalization, then build connected standard
mathematics from books and mathlib. Advanced papers, autonomous research, and
public contributions come later.

## Submission and formalization pipeline

1. Write human mathematics in `entry.html`, with metadata in `entry.json`.
2. Propose reusable formal nodes and link blocks to them with `data-formal`.
   A maintainer reviews the statements and their coverage of the human text.
3. Prove approved statements using Lean and existing nodes. Maintainers decide
   what enters the library; AI supplies proposals and recommendations.

Measure statement writing and proof translation separately. Binding an existing
mathlib result is useful corpus work, but does not show that a human argument was
translated. See the [experiment plan](docs/formalization-experiments.md).

## Current implementation

A file-backed corpus, a Django reader, and a local Lean checker. The frontend uses
plain HTML/CSS/JavaScript and self-hosted KaTeX. There is no database or frontend
build step. Accounts, submissions, and autonomous AI workflows are not implemented.

| Folder | Purpose |
| --- | --- |
| [`corpus/`](corpus/README.md) | Entry sources, assets, taxonomy, and reading order |
| [`formal/`](formal/README.md) | Formal nodes, Lean modules, and verification reports |
| [`app/`](app/README.md) | Reader, node pages, and read-only formal API |
| [`docs/`](docs/architecture.md) | Architecture, authoring, and experiment design |

## Run and check

From the repository root, with Python 3.12–3.14 and uv:

```sh
uv sync --locked
uv run python app/manage.py runserver
```

Open <http://127.0.0.1:8000/>. To validate changes:

```sh
uv run python app/manage.py validate_corpus
uv run python app/manage.py test catalog
```

With the [Lean environment](formal/README.md) installed:

```sh
uv run python app/manage.py check_formalizations
```

Serving the website does not require Lean or mathlib installed. Keep the tracked
corpus, Lean sources, reports, and Lake manifest; missing mathlib sources link to
the pinned upstream version. Page requests never run Lean.

## Further reading

- [Architecture](docs/architecture.md) and [content model](docs/content-model.md)
- [Entry authoring](docs/entry-sources.md) and [verification and review](docs/verification-and-review.md)
- [Experiment plan](docs/formalization-experiments.md) and [mathematical baseline](docs/baseline.md)
