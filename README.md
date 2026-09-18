# Lemmatheca

A mathematical library for people to read, Lean to check, and AI agents to explore.
Readers browse areas and subareas, follow definitions and prerequisites, and enjoy
explanatory proofs. Contributors submit human mathematics. AI assists with
formalization and review; a selected human maintainer decides what is published.

**Current status: a browsable web prototype, draft examples, and a first Lean project.**
The [web app](app/README.md) has area/subarea navigation and two linked mathematical
notes containing definitions, numbered results, proofs, and collapsible answers.
References point to specific results by name. Entry pages show authors, license,
optional source credits, and formalization badges derived from block statuses.
Completed formalizations and pending dependencies link to a shared Lean file viewer.
Equation references and tables are supported. Login and submission are
placeholders. The [formal project](formal/README.md) checks both general statements
and their supporting lemmas and counterexamples using Lean 4.34.0 and pinned mathlib, alongside the original concrete integer
example. There is no verification service or maintainer-approved corpus yet;
the examples remain editorial drafts awaiting maintainer review. A further integer
sumset bound has a human proof and links to two Lean helper statements with `sorry`
proofs, so its entry shows a partial badge.

The website currently uses Django templates, plain CSS, and self-hosted KaTeX
loaded only on proof pages. There is no browser framework or database requirement.
The longer-term design adds a versioned mathematical corpus, PostgreSQL for
operational data, and isolated Lean workers.

Run the web app from the repository root:

```sh
uv sync --locked
uv run python app/manage.py runserver
```

Then open <http://127.0.0.1:8000/>.

A web-only checkout does not need Lean or mathlib installed: it reads the committed
verification reports. If mathlib sources are absent from the Git-ignored
`formal/.lake/` directory, their viewer offers the source at the pinned GitHub
commit. Local Lean sources and reports must still be deployed with the corpus.

Start with these documents:

| Document | What it specifies |
| --- | --- |
| [Architecture](docs/architecture.md) | Tools, folders, website, storage, deployment, and implementation order |
| [Content model](docs/content-model.md) | Compact entry metadata, mathematical blocks, taxonomy, and AI access |
| [Entry source layout](docs/entry-sources.md) | Entry folders, HTML authoring, assets, reading order, and Lean module bindings |
| [Verification and review](docs/verification-and-review.md) | Lean checks, pending formalization dependencies, translation, beauty grading, and maintainer authority |
| [Mathematical baseline](docs/baseline.md) | A small starting collection, explicit hypotheses, human proofs, and dependency plans |
| [Mathematical corpus](corpus/README.md) | Two HTML/JSON sumset notes with local assets and cross-references |
| [First Lean proofs](formal/README.md) | Compilable sumset example, supporting lemmas, and axiom checks |
| [Web app](app/README.md) | Run the website, edit its content, and check navigation |

Three distinctions shape the project:

1. Lean checks a formal statement. A maintainer must also check that this is the
   intended statement and that its proof follows the submitted human argument.
2. Bind blocks to local Lean or existing mathlib declarations. List statements
   with unfinished Lean proofs under each block's `unformalized_dependencies`; a nonempty
   list prevents complete status. Foundational axioms are checked separately.
3. Correctness is a publication requirement. Beauty is a reasoned editorial
   judgment; AI grades never grant publication permission.

Build one complete path first: **sumset definition → cardinality bound → human
proof → faithful Lean proof → dependency report → maintainer approval → readable
page and JSON export**. Expand the mathematical coverage after that path works.
