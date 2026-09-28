# Entry workflow prompts

These prompts describe the active repository architecture. Paths inside a prompt
are relative to the repository root. Fill in the inputs before using a prompt and
carry the agreed scope and relevant review findings into the next step.

1. [Choose sources and scope](add-entry/01-choose-sources.txt).
2. [Draft the human entry](add-entry/02-draft-human-entry.txt).
3. [Review the human mathematics and presentation](add-entry/03-review-human-entry.txt).
4. [Prepare formal nodes and block bindings](add-entry/04-prepare-formal-nodes.txt).
5. [Review correspondence and coverage](add-entry/05-review-correspondence.txt).
6. [Prove the selected nodes](add-entry/06-prove-nodes.txt).

Reviews produce findings for the GitHub pull request. They do not update approval
fields or automatically publish, approve, or merge anything. Address findings as
part of the requested work; the app has no review state or automated review gate.
Proving takes its scope from the user and the agreed statements, not stored hashes.

Human-only entries are supported. Leave formalization unplanned until bindings
are prepared; an empty mapping means there is nothing to formalize, not unfinished
work. The build generates the entry-list summary even for a human-only entry.

At every stage, run `uv run python app/manage.py validate_corpus`. This read-only
check needs no Lean build and accepts unplanned blocks, unbound nodes, and missing
or stale generated results. It checks the corpus structure and references without
rendering pages. Review-only steps can run it without changing saved proof data.

Before submitting changes to HTML, bindings, or proofs, run from the repository root:

```sh
uv run python app/manage.py validate_corpus
uv run python app/manage.py build
uv run python app/manage.py test catalog
```

Include generated node results and entry summaries in the change. Review-only
steps should inspect saved results and report stale or missing evidence without
rewriting the corpus. Rendering and manual correspondence checks remain necessary;
a successful Lean build alone does not establish that the prose was formalized.

The maintained contracts are [corpus/README.md](../corpus/README.md),
[formal/README.md](../formal/README.md), and [app/README.md](../app/README.md).
Keep experiment-specific budgets, retrieval rules, attempts, and measurements in a
separate run specification and logs rather than adding them to corpus metadata.
