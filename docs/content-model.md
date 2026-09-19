# Content and machine access

An entry is a reading unit containing definitions, lemmas, theorems, questions,
proofs, and explanatory material. Each mathematical block is independently
addressable by `(entry_id, block_id)`.

The implemented metadata contract is in the [authoring guide](entry-sources.md).
Entry metadata contains identity, `based_on` citations, subject memberships,
editorial status, reading time, summary, abstract, and blocks. Citations record
authors, title, and optional publication details, DOI, and URL. Each block contains
only formalization and references.
The HTML owns block titles, kinds, and order. Git records history; the metadata
contains no version counters or separate proof records.

This file contract is the current storage model for corpus construction and
formalization experiments. Experiment inputs, model attempts, costs, and human
review time should live in separate run records, not in the entry schema. The
run-record format is still proposed; see the [experiment plan](formalization-experiments.md).

## Numbering and navigation

Number blocks by kind within each entry: Definition 1, Definition 2, Lemma 1,
Lemma 2, Theorem 1, Question 1. Display numbers are derived, never identifiers.
Local references show these labels; cross-entry references show the result name.
The reader returns to the citing block, reopening an answer when necessary.

Equations and figures have separate entry-local labels and numbers. Figure links
use stable HTML IDs and display their generated numbers; they are not mathematical
block dependencies and do not belong in JSON `references`. Tables and diagrams are
part of the human source. Assets stay in their entry folder. Categories form a
browsing hierarchy, while reading order is stored explicitly by primary area.
Only `corpus/entries/` and the working `taxonomy.json` are live inputs; archived
notes in `corpus/backup/` and `taxonomy_complete.json` stay outside the reader.
An entry's stable folder and `/entries/<id>/` URL do not encode its category.

## Formalization

Each block records a status (`not_started`, `partial`, or `complete`), declaration,
source path, report path, module, and `unformalized_dependencies`. The latter is
a list of links to local Lean statements with unfinished proofs (using `sorry`),
each identified by `declaration`, `module`, and `source`. A nonempty list is
incompatible with `complete`. Already-proved
mathlib lemmas do not belong on this list. References identify only
the target entry and block. Existing mathlib declarations are valid bindings;
they do not require duplicate proofs under Lemmatheca. Local formal code remains
in `formal/Lemmatheca/` and can support multiple entries.

The entry's formalization status is derived from all its block statuses. For a
question, the status describes its answer or counterexample. Definitions count
too. Missing work keeps the entry partial or not started; successful checking of
one result never makes another result complete.

Formal completeness and editorial publication are independent. A maintainer must
check that the formal declaration expresses the intended human mathematics.
An axiom report does not automatically establish that correspondence or enumerate
all mathematical dependencies. Pending statements are listed per block, with no
global exception registry. Removing the final pending statement does not by itself
make a formalization complete: its Lean binding must also pass verification.

## Sources and attribution

Display external sources as **Based on:** citations, linking titles and DOIs when
available. Original material may use an empty citation list. Entry authorship and
licensing are no longer fields in this reader's metadata. Preserve upstream
attribution in formal sources. A maintainer decides what is published; AI
recommendations do not change the editorial status.

## Later AI access

Local agents can read the existing corpus files and pinned Lean sources directly.
An HTTP API is not needed for the initial formalization pilot. Reading order,
taxonomy, bibliography, and block references already supply useful context, though
they do not constitute the complete formal dependency graph.

A read-only API can expose the same entry JSON, parsed blocks, HTML, assets, Lean
bindings, and direct dependency links. Git commits and content hashes can identify
a reproducible corpus snapshot without adding per-entry version fields. Agents
should be able to retrieve an entire snapshot or a bounded dependency closure.

Keep formal dependencies separate from expository citations: a formal helper may
be invisible in the human proof, and a background reading link may not occur in the
proof term. The full graph extractor and public API remain future work. Initially,
lexical search, declaration lookup, and graph traversal should be sufficient.
Research agents may propose results; additions still pass through a human workflow.
