# Reference backlog

This document collects useful corpus references to add as mathematical areas
develop. Familiar background may be used without a link: elementary arithmetic,
ordinary classical reasoning, and standard facts about real numbers need not be
reproved in every entry. Their absence from the corpus does not by itself block
an entry. See the [prerequisite and scope policy](../CONTRIBUTING.md#prerequisites-and-scope).

Entries should have no major dependencies on substantial theory missing from the
corpus. Such a dependency requires a supporting development, a narrower scope, or
deferral of the dependent material. Listing it here does not satisfy that requirement.
Nor does a planned link repair a false claim or incompatible assumptions.

## Maintaining the list

- Identify consuming locations by stable entry and block IDs, independently of
  reading order and area membership. Group repeated uses of the same background.
- Record the exact fact a reference should establish. A related title or an
  available Lean declaration alone is insufficient human coverage.
- During drafting or an authorized revision, inspect suitable new target blocks,
  check their assumptions, add `entry-id#block-id` links where useful, and remove
  the fulfilled locations from this list. Keep any remaining uses or missing facts.
- Planning and review steps propose changes in their handoff and remain read-only.
  Keep this backlog outside corpus metadata; it is not an approval or readiness system.

## Background references from the set-theory audit

The initial list records the background uses identified in the audit of the
18 existing set-theory entries. Proposed titles below are suggestions for future
coverage, not existing entries or authorization to create them. When a block
already supplies the fact, the remaining task is only to add a useful reference.

| Consuming entry/block IDs | Background used | Coverage to reference when useful |
| --- | --- | --- |
| `sets-and-maps#statements-and-conventions`; `axiomatic-set-theory#membership-language`; classical reasoning throughout the corpus | Connectives, quantifiers, equality, excluded middle, and contradiction; the distinction between a formula and an axiom schema | The existing notation blocks supply introductory context. A future mathematical-logic entry, **First-order logic: languages, formulas, structures, and truth**, can supply deeper coverage. Basic proof reasoning remains acceptable background. |
| `finite-and-countable-sets#finite-sets`; elementary natural-number arguments and examples in `sets-and-maps`, `equivalence-relations`, and `ordered-sets` | Natural-number arithmetic, induction, and least elements of nonempty subsets of the naturals | Existing targets: [induction on omega](../corpus/entries/natural-numbers-as-sets/entry.html#induction-on-omega), [natural order](../corpus/entries/natural-numbers-as-sets/entry.html#natural-order), and the arithmetic-law blocks in that entry. Links should clarify the background without making elementary examples depend on the set-theoretic construction. |
| `equivalence-relations#relation-properties`; `equivalence-relations#equivalence-classes`; `ordered-sets#orders-from-inclusion-and-divisibility`; `finite-and-countable-sets#integer-enumeration`; `finite-and-countable-sets#rational-enumeration` | Familiar integer and rational arithmetic, parity, divisibility, and positive-denominator fractions | Existing targets: [integers as an ordered ring](../corpus/entries/constructing-number-systems/entry.html#integers-ordered-ring) and [rationals as an ordered field](../corpus/entries/constructing-number-systems/entry.html#rational-field). These cover arithmetic structure; a future number-theory entry, **Divisibility and remainders: division, parity, and congruence**, could supply the remaining arithmetic facts. |
| `sets-and-maps#maps`; `sets-and-maps#composition`; `sets-and-maps#kinds-of-maps`; `ordered-sets#suprema-and-infima`; `ordered-sets#preorders`; `comparing-sizes#real-interval-sizes` | Elementary real arithmetic, order, absolute value, interval notation, and affine or rational formulas | Existing target for the underlying structure: [the complete ordered field](../corpus/entries/constructing-number-systems/entry.html#unique-complete-ordered-field). A future real-analysis entry, **Real numbers: order, completeness, and approximation**, can give a more direct reference for routine use of familiar reals. |
| `sets-and-maps#formula-question`; `sets-and-maps#kinds-of-maps` | Every nonnegative real has a unique nonnegative square root; negative reals have no real square root | A future real-analysis entry, **Real numbers: order, completeness, and approximation**, should establish general square-root existence and uniqueness. The existing number-systems entry constructs an irrational square root of two, which alone does not cover the general claim. |
| `comparing-sizes#uncountable-reals` | Every real in the open unit interval has a unique decimal expansion that is not eventually all nines; digit strings used in the diagonal argument represent reals | A future real-analysis entry, **Positional expansions: digits, representation, and uniqueness**, should prove existence, the ambiguity of terminating expansions, and the canonical convention. This standard background is acceptable in the current diagonal proof. |
| `infinite-cardinal-arithmetic#size-of-the-continuum` | Archimedeanness, rational density, and integer-part bounds used to separate two reals | Existing targets: [rational approximation of cuts](../corpus/entries/constructing-number-systems/entry.html#cut-approximations) and [completeness and rational density in an ordered field](../corpus/entries/constructing-number-systems/entry.html#unique-complete-ordered-field). A future real-analysis entry can provide a direct integer-part formulation. |
| `infinite-cardinal-arithmetic#size-of-the-continuum` | Bounded monotone sequences converge; the ternary partial sums define a real; geometric tail estimates separate codes | A future real-analysis entry, **Real sequences and series: convergence, completeness, and geometric sums**, should establish these facts. Existing [cut completeness](../corpus/entries/constructing-number-systems/entry.html#cut-completeness) provides their foundation. These limited standard facts may remain background in the current proof; a short local partial-sum/supremum argument is another possible improvement. |

Applications of the continuum result in `infinite-cardinal-arithmetic`,
`ordinal-powers`, and `infinite-sums-and-products` can continue to reference the
set-theory result itself. They need not each acquire duplicate analysis links.

## Boundaries of the set-theory expansion

The current corpus develops dense-order characterizations, normal functions and
Goodstein termination, and elementary continuum-function calculations from its
existing set-theoretic prerequisites. The following extensions need substantial
theory beyond those arguments and are deferred:

| Related entry/block IDs | Deferred material | Supporting development needed |
| --- | --- | --- |
| `continuum-function#continuum-restrictions`; `continuum-function#strong-limits-and-sch` | Easton's realization theorem for continuum functions on regular cardinals; consistency or independence results about GCH and SCH | Begin mathematical logic with **First-order logic: formulas, structures, and satisfaction** and **Models of set theory: relativization and absoluteness**, then set theory with **Forcing: partial orders, generic filters, and extensions**. A precise Easton statement must specify its model and cardinal-preservation framework; necessary inequalities alone are not a realization theorem. |
| `normal-functions#goodstein-termination` | Unprovability of Goodstein's theorem in Peano arithmetic | **Formal arithmetic: axioms, syntax, and provability**, followed by **Ordinal analysis: induction strength and arithmetic proofs**. The present entry proves termination using ordinals; it makes no assertion about formal provability in arithmetic. |
