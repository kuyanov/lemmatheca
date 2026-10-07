# Reference planning and scope notes

The [reference backlog](reference-backlog.md) contains only upcoming links from
current entries to future mathematical areas. This document keeps existing-target
integration notes, plans for entries not yet drafted, and deferred extensions.
These notes do not authorize new entries or establish that their prerequisites
are complete. Maintenance rules and the distinction between accepted background
and substantial missing theory belong in the
[prerequisite and scope policy](../CONTRIBUTING.md#prerequisites-and-scope).

The initial background audit covered 18 set-theory entries. The subsequent audit
covered **Finite errors and countable diagonalization**, **Almost disjoint
families**, **Boolean algebras**, **Clubs and stationary sets**, **Pressing down and
delta-systems**, and **Infinite trees**. Their current core arguments are supplied
locally or by existing links. Proposed titles here and in the backlog are
suggestions for coverage, not existing entries.

## Existing-target integration notes

When revising a consuming entry, inspect the target block and its assumptions,
then add a link where it helps. These locations belong here rather than in the
future-area backlog because the targets already exist. Some targets provide only
a foundation for the fuller future-area treatment.

| Consuming entry/block IDs | Existing coverage | Integration note |
| --- | --- | --- |
| `sets-and-maps#statements-and-conventions`; `axiomatic-set-theory#membership-language`; classical reasoning throughout the corpus | The current notation blocks supply introductory logical context. | Deeper first-order logic remains a future-area reference. Basic classical proof reasoning is acceptable background. |
| `finite-and-countable-sets#finite-sets`; elementary natural-number arguments and examples in `sets-and-maps`, `equivalence-relations`, and `ordered-sets` | [Induction on omega](../corpus/entries/natural-numbers-as-sets/entry.html#induction-on-omega), [natural order](../corpus/entries/natural-numbers-as-sets/entry.html#natural-order), and the arithmetic-law blocks in that entry | These establish arithmetic, induction, and least elements of nonempty subsets of the naturals. Links should clarify the background without making elementary examples depend on the set-theoretic construction. |
| `equivalence-relations#relation-properties`; `equivalence-relations#equivalence-classes`; `ordered-sets#orders-from-inclusion-and-divisibility`; `finite-and-countable-sets#integer-enumeration`; `finite-and-countable-sets#rational-enumeration` | [Integers as an ordered ring](../corpus/entries/constructing-number-systems/entry.html#integers-ordered-ring) and [rationals as an ordered field](../corpus/entries/constructing-number-systems/entry.html#rational-field) | These cover the arithmetic structure and positive-denominator fractions. The future number-theory row concerns parity, divisibility, and congruence rather than duplicating this construction. |
| `sets-and-maps#maps`; `sets-and-maps#composition`; `sets-and-maps#kinds-of-maps`; `ordered-sets#suprema-and-infima`; `ordered-sets#preorders`; `comparing-sizes#real-interval-sizes` | [The complete ordered field](../corpus/entries/constructing-number-systems/entry.html#unique-complete-ordered-field) | This supplies the underlying structure. The future analysis treatment can give direct references for routine arithmetic, order, absolute value, intervals, and real formulas. The constructed irrational square root of two alone does not cover general square-root existence. |
| `infinite-cardinal-arithmetic#size-of-the-continuum` | [Rational approximation of cuts](../corpus/entries/constructing-number-systems/entry.html#cut-approximations) and [completeness and rational density in an ordered field](../corpus/entries/constructing-number-systems/entry.html#unique-complete-ordered-field) | These support the rational-separation argument. A future analysis entry can give a direct integer-part formulation. |
| `infinite-cardinal-arithmetic#size-of-the-continuum` | [Cut completeness](../corpus/entries/constructing-number-systems/entry.html#cut-completeness) | This is a foundation for bounded monotone convergence and the ternary-series argument. The limited standard facts may remain background; a short local partial-sum/supremum argument is another possible improvement. |
| `boolean-algebras#boolean-operations`; `boolean-algebras#elementary-boolean-laws`; `boolean-algebras#adjoining-an-element` | [Infima and suprema](../corpus/entries/ordered-sets/entry.html#suprema-and-infima) and [power-set bounds](../corpus/entries/ordered-sets/entry.html#power-set-bounds) | These supply the order background. The Boolean entry defines its lattice structure and proves the complement laws it needs; the future lattice entry should give the general laws and examples. |

Applications of the continuum result in `infinite-cardinal-arithmetic`,
`ordinal-powers`, and `infinite-sums-and-products` can continue to reference the
set-theory result itself. They need not each acquire duplicate analysis links.

## Cross-area correspondence to establish

These comparisons are not claims currently used in the entries. Prove the
correspondence in the relevant future area before using it as a reference for the
current order-based treatment.

| Current entry/block IDs | Future treatment | Correspondence and limits |
| --- | --- | --- |
| `infinite-trees#sequence-trees`; `infinite-trees#konigs-lemma`; `almost-disjoint-families#binary-prefix-family` | Graphs, paths, rooted trees, and graph-theoretic König's lemma | In a nonempty restriction-closed tree of finite words, edges from a word to its one-letter extensions give a connected acyclic rooted graph. Prefixes give the unique root-to-node path, and infinite rays starting at the root correspond to cofinal branches when the tree has height omega. Restrict this bridge to finite words: general transfinite order trees can have several roots, and limit-height nodes need not have immediate predecessors. |
| `clubs-and-stationary-sets#closed-unbounded`; `clubs-and-stationary-sets#closure-points` | Order topology on ordinals | For a subset of a fixed ordinal, prove that closure under limits below that ordinal agrees with order-topology closedness, including endpoints and the supremum formulation. The current entry proves its ordinal closure properties directly; it needs no topological theorem or compactness claim. |

## References available for the planned expansion

The planned entries below have no drafted block IDs yet. During drafting,
identify the actual consuming blocks and add links only where their arguments
use the stated facts. These rows identify useful existing targets, not complete
prerequisite coverage for each planned entry.

| Planned consuming entries | Existing coverage and exact fact | Remaining scope to develop |
| --- | --- | --- |
| **Partition relations: Ramsey's theorem and infinite colourings** | [König's lemma](../corpus/entries/infinite-trees/entry.html#konigs-lemma) supplies a cofinal branch in a height-omega tree with finite levels, useful for deriving finite Ramsey bounds from an infinite result through a tree of counterexamples. | Construct that counterexample tree with compatible restrictions; prove the Ramsey statements separately. König's lemma alone is not a partition theorem. |
| **Suslin trees and diamond**; **Martin's axiom** | [Branches and antichains](../corpus/entries/infinite-trees/entry.html#branches-and-antichains) fix the tree notions; [Aronszajn existence](../corpus/entries/infinite-trees/entry.html#aronszajn-existence) gives a tree with countable levels and no uncountable branch; [diagonal club intersection](../corpus/entries/clubs-and-stationary-sets/entry.html#diagonal-intersection) and [Fodor's lemma](../corpus/entries/pressing-down-and-delta-systems/entry.html#fodors-lemma) supply the ordinal combinatorics. | Define Suslin trees and diamond, prove the prediction and construction arguments, and develop the forcing framework for the Martin's axiom application. An Aronszajn tree need not be Suslin. |
| **Sets of reals: Cantor space, Baire space, and perfect sets**; **Borel sets**; **Analytic sets** | [Sequence trees](../corpus/entries/infinite-trees/entry.html#sequence-trees) identify binary sequences with cofinal branches; [binary-prefix coding](../corpus/entries/almost-disjoint-families/entry.html#binary-prefix-family) gives an explicit encoding of finite binary words. | Supply the product topology, cylinders, closed-set/tree correspondence, and the relevant countable constructions before the Borel and analytic results. The existing tree results provide the combinatorics, not these topological or descriptive-set-theoretic theorems. |
| **Forcing extensions**; **Preserving cardinals**; **Cohen reals**; **Iterated forcing**; **Martin's axiom** | [Finite partial maps](../corpus/entries/pressing-down-and-delta-systems/entry.html#finite-partial-maps) prove that two binary maps have a common extension exactly when they agree on their overlap. The [uncountable compatible-family theorem](../corpus/entries/pressing-down-and-delta-systems/entry.html#uncountable-compatible-family), using the [delta-system lemma](../corpus/entries/pressing-down-and-delta-systems/entry.html#delta-system-lemma), gives an uncountable pairwise compatible subfamily. | Define the forcing order, incompatibility, the Knaster property, and ccc, then prove the appropriate preservation or iteration theorems. Distinguish incomparability from incompatibility. A Boolean-algebra presentation additionally needs its own treatment of Boolean completions; [Boolean filters](../corpus/entries/boolean-algebras/entry.html#ideals-and-filters) alone do not provide it. |
| **Ultraproducts**; **Measurable cardinals** | [Ultrafilter extension](../corpus/entries/filters-and-ultrafilters/entry.html#ultrafilter-extension) supplies ordinary ultrafilters under choice; [Boolean ultrafilters](../corpus/entries/boolean-algebras/entry.html#boolean-ultrafilters) explain complement decisions in the algebraic setting. | First-order syntax and satisfaction are needed for Łoś's theorem. Measurability additionally requires a nonprincipal complete ultrafilter and a well-founded ultrapower argument. Neither ordinary ultrafilter extension nor the completeness of the club filter establishes a measure. |

## Boundaries of the set-theory expansion

The current corpus develops dense-order characterizations, normal functions and
Goodstein termination, and elementary continuum-function calculations from its
existing set-theoretic prerequisites. The recent entries likewise stop at
algebraic Stone representation, countable diagonal arguments, elementary
stationary-set combinatorics, and the construction of an Aronszajn tree. The
following extensions need further development and are deferred:

| Related entry/block IDs | Deferred material | Supporting development needed |
| --- | --- | --- |
| `continuum-function#continuum-restrictions`; `continuum-function#strong-limits-and-sch` | Easton's realization theorem for continuum functions on regular cardinals; consistency or independence results about GCH and SCH | Begin mathematical logic with **First-order logic: formulas, structures, and satisfaction** and **Models of set theory: relativization and absoluteness**, then set theory with **Forcing: partial orders, generic filters, and extensions**. A precise Easton statement must specify its model and cardinal-preservation framework; necessary inequalities alone are not a realization theorem. |
| `normal-functions#goodstein-termination` | Unprovability of Goodstein's theorem in Peano arithmetic | **Formal arithmetic: axioms, syntax, and provability**, followed by **Ordinal analysis: induction strength and arithmetic proofs**. The present entry proves termination using ordinals; it makes no assertion about formal provability in arithmetic. |
| `boolean-algebras#stone-map`; `boolean-algebras#stone-representation` | Topological Stone representation: the ultrafilters form a compact Hausdorff zero-dimensional space, and the represented algebra is exactly its clopen algebra | Begin with **Topological spaces: open sets, continuity, and compactness**, then **Stone spaces: Boolean algebras and compact zero-dimensional spaces**. Prove that the sets represented by Boolean elements form a clopen basis, establish compactness, and use it to show that every clopen set is a finite union of basis sets. The current theorem represents an algebra as a subalgebra of a power set without topology. |
| `finite-errors-and-countable-diagonalization#finite-error-equivalence`; `finite-errors-and-countable-diagonalization#countable-pseudointersection`; `boolean-algebras#set-algebra-examples`; `almost-disjoint-families#almost-disjoint` | The quotient Boolean algebra of subsets of the naturals modulo finite sets; almost inclusion as its order and almost disjointness as zero meet | **Equality modulo finite errors: quotients and Boolean operations** should prove that union, intersection, and complement are independent of representatives, then identify the quotient order. Infinite pseudointersections correspond to nonzero lower bounds; allowing the zero class would lose the infinitude requirement. The current entries prove finite-error equivalence and Boolean laws, but do not yet construct this quotient. |
| `finite-errors-and-countable-diagonalization#countable-pseudointersection`; `finite-errors-and-countable-diagonalization#countable-eventual-bound`; `finite-errors-and-countable-diagonalization#no-countable-ultrafilter-base`; `almost-disjoint-families#countable-family-extension`; `almost-disjoint-families#continuum-maximal-family` | Cardinal invariants defined by pseudointersections, eventual bounding and domination, ultrafilter bases, and infinite maximal almost disjoint families; comparisons and possible different values | **Cardinal characteristics of the continuum: small families and diagonal obstructions** should define the minima and prove their elementary bounds and comparisons. In the almost-disjoint invariant, restrict to infinite maximal families: finite maximal families already exist. Claims that particular values or inequalities are independent require a models-and-forcing development; the current countable obstructions do not establish them. |
| `pressing-down-and-delta-systems#delta-system-lemma`; `pressing-down-and-delta-systems#delta-systems` | Quantitative finite sunflower bounds and their combinatorial applications | A future finite-combinatorics entry, **Sunflowers: common cores and finite family bounds**, should state and prove the size estimates with their parameters. The present uncountable delta-system lemma concerns uncountable families of finite sets, not a numerical bound for a finite family. |
| `infinite-trees#branches-and-antichains`; `infinite-trees#aronszajn-existence` | Tree forcing, specialization, and the effect of forcing axioms on Suslin or Aronszajn trees | Develop **Forcing extensions: conditions, generic filters, and names**, **Preserving cardinals: chain conditions and closure in forcing**, and the relevant tree-forcing constructions. State the order and hypotheses for each construction; the current existence proof supplies no generic extension or preservation theorem. |
