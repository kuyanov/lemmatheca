# Reference backlog and planning

This document collects pending references and their planning context for the
corpus. The [upcoming references](#upcoming-references) section contains one
four-column table of links from current entry blocks to future mathematical
areas. Existing-target integration, cross-area correspondences to establish,
references for planned entries, and deferred extensions have their own sections
below. The [mathematical-logic source collection and development plan](#mathematical-logic-sources-and-development-plan)
sets out the area's further development and proposed reading order.

These notes do not authorize new entries or establish that their prerequisites
are complete. Maintenance rules and the distinction between accepted background
and substantial missing theory belong in the
[prerequisite and scope policy](../CONTRIBUTING.md#prerequisites-and-scope).
Titles without links to corpus entries are suggestions for future coverage.

## Upcoming references

| Future area | Proposed reference coverage | Consuming entry/block IDs | Fact or context to reference |
| --- | --- | --- | --- |
| Mathematical logic | **Quantifier elimination: replacing formulas by quantifier-free equivalents** | `first-order-normal-forms#prenex-normal-form` | Prenex conversion moves quantifiers to a prefix. A future quantifier-elimination treatment should state the theory over which an equivalent quantifier-free formula exists, including parameter conditions. |
| Mathematical logic | **Skolemization: adding symbols for witnesses** | `first-order-normal-forms#prenex-normal-form`; `elementary-submodels#selected-witnesses` | Develop the expanded-language construction and its satisfiability correspondence, distinguishing it from same-language formula equivalence and from choosing witness functions in one fixed structure. |
| Mathematical logic | **Infinitary logic: infinite expressions and compactness boundaries** | `propositional-compactness#infinitary-conjunction-question` | The local infinite-conjunction counterexample shows why ordinary propositional compactness needs finite formulas. A broader treatment should define its allowed infinitary syntax and distinguish the compactness principles for it. |
| Mathematical logic | **Definable classes, relativization, and set-valued class recursion** | `axiomatic-set-theory#sets-and-classes`; `ordinals#transfinite-methods`; `cumulative-hierarchy#set-valued-ordinal-recursion`; `mostowski-collapse#well-founded-set-valued-recursion` | Develop the specialized set-language treatment of definable classes and recursion, using the existing syntax and schema conventions. These statements use formulas rather than quantification over arbitrary class objects; uniquely specified outputs determine recursive set-function graphs. Model relativization needs its own satisfaction argument. |
| Mathematical logic | **Models and independence: consistency witnesses and possible values** | `bounding-and-dominating-families#continuum-hypothesis-question`; `small-families-of-subsets#continuum-hypothesis-question`; `splitting-and-reaping#continuum-hypothesis-question`; `diamond-and-suslin-trees#diamond-sequences`; `diamond-and-suslin-trees#construction-boundary-question` | Develop precise relative-consistency and independence statements and explain what model witnesses establish. The conditional CH and diamond arguments already have references for implication over a theory. Their inequalities do not realize possible unequal values; the diamond construction does not establish consistency or independence of diamond. Actual realization results require the later set-theory model and forcing developments. |
| Mathematical logic | **Arithmetic theories: induction schemas and natural-number systems** | `natural-numbers-as-sets#induction-on-omega`; `natural-numbers-as-sets#unique-natural-number-system` | Induction for every subset differs from first-order induction restricted to formulas with fixed parameters. The every-subset Peano characterization yields a unique natural-number-system isomorphism; it does not assert categoricity of first-order Peano arithmetic. |
| Mathematical logic | **Back-and-forth: countable structures and partial isomorphisms** | `dense-linear-orders#finite-order-extension`; `dense-linear-orders#cantor-back-and-forth` | Alternating enumerations of two countable carriers and extending finite partial isomorphisms in both directions yields an isomorphism. The current dense-order argument supplies its extension hypotheses and proof locally; a broader logic treatment can explain the general method. |
| Number theory | **Divisibility and remainders: division, parity, and congruence** | `equivalence-relations#relation-properties`; `equivalence-relations#equivalence-classes`; `ordered-sets#orders-from-inclusion-and-divisibility`; `finite-and-countable-sets#integer-enumeration`; `equivalence-relations#rules-on-representatives`; `equivalence-relations#maps-between-quotients`; `equivalence-relations#adding-classes`; `finite-and-countable-sets#empty-and-repeated-lists`; `finite-and-countable-sets#positive-and-even-naturals`; `finite-and-countable-sets#finite-unions`; `comparing-sizes#proper-subset-question`; `comparing-sizes#bernstein-example`; `ordered-sets#chains-and-hasse-diagrams`; `ordered-sets#which-identifications-work`; `well-ordered-sets#well-founded-induction`; `constructing-number-systems#irrational-cut-question`; `filters-and-ultrafilters#ultrafilter-decision`; `filters-and-ultrafilters#partition-choice-question`; `subsets-modulo-small-sets#finite-error-quotient`; `subsets-modulo-small-sets#representative-intersection-question`; `subsets-modulo-small-sets#atomless-finite-error-quotient`; `independent-families#finite-pattern-example`; `bounding-and-dominating-families#strict-comparison-question`; `partition-relations#parity-colouring`; `partition-relations#all-arities-question`; `small-families-of-subsets#bases-have-no-pseudointersection`; `splitting-and-reaping#splitting`; `splitting-and-reaping#witnesses-and-minima`; `splitting-and-reaping#next-points-and-intervals`; `splitting-and-reaping#single-set-question` | Unique quotient and remainder, parity classes, even/odd decomposition, and congruence as divisibility of a difference; addition respects congruence for every positive modulus. Division gives periodic listings and repeated listings, while parity separates tagged lists and gives alternating-sign integer codes. Include the modulo-three pattern in the size-comparison example. Positive-integer divisibility is an order, its proper divisors have smaller natural value, and finite covers give divisor comparisons. Both natural-number parity classes are infinite and complementary; an odd square is odd, supporting the least-denominator irrationality argument. Residue classes modulo four are infinite and give the four independent Boolean cells; alternating even and odd indices split an infinite enumeration. Parity of points and finite cardinalities gives colouring examples, and both parity classes are unbounded. |
| Number theory | **Positional integer expansions: digits, finite sums, and hereditary representations** | `finite-and-countable-sets#finite-subset-family`; `comparing-sizes#finite-sequences-question`; `normal-functions#hereditary-base-representations`; `normal-functions#base-change-and-descent`; `normal-functions#goodstein-growth-question` | Finite base-b digit expansions are unique and obtained by quotient and remainder. In a sum of distinct powers of two, the largest differing exponent dominates all smaller exponents; a leading length marker separates binary words of different lengths. Recursively expanding the exponents gives canonical finite hereditary representations, and replacing the base throughout the expression defines base substitution. |
| Number theory | **Greatest common divisors and least common multiples: divisibility universal properties** | `ordered-sets#suprema-and-infima` | The greatest common divisor is the greatest common lower bound and the least common multiple is the least common upper bound in positive-integer divisibility. Reference their universal properties as well as numerical algorithms. |
| Real analysis | **Real numbers: order, completeness, and approximation** | `sets-and-maps#maps`; `sets-and-maps#composition`; `sets-and-maps#kinds-of-maps`; `ordered-sets#suprema-and-infima`; `ordered-sets#preorders`; `comparing-sizes#real-interval-sizes`; `sets-and-maps#formula-question`; `uncountable-pair-colourings#no-long-monotone-real-sequence`; `uncountable-pair-colourings#sierpinski-colouring` | Elementary real arithmetic, order, absolute value, interval notation, and affine or rational formulas. Every nonnegative real has a unique nonnegative square root; negative reals have no real square root. Rational density and countability separate adjacent terms of a strictly monotone real sequence, ruling out a sequence indexed by omega1; comparing ordinal order with distinct real values then gives Sierpiński’s colouring. |
| Real analysis | **Positional expansions: digits, representation, and uniqueness** | `comparing-sizes#uncountable-reals` | Every real in the open unit interval has a unique decimal expansion that is not eventually all nines; digit strings used in the diagonal argument represent reals. Cover terminating-expansion ambiguity and the canonical convention. |
| Real analysis | **Real sequences and series: convergence, completeness, and geometric sums** | `infinite-cardinal-arithmetic#size-of-the-continuum` | Bounded monotone sequences converge; ternary partial sums define a real; geometric tail estimates separate codes. |
| Order theory / algebra | **Lattices: meets, joins, bounds, and distributivity** | `boolean-algebras#boolean-operations`; `boolean-algebras#elementary-boolean-laws`; `boolean-algebras#adjoining-an-element`; `ordered-sets#power-set-bounds`; `ordered-sets#isomorphisms-preserve-bounds` | Binary infima and suprema imply associativity, commutativity, idempotence, and absorption. Distinguish bounded, distributive, complemented, and complete lattices; the Boolean arguments use finite lattice operations. Power-set lattices have unions and intersections as joins and meets, including empty bounds; order isomorphisms preserve bounds. |
| Order theory | **Complete lattices and monotone fixed points: Knaster–Tarski** | `ordered-sets#knaster-tarski`; `ordered-sets#fixed-point-size-comparison` | The fixed points of a monotone map on a complete lattice form a complete lattice in their induced order. The least and greatest fixed points are respectively the infimum of pre-fixed points and supremum of post-fixed points; internal fixed-point bounds need not equal ambient meets and joins. Include the power-set fixed-point proof of Cantor–Schroeder–Bernstein. |
| Algebra | **Algebraic structures: operations, homomorphisms, and substructures** | `boolean-algebras#stone-map`; `boolean-algebras#stone-representation`; `constructing-number-systems#integers-ordered-ring`; `constructing-number-systems#rational-field`; `constructing-number-systems#cuts-ordered-additive-group`; `constructing-number-systems#cut-ring-laws`; `constructing-number-systems#unique-complete-ordered-field` | Ring, integral-domain, field, and ordered-field laws; embeddings preserving constants, operations, and order. An operation- and constant-preserving map has a subalgebra as its image. The inverse of a bijective homomorphism preserves those operations and constants, including zero and one; an order-preserving field isomorphism and its inverse also preserve order. The current constructions supply their required laws locally. |
| Algebra | **Quotient operations: congruences and maps on equivalence classes** | `equivalence-relations#maps-from-quotients`; `equivalence-relations#maps-between-quotients`; `equivalence-relations#adding-classes`; `equivalence-relations#quotient-is-image`; `subsets-modulo-small-sets#representative-independence`; `subsets-modulo-small-sets#quotient-boolean-algebra`; `subsets-modulo-small-sets#ignoring-a-fixed-region` | Representative-independent unary and binary operations, unique factorization through a quotient, and the kernel-quotient-to-image bijection give the set-level pattern for algebraic quotient structures. An equivalence relation defines an algebraic congruence only when the relevant operations respect it. The ideal-of-errors quotient supplies this pattern for Boolean operations: the projection preserves operations and the fixed-region quotient is explicitly isomorphic to the remaining power set. These facts are proved locally. |
| Graph theory | **Graphs and paths: connectedness, cycles, and trees**; **Rooted trees: levels, branches, and König's lemma** | `infinite-trees#sequence-trees`; `infinite-trees#konigs-lemma`; `almost-disjoint-families#binary-prefix-family` | Finite words ordered by prefix have one predecessor at every shorter length; infinite binary sequences correspond exactly to cofinal branches; a height-omega tree with finite levels has a cofinal branch. The rooted-graph treatment concerns finite-word trees and infinite rays, while general transfinite order trees can have several roots and limit-height nodes without immediate predecessors. |
| Graph theory | **Directed graphs: paths, reachability, cycles, and Hasse diagrams** | `equivalence-relations#relation-composition`; `equivalence-relations#relation-closures`; `ordered-sets#chains-and-hasse-diagrams`; `foundation-and-rank#no-membership-cycles`; `mostowski-collapse#well-founded-and-extensional`; `mostowski-collapse#finite-collapse-example` | Relations are directed edges: positive-length paths give transitive closure, paths allowing length zero give reflexive-transitive closure, and paths allowing either edge orientation give the equivalence closure and connected-component partition. The cover graph of a finite poset recovers strict comparison by upward paths; covers alone do not recover arbitrary infinite or dense orders. Acyclicity of a finite relation implies well-foundedness, but an acyclic infinite relation need not be well-founded. Foundation excludes every positive finite membership cycle. The three-point path illustrates that an acyclic extensional relation need not be transitive. |
| Topology | **Order topology: intervals and limits on ordinals** | `clubs-and-stationary-sets#closed-unbounded`; `clubs-and-stationary-sets#closure-points` | Closure under ordinal limits below a fixed ordinal, its supremum characterization, and the closure properties of ordinal-function closure points. The order-topology treatment should cover closedness at limits and the endpoint conventions on that ordinal. |
| Finite combinatorics | **Finite subsets and finite colourings: counting and bounds** | `partition-relations#finite-colouring-trees`; `propositional-logic#truth-tables`; `propositional-normal-forms#finite-truth-functions`; `propositional-normal-forms#normal-form-theorem`; `propositional-compactness#finite-atom-stock`; `propositional-compactness#countable-atoms` | An r-element set has exactly 2^r subsets; its fixed-size subsets form a finite set. There are k^q maps from a q-element domain to k colours. The partition entry supplies the finite counting needed for its length-tagged colouring tree. A list of n distinct propositional atoms has exactly 2^n assignments to two truth values, including one empty assignment; the propositional entry proves this by doubling. |
| Graph theory | **Edge colourings and Ramsey numbers: monochromatic complete subgraphs** | `partition-relations#colourings-and-homogeneity`; `partition-relations#parity-colouring`; `partition-relations#six-point-example` | Unordered pairs are graph edges, and a pair-homogeneous set is a monochromatic complete subgraph. The six-point/two-colour triangle theorem and the five-cycle counterexample use these notions explicitly. |
| Graph theory | **Edge colourings: homogeneous sets, cliques, and independent sets** | `uncountable-pair-colourings#asymmetric-partition-relation`; `uncountable-pair-colourings#large-neighbourhood-dichotomy`; `uncountable-pair-colourings#dushnik-miller-regular` | A two-colouring of unordered pairs describes a graph by choosing one colour for edges; homogeneous sets correspond to cliques and independent sets. The entry supplies its neighbourhood recursion directly and requires no graph theory. |
| Topology | **Sequence spaces: cylinders, closed sets, and perfect kernels** | `perfect-subtrees#sequence-trees-and-branches`; `perfect-subtrees#perfect-trees`; `perfect-subtrees#perfect-kernel`; `perfect-subtrees#branch-cardinality`; `perfect-subtrees#prefix-closure-question`; `perfect-subtrees#countable-cones`; `perfect-subtrees#binary-splitting` | Finite-prefix cones become basic open cylinders, and tree bodies are closed. The largest perfect subtree and countable remainder supply the closed-set perfect kernel; passing from a family of paths to its prefix tree can add paths. All required combinatorics is proved locally. |
| Finite combinatorics | **Systems of distinct representatives: Hall's theorem and selection constraints** | `finite-constraints-and-distinct-representatives#distinct-representatives`; `finite-constraints-and-distinct-representatives#finite-hall`; `finite-constraints-and-distinct-representatives#small-obstructions-question`; `finite-constraints-and-distinct-representatives#infinite-hall` | Injective selection maps, the finite Hall counting criterion, tight-subfamily induction, and its finite-valued infinite extension are developed locally; connect them to broader finite selection theory. |
| Topology | **Compactness: finite discrete products and the finite intersection property** | `finite-constraints-and-distinct-representatives#rado-selection`; `finite-constraints-and-distinct-representatives#persistent-constraints` | The local-to-global conclusion is a compactness property of products of finite discrete spaces. Current proofs use ultrafilters directly and do not assume topology. |
| Constructive logic | **Intuitionistic natural deduction and classical contradiction** | `propositional-proofs#deduction-rules`; `propositional-proofs#classical-cases`; `propositional-proofs#soundness` | The entry includes classical contradiction and derives excluded middle from it. A future treatment should explain the intuitionistic rule system and compare its soundness with classical two-valued semantics. No constructive-logic result is required by the current proofs. |

## Existing-target integration notes

When revising a consuming entry, inspect the target block and its assumptions,
then add a link where it helps. These locations belong here rather than in the
upcoming-reference table because the targets already exist. Some targets provide only
a foundation for the fuller future-area treatment.

| Consuming entry/block IDs | Existing coverage | Integration note |
| --- | --- | --- |
| `finite-and-countable-sets#finite-sets` | [Induction on omega](entries/natural-numbers-as-sets/entry.html#induction-on-omega) and [natural order](entries/natural-numbers-as-sets/entry.html#natural-order) | Add an optional background pointer for induction and least natural numbers, keeping the elementary finite-set explanation independent of the later set-theoretic construction. |
| `equivalence-relations#relation-properties`; `equivalence-relations#equivalence-classes`; `ordered-sets#orders-from-inclusion-and-divisibility`; `finite-and-countable-sets#integer-enumeration`; `finite-and-countable-sets#rational-enumeration` | [Integers as an ordered ring](entries/constructing-number-systems/entry.html#integers-ordered-ring) and [rationals as an ordered field](entries/constructing-number-systems/entry.html#rational-field) | Add optional pointers where the arithmetic structures or positive-denominator fractions help readers; do not turn their later construction into a prerequisite for elementary examples. Parity, divisibility, and congruence still await the number-theory treatment. |
| `sets-and-maps#maps`; `sets-and-maps#composition`; `sets-and-maps#kinds-of-maps`; `ordered-sets#suprema-and-infima`; `ordered-sets#preorders`; `comparing-sizes#real-interval-sizes` | [The complete ordered field](entries/constructing-number-systems/entry.html#unique-complete-ordered-field) | Add optional pointers identifying the underlying real-number structure. Keep routine real facts as background; a future analysis entry still needs general square-root existence, absolute value, intervals, and real formulas. |

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
| **Martin's axiom** | [Branches and antichains](entries/infinite-trees/entry.html#branches-and-antichains) fix the tree notions; [Aronszajn existence](entries/infinite-trees/entry.html#aronszajn-existence) gives a tree with countable levels and no uncountable branch; [diagonal club intersection](entries/clubs-and-stationary-sets/entry.html#diagonal-intersection) and [Fodor's lemma](entries/pressing-down-and-delta-systems/entry.html#fodors-lemma) supply the ordinal combinatorics. [The diamond construction](entries/diamond-and-suslin-trees/entry.html#diamond-tree-construction) supplies a Suslin tree under its stated assumption. | Develop the forcing framework and prove the Martin's axiom application. An Aronszajn tree need not be Suslin. |
| **Sets of reals: Cantor space, Baire space, and perfect sets**; **Borel sets**; **Analytic sets** | [Sequence trees](entries/infinite-trees/entry.html#sequence-trees) identify binary sequences with cofinal branches; [binary-prefix coding](entries/almost-disjoint-families/entry.html#binary-prefix-family) encodes finite binary words. [The perfect kernel](entries/perfect-subtrees/entry.html#perfect-kernel) has a countable branch remainder, and [branch cardinality](entries/perfect-subtrees/entry.html#branch-cardinality) gives the countable-or-continuum dichotomy. | Supply the product topology, cylinders, closed-set/tree correspondence, and the relevant countable constructions before applying these combinatorial results to closed sets or developing Borel and analytic sets. |
| **Forcing extensions**; **Preserving cardinals**; **Cohen reals**; **Iterated forcing**; **Martin's axiom** | [Finite partial maps](entries/pressing-down-and-delta-systems/entry.html#finite-partial-maps) prove that two binary maps have a common extension exactly when they agree on their overlap. The [uncountable compatible-family theorem](entries/pressing-down-and-delta-systems/entry.html#uncountable-compatible-family), using the [delta-system lemma](entries/pressing-down-and-delta-systems/entry.html#delta-system-lemma), gives an uncountable pairwise compatible subfamily. | Define the forcing order, incompatibility, the Knaster property, and ccc, then prove the appropriate preservation or iteration theorems. Distinguish incomparability from incompatibility. A Boolean-algebra presentation additionally needs its own treatment of Boolean completions; [Boolean filters](entries/boolean-algebras/entry.html#ideals-and-filters) alone do not provide it. |
| **Ultraproducts**; **Measurable cardinals** | [Ultrafilter extension](entries/filters-and-ultrafilters/entry.html#ultrafilter-extension) supplies ordinary ultrafilters under choice; [Boolean ultrafilters](entries/boolean-algebras/entry.html#boolean-ultrafilters) explain complement decisions in the algebraic setting. [First-order syntax](entries/first-order-languages/entry.html#scoped-formulas) and [satisfaction](entries/first-order-structures/entry.html#satisfaction) supply the language and truth definitions. | Prove Łoś's theorem for the ultraproduct construction. Measurability additionally requires a nonprincipal complete ultrafilter and a well-founded ultrapower argument. Neither ordinary ultrafilter extension nor the completeness of the club filter establishes a measure. |

## Boundaries of the set-theory expansion

The following extensions need further development and are deferred:

| Related entry/block IDs | Deferred material | Supporting development needed |
| --- | --- | --- |
| `continuum-function#continuum-restrictions`; `continuum-function#strong-limits-and-sch` | Easton's realization theorem for continuum functions on regular cardinals; consistency or independence results about GCH and SCH | Develop **Models and theories: consistency, extensions, and independence**, **Models of set theory: relativization and absoluteness**, and **Forcing: partial orders, generic filters, and extensions**. A precise Easton statement must specify its model and cardinal-preservation framework; necessary inequalities alone are not a realization theorem. |
| `normal-functions#goodstein-termination` | Unprovability of Goodstein's theorem in Peano arithmetic | **Formal arithmetic: axioms, syntax, and provability**, followed by **Ordinal analysis: induction strength and arithmetic proofs**. The present entry proves termination using ordinals; it makes no assertion about formal provability in arithmetic. |
| `boolean-algebras#stone-map`; `boolean-algebras#stone-representation` | Topological Stone representation: the ultrafilters form a compact Hausdorff zero-dimensional space, and the represented algebra is exactly its clopen algebra | Begin with **Topological spaces: open sets, continuity, and compactness**, then **Stone spaces: Boolean algebras and compact zero-dimensional spaces**. Prove that the sets represented by Boolean elements form a clopen basis, establish compactness, and use it to show that every clopen set is a finite union of basis sets. The current theorem represents an algebra as a subalgebra of a power set without topology. |
| `finite-errors-and-countable-diagonalization#countable-pseudointersection`; `independent-families#independent-families`; `small-families-of-subsets#three-minima`; `bounding-and-dominating-families#bounding-and-dominating-numbers`; `splitting-and-reaping#cardinal-comparisons` | Tower and independence numbers, further cardinal-characteristic comparisons, and realization or independence of possible values | Define the tower and independence minima with their exact maximality and almost-inclusion conventions, then prove their bounds and comparisons. Realization and independence results require models and forcing; the existing elementary inequalities do not establish them. |
| `pressing-down-and-delta-systems#delta-system-lemma`; `pressing-down-and-delta-systems#delta-systems` | Quantitative finite sunflower bounds and their combinatorial applications | A future finite-combinatorics entry, **Sunflowers: common cores and finite family bounds**, should state and prove the size estimates with their parameters. The present uncountable delta-system lemma concerns uncountable families of finite sets, not a numerical bound for a finite family. |
| `infinite-trees#branches-and-antichains`; `infinite-trees#aronszajn-existence` | Tree forcing, specialization, and the effect of forcing axioms on Suslin or Aronszajn trees | Develop **Forcing extensions: conditions, generic filters, and names**, **Preserving cardinals: chain conditions and closure in forcing**, and the relevant tree-forcing constructions. State the order and hypotheses for each construction; the current existence proof supplies no generic extension or preservation theorem. |
| `splitting-stationary-sets#ulam-splitting` | Splitting stationary sets at arbitrary regular uncountable cardinals | Supply a proof beyond successor-cardinal Ulam matrices, with the regularity and stationarity hypotheses stated explicitly. |
| `uncountable-pair-colourings#dushnik-miller-regular` | Dushnik–Miller's theorem at singular cardinals | Develop the singular-cardinal argument rather than extending the existing regular-cardinal proof without justification. |
| `diamond-and-suslin-trees#diamond-sequences`; `diamond-and-suslin-trees#construction-boundary-question` | Diamond in the constructible universe; consistency or independence of diamond | Develop the model framework and constructibility proofs. The existing entry assumes diamond and proves its consequences. |

## Mathematical logic: sources and development plan

Area ID: `mathematical-logic`, under `logic-and-foundations`. The fourteen
proposed entries below need a step-1 handoff and the subsequent pipeline stages.
Their existing foundations are [propositional semantics](entries/propositional-logic/entry.html),
[propositional normal forms](entries/propositional-normal-forms/entry.html),
[propositional proofs](entries/propositional-proofs/entry.html),
[propositional compactness](entries/propositional-compactness/entry.html),
[first-order syntax](entries/first-order-languages/entry.html),
[first-order semantics](entries/first-order-structures/entry.html),
[first-order normal forms](entries/first-order-normal-forms/entry.html),
[first-order proofs](entries/first-order-proofs/entry.html),
[Henkin completeness](entries/henkin-completeness/entry.html),
[countable-language compactness](entries/logical-compactness/entry.html),
[definability](entries/definability-and-automorphisms/entry.html), and
[elementary submodels](entries/elementary-submodels/entry.html).

Keep the language being studied separate from the mathematics used to study it.
Use sets, maps, finite lists, and induction as background; orders and arithmetic
provide examples without requiring an algebra or topology area. Future proof
coding must use the existing sentence-based natural-deduction calculus: closed
term instances and explicitly fresh auxiliary constants. Semantics still treats
arbitrary formulas and assignments; another calculus needs its own translation.

The existing Henkin construction and first-order compactness entry have
**countable-language** scope. Arbitrary-language compactness will be developed
through ultraproducts; it is needed before diagrams of arbitrary structures can
be used for unrestricted upward extensions. Countable diagrams can be developed
now. Keep metatheoretic choice separate from the axioms of the object theory.

### Other elementary branches

The following independent branches remain optional additions:

- **Resolution: clauses and finite refutations.** After propositional normal
  forms, prove soundness and completeness of finite clause refutation by
  eliminating an atom. This is a distinct proof calculus; define its derivations
  and check its correspondence separately. Keep complexity and NP-completeness
  outside this entry until the computation/complexity background exists.
- **Universal and existential preservation.** Add the elementary directions to
  the chain/substructure treatment: universal formulas go down to substructures
  and existential formulas go up, using quantifier-free agreement. The converse
  preservation theorems need diagrams and the appropriate compactness scope.
- **Finite axiomatizability and expressive limits.** A class and its complement
  are both axiomatizable exactly when the class is finitely axiomatizable,
  relative to a fixed background theory if one is used. Well-ordering and finite
  reachability give new compactness applications; finitude itself is already
  covered. Relation/path examples must include their own definitions and finite
  witnesses instead of presupposing a graph-theory area.

Quantifier elimination for dense orders is a useful later
sequel to normal forms and back-and-forth; it must retain all parameter-only
conditions. Skolemization can branch after normal forms, with its expanded-language
satisfaction proof and its distinction from equivalence supplied explicitly. Computability may proceed in parallel with the model-theory branch.

### Source collection

Use **Doets**, **Weiss–D'Mello**, and **Kruckman** for chains and diagrams,
and **Marker** for ultraproducts. Use **Smith**,
**Avigad's 2007 notes**, and
**Incompleteness and Computability** for the arithmetic branch. The latter Open
Logic text incorporates Avigad material, so their agreement is not an independent
cross-check. Exact inspected versions and limitations are also recorded in
[Source errors](source-errors.md#coverage). Page numbers here are printed pages. A checked source passage is not a
completed step-1 handoff or a whole-book audit.

| Key | Source, inspected version, and primary access | Passages and planned use |
| --- | --- | --- |
| F1 | Zach / Open Logic Project, [*Sets, Logic, Computation* — archived Fall 2025 PDF](https://slc.openlogicproject.org/archives/f25/slc-screen.pdf), remix `38828e6` and Open Logic Text `0c1e9e3`, both 2025-07-01. [Project](https://slc.openlogicproject.org/). | §12.9, 246–249, compactness applications for the arithmetic/model branch. Match proof coding to the existing calculus and its actual quantifier and equality side conditions, using chapter 11 as needed. |
| M1 | Doets, [*Basic Model Theory*](https://web.stanford.edu/group/cslipublications/cslipublications/Online/doets-basic-model-theory.pdf), CSLI / FoLLI, 1996. [Publisher record](https://web.stanford.edu/group/cslipublications/cslipublications/site/1575860481.shtml). | §2.2, 16–17: elementary chains; §3.4, 44–45: countable back-and-forth; §4.2, 55–58: signed/elementary diagrams, upward Löwenheim–Skolem and preservation. Diagram Lemma 4.8 is an exercise; Theorem 4.10 supplies the upward proof with the necessary infinite-model hypothesis. Correct the adjacent Łoś–Vaught hypothesis before any use. |
| M2 | Marker, [*Model Theory for Algebra and Algebraic Geometry*, Orsay sections 1–3](https://homepages.math.uic.edu/~marker/orsay/orsay1.pdf), Spring 2010, 25 pages. | §3, 20–24, ultraproduct quotient, Łoś and compactness, diagonal embedding. Use relation/order examples without importing algebraic applications. Repair its compactness filter construction and local slips. |
| M3 | Alex Kruckman, [*Math 509 Lecture Notes*](https://akruckman.faculty.wesleyan.edu/files/2025/12/Lecture-Notes.pdf), Fall 2025, updated 2025-12-18, 92 pages. | 18–19, §2.4 and Proposition 2.19: complete diagram-to-morphism proof; 15, Proposition 2.8, distinguishes embeddings from positive homomorphisms. Later preservation arguments on 48–49 were checked narrowly; direct limits beyond their opening construction still need a full audit. |
| M4 | Weiss and D'Mello, [*Fundamentals of Model Theory*](https://www.math.toronto.edu/weiss/model_theory.pdf), ©2015, 64 PDF pages. | 16–18, Definitions 21–22 and Theorem 4: full omega-chain union proof and counterexample to replacing elementarity by elementary equivalence. Cross-check with Doets Definition 2.16/Lemma 2.17, 17. |
| C1 | Avigad, [*Computability and Incompleteness*](https://www.andrew.cmu.edu/user/avigad/Teaching/candi_notes.pdf), version 2007-01-09, 128 PDF pages. | §§2.3–2.7, 20–46: recursion, coding, normal form, universality, halting; §4.3, 90–100: Robinson arithmetic and representability; §§4.4–4.7, 100–115: undecidability, diagonal lemma, first and conditional second incompleteness. Machine equivalence and all derivability-condition details were not fully audited. |
| C2 | Smith, [*An Introduction to Gödel's Theorems*](https://logicmatters.net/igt/pdfs/GodelBookLM.pdf), second edition, Logic Matters corrected reprint, August 2020. [Author page](https://logicmatters.net/igt/), [corrections](https://logicmatters.net/igt/pdfs/CorrectionsLM.pdf). | Chapters 9–17: induction, Q, PA and representation; 19–20: syntax/proof coding; 24–27: diagonal lemma, Rosser, enumerable theories and truth; 31 and 33–35: second incompleteness/derivability conditions; 38–43: partial recursion and machines. Actual selected readings include 90–94, 107–112, 113–116, 119–121, 185–189 and 258–261; other locations were verified from the contents. Page 116 supplies a compact CRT/beta proof with a boundary-case correction. |
| C3 | Zach / Open Logic Project, [*Incompleteness and Computability*](https://ic.openlogicproject.org/ic-screen.pdf), cover Fall 2025; remix `6b09d98`, 2026-07-11, generated from Open Logic Text `9620cc7`, 2026-07-12. [Project](https://ic.openlogicproject.org/). | Chapter 2, 20–58: recursive functions/coding; chapter 3, 59–75: syntax/derivations; chapter 4, 76–106: Q/representation; chapter 5, 107–128: incompleteness; chapter 6, 129–151: universality/halting/enumerability. Selected beta, minimization, conditional second-incompleteness and halting proofs were inspected. The [fixed-point](https://builds.openlogicproject.org/content/incompleteness/incompleteness-provability/fixed-point-lemma.pdf) and [truth](https://builds.openlogicproject.org/content/incompleteness/incompleteness-provability/tarski-thm.pdf) modules were also checked at Text revision `9620cc7`. |

The source-to-entry map is:

| Proposed entries | Sources and specific support |
| --- | --- |
| `elementary-chains`, `diagrams-and-extensions` | M4, 16–18, and M1, 17, for chains; M3, 18–19, for diagrams. For countable proper extensions, name all elements of a countable infinite structure, add a new element distinct from those names, and check every finite fragment in the original structure. |
| `back-and-forth`, `ultraproducts` | M1 Theorem 3.48; M2 §3 and Marks §13, 57–58, for Łoś and the corrected finite-cone compactness proof. |
| `arithmetic-theories`, `models-and-independence` | C2 chapters 9–13; F1 compactness; M1 Theorem 4.10, 56–57, for unrestricted upward extensions after general compactness. Marks §18 supplies the separate internal/external set-model discussion. Arithmetic examples are optional in the general models entry. |
| `computable-functions`, `coding-formal-proofs`, `universal-computation` | C1 §§2.3–2.7; C3 §§2.2–2.12, 2.15–2.18, chapter 3 and §§6.2–6.12; C2 chapters 14, 19–20, 38 and 41–43. Match codes to the calculus actually chosen. |
| `arithmetic-representability`, `diagonal-lemma`, `first-incompleteness` | C2 chapters 10–11, 15–17, 24–27 and 39; C1 §§4.3–4.5 with recorded corrections; C3 chapter 4 and §§5.2–5.4. |
| `second-incompleteness`, `second-order-logic` | C2 chapters 31, 33–35 and C1/C3 conditional arguments; Avigad 2002 §8.3, 101–106, locates second-order semantics. Full PA derivability-condition proofs and any second-order no-effective-complete-calculus reduction remain to inspect. |
| Optional resolution / expressive-limit branches | Madhusudan–Viswanathan, [*Logic in Computer Science*](https://courses.grainger.illinois.edu/CS474/fa2021/DraftNotes.pdf), 2021-10-11, §2.2, 27–34, is a collected resolution source whose complete proof still needs a stage-1 audit. Schlicht, [*An Introduction to Model Theory*](https://philippschlicht.github.io/teaching/files/modeltheory2017.pdf), course 2017, PDF dated 2021-07-13, 7, supplies the finite-axiomatizability theorem and a connectedness example; expand its finite-path witness. Its adjacent upward-extension proof has a recorded diagram defect. |

For the set-theory interface, retain these already-used publications but extend
their checked scope: [Marks, *Set Theory*](https://math.berkeley.edu/~marks/notes/set_theory_notes_4.pdf),
2026-01-31, §§18–19, 75–84, on membership models, absoluteness and reflection;
[Weiss, *An Introduction to Set Theory*](https://www.math.toronto.edu/~weiss/Set_Theory.pdf),
2014-11-21, chapter 11, 103–120, for an independent model/absoluteness/reflection
treatment; and [Philip, *Axiomatic Set Theory*](https://www.math.lmu.de/~philip/publications/lectureNotes/philipPeter_AxiomaticSetTheory.pdf),
2025-12-30, §§2.2–2.3, 15–19, for small membership-model examples. The early
constructibility, measure and forcing passages inspected for boundary planning
are not full proof audits of those later theories.

Other narrowly inspected alternatives and their access limits remain in
[Source errors](source-errors.md#coverage). A contents location or an exercise
outline is not a replacement for the per-entry source and proof checks.

For later branches, [Schlicht's *Introduction to Mathematical Logic*](https://philippschlicht.github.io/teaching/files/mathematicallogic2021.pdf),
Bonn summer 2021, PDF dated 2022-02-01, §5.1, 65–66, gives direct dense-order
quantifier elimination after repairing dropped parameter conditions.
[Marker's *Model Theory II: Quantifier Elimination*](https://homepages.math.uic.edu/~marker/MSRI-2.pdf),
2020-10-14, slides 1–13, is an orientation for later algebraic applications.
[Avigad's *Proof Theory*](https://arxiv.org/abs/1711.01994v2),
2017-12-16, §2, surveys cut elimination and Herbrand; it states rather than
supplies the full cut-elimination proof.
His [*Classical and constructive logic*](https://www.andrew.cmu.edu/user/avigad/Teaching/classical.pdf),
2000-09-19, revised 2001-11-02, §§1–2, provides introductory comparisons,
not yet a checked source for the later translation theorems.

For Goodstein unprovability, collect [Kirby and Paris, *Accessible Independence
Results for Peano Arithmetic*](https://www.cs.tau.ac.il/~nachumd/term/Kirbyparis.pdf),
1982, 285–293 ([publication](https://doi.org/10.1112/blms/14.4.285)), and
[Avigad, *Ordinal analysis without proofs*](https://www.andrew.cmu.edu/user/avigad/Papers/ordinals.pdf),
published 2002, 1–36; the author preprint has 37 pages and copyright 2000.
Kirby–Paris uses imported model/growth results; Avigad's later analysis proofs
were not audited. Neither is a self-contained immediate sequel to compactness.

Bibliographic reserves with **uninspected chapter proofs** are Avigad's
[*Mathematical Logic and Computation*](https://assets.cambridge.org/97811084/78755/frontmatter/9781108478755_frontmatter.pdf),
Cambridge 2022; Boolos–Burgess–Jeffrey's
[*Computability and Logic*](https://assets.cambridge.org/97805217/01464/frontmatter/9780521701464_frontmatter.pdf),
fifth edition, Cambridge 2007; and Leary–Kristiansen's
[*A Friendly Introduction to Mathematical Logic*](https://textbooks.aimath.org/textbooks/approved-textbooks/leary-kristiansen/),
second edition, 2015, whose publisher download failed in this pass. Marker's
[`ml-web.pdf`](https://homepages.math.uic.edu/~marker/ml-web.pdf) supplied only a
12-page preface/contents preview. Do not cite these unavailable proofs as read.
Write original exposition; the Open Logic texts' CC BY 4.0 licenses do not
extend to unrelated publisher PDFs or differently licensed cover artwork.

### Proposed reading order

These batches are scheduling units, not additional prerequisites. Keep chains, diagrams and back-and-forth together. The computation branch can begin
without waiting for ultraproducts or unrestricted upward Löwenheim–Skolem.

| Batch / order | Proposed plain-text title and ID | Main result and scope | Prerequisites within the area |
| --- | --- | --- | --- |
| 1 / 1 | **Elementary chains: unions that preserve first-order truth** — `elementary-chains` | Construct the union structure and prove the elementary-chain theorem, starting with omega chains; contrast elementary equivalence. Include the elementary universal/existential preservation directions. | `first-order-structures`, `elementary-submodels`; existing ordered sets, and ordinals only for the transfinite version. |
| 1 / 2 | **Diagrams and extensions: naming a structure inside another model** — `diagrams-and-extensions` | Signed atomic and elementary diagrams; diagram models give embeddings or elementary embeddings. Apply countable compactness to obtain proper countable elementary extensions of countable infinite structures. | `first-order-structures`, `elementary-submodels`, `logical-compactness`; countability of the named structure and language. |
| 1 / 3 | **Back-and-forth: partial isomorphisms and countable structures** — `back-and-forth` | Extension criterion for countable back-and-forth systems; dense-order application; isomorphism versus elementary equivalence. For functional languages use finite partial maps preserving atomic formulas with terms, rather than requiring finite substructures. | `first-order-structures`, `elementary-submodels`; existing dense linear orders. Diagrams/chains are useful context, not prerequisites. |
| 1 / 4 | **Ultraproducts: ultrafilters, Łoś's theorem, and transfer** — `ultraproducts` | Quotient a product of nonempty structures; prove Łoś including existential witnesses; arbitrary-language compactness and elementary diagonal embeddings. Well-founded ultrapowers remain later. | `first-order-structures`, `elementary-submodels`; existing filters, ultrafilter extension, quotients and cardinal arithmetic. |
| 2 / 5 | **Models and theories: cardinalities, consistency, and independence** — `models-and-independence` | Unrestricted upward Löwenheim–Skolem using diagrams; models as witnesses to nonderivability; relative-consistency and independence terminology. Internal/external set-model applications require their separate set-theory development. | `henkin-completeness`, `elementary-submodels`, `diagrams-and-extensions`, `ultraproducts`. Arithmetic is an optional example. |
| 2 / 6 | **Arithmetic theories: induction schemas and nonstandard models** — `arithmetic-theories` | Robinson arithmetic and Peano arithmetic; induction with formula parameters; a nonstandard model from compactness; comparison with induction for all subsets. | `first-order-proofs`, `logical-compactness`; existing natural-number arithmetic and uniqueness. |
| 2 / 7 | **Computable functions: primitive recursion and unbounded search** — `computable-functions` | Precise partial-computation model; primitive-recursive arithmetic, bounded search/quantification and unbounded minimization with divergence conventions. | Existing natural-number recursion/arithmetic; finite syntax from `first-order-languages`. Can run in parallel with batch 1. |
| 2 / 8 | **Coding finite sequences and formal proofs** — `coding-formal-proofs` | Primitive-recursive finite-list/syntax/substitution/derivation coding for a fixed finite arithmetic language. Start with recognizable axiom sets; enumerable-axiom certificates follow universal computation. | `first-order-proofs`, `arithmetic-theories`, `computable-functions`. |
| 3 / 9 | **Universal computation: enumeration, halting, and undecidability** — `universal-computation` | Programs and computation histories, universal-function/normal-form theorem, halting undecidability, and decidability iff both sides are enumerable. | `computable-functions`, `coding-formal-proofs`. |
| 3 / 10 | **Representability in arithmetic: expressing computations** — `arithmetic-representability` | Numeralwise functional representability in Robinson arithmetic at defined inputs; positive and negative numeral instances for recursive relations. Distinguish truth, provability and provable totality. | `arithmetic-theories`, `coding-formal-proofs`, `universal-computation`. |
| 3 / 11 | **Self-reference: the diagonal lemma and undefinability of truth** — `diagonal-lemma` | Fixed points using substitution codes; arithmetic truth is not arithmetically definable. | `arithmetic-representability`, `coding-formal-proofs`. |
| 3 / 12 | **First incompleteness: undecidable sentences and Rosser's theorem** — `first-incompleteness` | Consistent computably axiomatized extensions of weak arithmetic are incomplete; Rosser and the stronger hypotheses in Gödel's original argument. | `diagonal-lemma`, `arithmetic-representability`; `models-and-independence` supplies terminology/context. |
| 4 / 13 | **Second incompleteness: provability and consistency statements** — `second-incompleteness` | Concrete PA proof predicate and proved derivability conditions; consistent PA cannot prove its corresponding consistency sentence. Check other proof predicates separately. | `first-incompleteness`, `coding-formal-proofs`, `arithmetic-representability`. |
| 4 / 14 | **Second-order logic: full semantics, Henkin semantics, and categoricity** — `second-order-logic` | Relation/subset quantification, full Peano categoricity and the effect of restricted Henkin domains. Semantics/categoricity may branch after arithmetic; any no-effective-complete-calculus claim waits for its separate reduction. | `arithmetic-theories`, first-order syntax/semantics and `henkin-completeness`; `first-incompleteness` only for the optional effective-calculus reduction. |

### Source checks still required before drafting

The limited reviews found usable arguments and confirmed defects recorded in
[Source errors](source-errors.md). Apply those repairs before adopting the
affected constructions. No unavailable proof, contents-only reading, survey
statement, or omitted exercise has been certified as a completed argument.

For the model-theory batch, signed atomic diagrams must include negated atoms
when an embedding is claimed. Proper-extension applications require an infinite
starting structure. Countable diagram languages fit the existing compactness
entry; unrestricted diagrams wait for arbitrary-language compactness.

For computation, mere countability of formulas does not establish effective
coding. Use the finite arithmetic language first. An explicit pairing and list
code with bounded decoders avoids making prime factorization an external
prerequisite. Prove the chosen decoding bounds. Arithmetic representability
additionally needs a finite simultaneous-remainder/beta lemma: Smith's page 116
provides a compact route, but division, coprime cancellation and the needed
coprime-modulus argument must be proved locally. Avigad and Zach's appeals to
CRT do not supply those missing reader prerequisites.

The inspected second-incompleteness sources prove a conditional abstract
argument, then omit or sketch parts of the concrete PA derivability conditions.
Smith 258–261 likewise sketches formalized Σ₁ completeness. Obtain and audit a full proof for the chosen
coding, or develop it explicitly, before drafting `second-incompleteness` as a theorem about
PA. A theorem conditional on the conditions would have to be labelled with
that smaller scope. This is a source-coverage limit, not a source error.
Second-order semantics and its non-effective-completeness reduction also need
a full per-entry proof audit; the chapter location collected above is not one.

### Coverage of the current reference backlog

The mathematical-logic tasks in [Upcoming references](#upcoming-references)
need the following specialized coverage beyond the existing proof, model,
compactness, and elementary-submodel results.

| Pending coverage | Planned entries that supply it | Integration boundary |
| --- | --- | --- |
| Quantifier elimination — 1 block | Later logic branch, starting with dense orders. | Supply equivalence over the stated theory; prenex conversion itself removes no quantifier. |
| Skolemization — 2 blocks | Later logic branch after normal forms. | Preserve the expanded-language satisfiability scope; chosen witness functions need not be definable in the original language. |
| Infinitary syntax and compactness — 1 block | Later infinitary-logic branch. | The current counterexample is already proved locally; distinguish its enlarged syntax from the finite-formula theorem. |
| Definable classes, relativization, and set-valued class recursion — 4 blocks | Planned set-theory treatment of relativization and absoluteness. | The schema and fixed-parameter conventions are already available. Definable classes are not arbitrary second-order objects; class recursion needs its set-function construction and uniqueness argument. |
| Model witnesses, relative consistency, and independence — 5 blocks | `models-and-independence`, followed by the planned constructibility and forcing developments. | Implication over a theory is already available. Preserve the current conditional CH/diamond arguments; a model framework does not itself realize cardinal-characteristic values or prove consistency or independence of diamond. |
| Induction schemas versus induction for all subsets — 2 blocks | `arithmetic-theories`; `second-order-logic` gives the fuller comparison. | Preserve the existing every-subset natural-number-system theorem. Do not identify it with first-order categoricity of PA. |
| Countable back-and-forth — 2 blocks | `back-and-forth`. | State both extension directions and the countability hypothesis; the existing dense-order proof remains its own checked application. |

### Later branches and the set-theory interface

After the elementary model-theory batch, the next set-theory development can be
**Models of set theory: relativization and absoluteness**, followed by
**Reflection: finite fragments and rank initial segments**. Use the existing
rank hierarchy, Mostowski collapse, and hereditary-size bounds, but check each
model's axioms explicitly. Consistency of ZFC gives a model through completeness
in the metatheory; it does not by itself supply a well-founded or transitive
model. A countable model's internally uncountable sets need not be externally
uncountable. Reflection applies to a specified finite family of formulas, not
one set model simultaneously reflecting every formula.

Constructibility, condensation, forcing, preservation, Cohen reals, symmetric
models, and large cardinals remain **set-theory entries**. Ultraproducts prepare
for ultrapowers, but measurability still needs a complete measure and a separate
well-foundedness argument. The current diamond entry assumes diamond; a model
framework alone does not establish diamond in the constructible universe or
its consistency.

Further logic branches should be planned separately: quantifier elimination,
types and saturation, Fraïssé constructions, computable reductions and degrees,
Rice's theorem and the recursion theorem, sequent calculi and cut elimination,
intuitionistic logic and negative translations, and modal logic. Ordinal
analysis and Goodstein unprovability require their own arithmetic-strength
proofs after the arithmetic and incompleteness entries. A proof of Goodstein
termination by ordinal descent is not such an unprovability proof.

### Formalization preparation

The environment remains pinned by `formal/lean-toolchain` and
`formal/lake-manifest.json`. Mathlib's `ModelTheory` supplies partial equivalences,
ultraproducts, and semantic compactness; inspect their actual definitions and
hypotheses when preparing the remaining entries. General-language compactness
uses ultraproducts, whereas the existing countable Henkin entry uses the explicit
natural-deduction calculus.

For future coding, preserve the [free-name and indexed-bound-variable
convention](entries/first-order-languages/entry.html#scoped-formulas) and the
finite `Proof`/`Derives` definitions in `MathematicalLogic/FirstOrderProofs.lean`.
`Mathlib.ModelTheory.DirectLimit` supplies structure constructions; its full
elementary-chain correspondence still needs inspection for the proposed entry.
Reuse the existing formula representations and proof calculi.

Check that effective codes recognize the actual rules, auxiliary-name conditions,
closed-term instances, and allowed axioms. Expand derived proof-tree operations
or supply their effective finite certificates before treating all derivations as
primitive-recursively recognizable. In `BoundedFormula α n`, `n` counts
in-scope bound variables; “bounded” does **not** mean bounded quantification in
the set-theoretic or arithmetic hierarchy.

`Computability` has primitive and partial recursion, program codes, universal
evaluation, and `ComputablePred.halting_problem`; the relevant definitions and
signatures were inspected. Arithmetic proof coding, representability, and
incompleteness still need a dedicated formal design and correspondence audit.
An ordinary Lean proof of a statement about natural numbers is not automatically
a proof of its derivability in PA or ZFC. These later claims need their own
bindings and verification; inspected library declarations do not establish that
coverage.
