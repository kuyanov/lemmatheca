# Ordered sets: formal binding notes

This is the correspondence map for [the ordered-sets entry](../corpus/entries/ordered-sets/entry.html).
The HTML `data-formal` attributes are the authoritative block bindings. Every block
has mathematical content and a nonempty mapping; none is marked not applicable.
Node JSON and entry-list summaries are generated or refreshed by `app/manage.py build`.

## Representation and reuse

- A set equipped with an order is represented by a Lean type with that order.
  For a fixed subset U of a larger universe, use its subtype as the ambient type:
  `Set U` represents its power set. `Set.univ` is therefore U, and intersections
  of empty families are relative to U. The complete lattice instance specifies
  `sSup = Set.sUnion` and `sInf = Set.sInter`; binary operations are union/intersection.
  Existing empty indexed-family nodes apply by indexing with the family subtype.
- `IsPartialOrder` and `IsLinearOrder` describe arbitrary binary relations without
  adding decidability. Bundled `PartialOrder`/`Preorder` instances supply notation.
  Lean defines strict comparison in a preorder by `a ≤ b ∧ ¬ b ≤ a`; in a partial
  order this is equivalent to `a ≤ b ∧ a ≠ b`. `partialOrderOfSO` uses equality
  first in its disjunction, which changes no mathematics. Its strict field is the
  original relation, and `le_iff_lt_or_eq` supplies the other recovery direction.
- `Minimal`/`Maximal` are predicates including membership, not extrema selectors.
  Under a preorder they agree with membership plus absence of a strictly smaller/
  larger member. `IsLeast.minimal_iff` includes both minimality and uniqueness.
  `lt_trichotomy`, strict asymmetry and strict comparison together give exactly
  one alternative in a linear order; the four-way partial-order result includes
  incomparability. No least element is inferred from unique minimality without
  the required finiteness or totality assumption.
- `DvdPNat` is a distinct copy of the positive integers with divisibility order.
  Its multiplier is positive, as in the prose. `Divisor12` and `ProperDivisor12`
  carry inherited orders; the latter removes 12 from the ambient type, not only
  from the subset being bounded. The `divisor` helper packages membership proofs
  for figure labels and is not a registered claim. Generic lcm/gcd nodes use the
  existing positive-integer divisibility theorems directly.
- `FourPoint` is a copy of `Fin 4`, labelled a=0, b=1, u=2, v=3. Its only
  non-reflexive comparisons go from {0,1} to {2,3}. `PreorderedPlane` is a copy of
  the real plane comparing only first coordinates. Distinct type synonyms prevent
  either example from inheriting the numerical or product order accidentally.
  The isolated-star example uses the library disjoint-union order on `ℤ ⊕ Unit`,
  with star represented by `Sum.inr ()`; it is not a top or bottom extension.
- `{0,1}` is represented by `Fin 2`. The monotone-bijection counterexample writes
  domain comparison explicitly as equality and codomain comparison numerically.
  Its last conjunct is precisely failure of monotonicity for the inverse identity.
  The indicator example uses `Set (Fin 2)` and fixes both its formula and witnesses.
- Suprema and infima in arbitrary posets are expressed with `IsLUB` and `IsGLB`,
  not a total choice function that could assign values when bounds do not exist.
  Generic interval and midpoint theorems are specialized to R and Q respectively.
  The two nontrivial max/min witness formulas in (0,1) have separate local statements.
- Finite Hasse paths use `Relation.TransGen CovBy`, meaning a nonempty finite
  path. The library theorem assumes `LocallyFiniteOrder`, which any finite poset
  supports; it also covers the more general locally finite case. No such claim is
  made for arbitrary infinite posets. All seven edges of the divisor diagram are
  specified, as are the highlighted chain and the incomparable pair.
- The ordered quotient is mathlib's `Antisymmetrization`, whose setoid is mutual
  comparison. Existing quotient projection nodes apply definitionally. The generic
  factorization is bound directly to `preordToPartOrdForgetAdjunction`: its
  `homEquiv` precomposes with the projection, and its inverse is the quotient lift
  sending `[a]` to `f(a)`. The inverse laws give uniqueness as well as existence;
  both directions are bundled monotone maps. This avoids a wrapper around an
  existing theorem. The categorical presentation uses one universe for A and P;
  types in different universes can be placed in their common larger universe.
- The plane quotient statement fixes both maps: `[(x,s)] ↦ x` and
  `x ↦ [(x,0)]`. Parity uses the existing `paritySetoid`, the kernel of reduction
  modulo two. Existential representative comparison is a predicate on actual
  quotient elements, with distinct even/odd classes and the witnesses 0≤1≤2.

## Local declarations and proof planning

[SetTheory/OrderedSets.lean](Lemmatheca/SetTheory/OrderedSets.lean) contains the
remaining general statements: the equality order and its totality criterion,
finite unique extrema, empty ambient types, antisymmetry of a pulled-back relation,
and the canonical quotient isomorphism for a poset.
[Entry/OrderedSets.lean](Lemmatheca/Entry/OrderedSets.lean) specifies the concrete
orders, witnesses, diagrams and counterexamples from the prose. Standard library
constructions are used directly instead of restating them as local wrappers.
New theorem bodies and the unfinished four-point order laws are `sorry`; definition
bodies are specified. Existing proofs and environment pins are unchanged.

Dependency arrays contain only direct proof-planning suggestions. For example,
finite unique extrema use the corresponding finite extremum existence result;
the divisor supremum/infimum and removed-ambient-point counterexample use the
exact bound sets; the plane quotient isomorphism uses the fiber description and
quotient comparison; failure of plane identity factorization uses distinct mutually
comparable points and quotient equality. They do not control verification flags.

## Block coverage

| Block | Claims covered | Node IDs |
| --- | --- | --- |
| `partial-and-total-orders` | Order axioms, comparability, numerical orders, equality order and its totality, incomparable singletons. | [order-partial](../corpus/nodes/order-partial.json), [order-linear](../corpus/nodes/order-linear.json), [order-comparable](../corpus/nodes/order-comparable.json), [order-incomparable](../corpus/nodes/order-incomparable.json), [set-singleton-inclusion](../corpus/nodes/set-singleton-inclusion.json), [order-nat-linear](../corpus/nodes/order-nat-linear.json), [order-int-linear](../corpus/nodes/order-int-linear.json), [order-rat-linear](../corpus/nodes/order-rat-linear.json), [order-real-linear](../corpus/nodes/order-real-linear.json), [order-equality](../corpus/nodes/order-equality.json), [equality-equivalence-relation](../corpus/nodes/equality-equivalence-relation.json), [order-equality-total-iff](../corpus/nodes/order-equality-total-iff.json) |
| `orders-from-inclusion-and-divisibility` | Inclusion; positive divisibility; the divisors of 12 and their comparisons; inherited and opposite orders. | [order-power-set-complete-lattice](../corpus/nodes/order-power-set-complete-lattice.json), [set-singleton-inclusion](../corpus/nodes/set-singleton-inclusion.json), [positive-divisibility-definition](../corpus/nodes/positive-divisibility-definition.json), [positive-divisibility-order](../corpus/nodes/positive-divisibility-order.json), [positive-divisibility-incomparable](../corpus/nodes/positive-divisibility-incomparable.json), [order-inherited](../corpus/nodes/order-inherited.json), [positive-divisors-twelve](../corpus/nodes/positive-divisors-twelve.json), [divisors-twelve-comparisons](../corpus/nodes/divisors-twelve-comparisons.json), [order-opposite](../corpus/nodes/order-opposite.json) |
| `strict-orders` | Strict/non-strict conversions and their recovery laws; trichotomy, exclusivity, incomparability, proper inclusion. | [order-strict](../corpus/nodes/order-strict.json), [order-strict-from-partial](../corpus/nodes/order-strict-from-partial.json), [order-strict-comparison](../corpus/nodes/order-strict-comparison.json), [order-from-strict](../corpus/nodes/order-from-strict.json), [order-nonstrict-comparison](../corpus/nodes/order-nonstrict-comparison.json), [order-trichotomy](../corpus/nodes/order-trichotomy.json), [order-strict-asymmetric](../corpus/nodes/order-strict-asymmetric.json), [order-four-comparisons](../corpus/nodes/order-four-comparisons.json), [set-proper-subset](../corpus/nodes/set-proper-subset.json), [set-singleton-inclusion](../corpus/nodes/set-singleton-inclusion.json) |
| `chains-and-hasse-diagrams` | Chains, antichains, covers; every labelled edge and highlighted chain in the figure; finite cover paths; the rational midpoint and absence of covers. | [order-chain](../corpus/nodes/order-chain.json), [order-antichain](../corpus/nodes/order-antichain.json), [order-cover](../corpus/nodes/order-cover.json), [divisors-twelve-chain-antichain](../corpus/nodes/divisors-twelve-chain-antichain.json), [divisors-twelve-covers](../corpus/nodes/divisors-twelve-covers.json), [divisors-twelve-comparisons](../corpus/nodes/divisors-twelve-comparisons.json), [order-finite-cover-paths](../corpus/nodes/order-finite-cover-paths.json), [order-dense-no-covers](../corpus/nodes/order-dense-no-covers.json), [order-midpoint-above-left](../corpus/nodes/order-midpoint-above-left.json), [order-midpoint-below-right](../corpus/nodes/order-midpoint-below-right.json) |
| `least-and-minimal-elements` | Extremal-element definitions and uniqueness, least implies uniquely minimal, linear-order converses, the {4,6} example, top and bottom. | [order-least](../corpus/nodes/order-least.json), [order-greatest](../corpus/nodes/order-greatest.json), [order-minimal](../corpus/nodes/order-minimal.json), [order-maximal](../corpus/nodes/order-maximal.json), [order-least-unique](../corpus/nodes/order-least-unique.json), [order-greatest-unique](../corpus/nodes/order-greatest-unique.json), [order-least-only-minimal](../corpus/nodes/order-least-only-minimal.json), [divisors-twelve-pair-extrema](../corpus/nodes/divisors-twelve-pair-extrema.json), [order-linear-minimal-least](../corpus/nodes/order-linear-minimal-least.json), [order-linear-maximal-greatest](../corpus/nodes/order-linear-maximal-greatest.json), [order-bottom](../corpus/nodes/order-bottom.json), [order-top](../corpus/nodes/order-top.json), [order-power-set-complete-lattice](../corpus/nodes/order-power-set-complete-lattice.json), [divisors-twelve-bottom-top](../corpus/nodes/divisors-twelve-bottom-top.json) |
| `finite-extrema` | Minimal elements below each member and maximal elements above; uniqueness implies least/greatest. | [order-finite-minimal-below](../corpus/nodes/order-finite-minimal-below.json), [order-finite-maximal-above](../corpus/nodes/order-finite-maximal-above.json), [order-finite-unique-minimal-least](../corpus/nodes/order-finite-unique-minimal-least.json), [order-finite-unique-maximal-greatest](../corpus/nodes/order-finite-unique-maximal-greatest.json) |
| `unique-minimal-question` | The disjoint-union order, the isolated star, the explicit n−1 witness, and failure of a least element. | [order-disjoint-union](../corpus/nodes/order-disjoint-union.json), [isolated-integer-star-minimal-not-least](../corpus/nodes/isolated-integer-star-minimal-not-least.json) |
| `bounds` | Ambient bounds and boundedness; exact bounds of {4,6}, exclusion from that set, and loss of upper bounds when 12 is removed. | [order-upper-bounds](../corpus/nodes/order-upper-bounds.json), [order-lower-bounds](../corpus/nodes/order-lower-bounds.json), [order-bounded-above](../corpus/nodes/order-bounded-above.json), [order-bounded-below](../corpus/nodes/order-bounded-below.json), [divisors-twelve-pair-bounds](../corpus/nodes/divisors-twelve-pair-bounds.json), [order-least](../corpus/nodes/order-least.json), [order-greatest](../corpus/nodes/order-greatest.json), [proper-divisors-twelve-no-upper-bound](../corpus/nodes/proper-divisors-twelve-no-upper-bound.json) |
| `suprema-and-infima` | Definitions, uniqueness and membership criteria; (0,1) endpoints and both explicit midpoint witnesses; divisor bounds; lcm/gcd universal properties. | [order-supremum](../corpus/nodes/order-supremum.json), [order-infimum](../corpus/nodes/order-infimum.json), [order-supremum-unique](../corpus/nodes/order-supremum-unique.json), [order-infimum-unique](../corpus/nodes/order-infimum-unique.json), [order-infimum-member-least](../corpus/nodes/order-infimum-member-least.json), [order-supremum-member-greatest](../corpus/nodes/order-supremum-member-greatest.json), [order-open-interval-supremum](../corpus/nodes/order-open-interval-supremum.json), [order-open-interval-infimum](../corpus/nodes/order-open-interval-infimum.json), [order-open-interval-excludes-left](../corpus/nodes/order-open-interval-excludes-left.json), [order-open-interval-excludes-right](../corpus/nodes/order-open-interval-excludes-right.json), [real-open-unit-interval-upper-witness](../corpus/nodes/real-open-unit-interval-upper-witness.json), [real-open-unit-interval-lower-witness](../corpus/nodes/real-open-unit-interval-lower-witness.json), [divisors-twelve-pair-bounds](../corpus/nodes/divisors-twelve-pair-bounds.json), [divisors-twelve-pair-supremum-infimum](../corpus/nodes/divisors-twelve-pair-supremum-infimum.json), [positive-lcm-upper-left](../corpus/nodes/positive-lcm-upper-left.json), [positive-lcm-upper-right](../corpus/nodes/positive-lcm-upper-right.json), [positive-lcm-least](../corpus/nodes/positive-lcm-least.json), [positive-gcd-lower-left](../corpus/nodes/positive-gcd-lower-left.json), [positive-gcd-lower-right](../corpus/nodes/positive-gcd-lower-right.json), [positive-gcd-greatest](../corpus/nodes/positive-gcd-greatest.json) |
| `bounded-without-supremum` | The exact four-point order, incomparable bounds, minimal upper bounds, and absence of a supremum/infimum. | [four-point-order](../corpus/nodes/four-point-order.json), [four-point-bounds-no-supremum-infimum](../corpus/nodes/four-point-bounds-no-supremum-infimum.json) |
| `power-set-bounds` | Arbitrary union/intersection as bounds, empty families, binary bounds, lattices and complete lattices. | [order-power-set-complete-lattice](../corpus/nodes/order-power-set-complete-lattice.json), [order-complete-supremum](../corpus/nodes/order-complete-supremum.json), [order-complete-infimum](../corpus/nodes/order-complete-infimum.json), [set-empty-family-union](../corpus/nodes/set-empty-family-union.json), [set-empty-family-intersection](../corpus/nodes/set-empty-family-intersection.json), [order-pair-supremum](../corpus/nodes/order-pair-supremum.json), [order-pair-infimum](../corpus/nodes/order-pair-infimum.json), [order-lattice](../corpus/nodes/order-lattice.json), [order-complete-lattice](../corpus/nodes/order-complete-lattice.json) |
| `empty-orders-and-bounds` | Unique empty relation and vacuous order axioms; no extrema/bounds in an empty ambient type; empty-subset bounds, singleton posets and the power set of the empty set. | [empty-relation-equivalence](../corpus/nodes/empty-relation-equivalence.json), [order-empty-orders](../corpus/nodes/order-empty-orders.json), [order-empty-poset-extrema-bounds](../corpus/nodes/order-empty-poset-extrema-bounds.json), [order-empty-upper-bounds](../corpus/nodes/order-empty-upper-bounds.json), [order-empty-lower-bounds](../corpus/nodes/order-empty-lower-bounds.json), [order-empty-supremum](../corpus/nodes/order-empty-supremum.json), [order-empty-infimum](../corpus/nodes/order-empty-infimum.json), [order-subsingleton-bottom](../corpus/nodes/order-subsingleton-bottom.json), [order-subsingleton-top](../corpus/nodes/order-subsingleton-top.json), [set-powerset-empty](../corpus/nodes/set-powerset-empty.json), [order-power-set-complete-lattice](../corpus/nodes/order-power-set-complete-lattice.json) |
| `order-maps` | Monotone maps, comparison-preserving embeddings and injectivity, isomorphisms and monotone inverses; constants, inclusions, translation, identity and composition. | [order-monotone](../corpus/nodes/order-monotone.json), [order-embedding](../corpus/nodes/order-embedding.json), [order-embedding-from-comparisons](../corpus/nodes/order-embedding-from-comparisons.json), [order-isomorphism](../corpus/nodes/order-isomorphism.json), [order-isomorphism-from-monotone-inverses](../corpus/nodes/order-isomorphism-from-monotone-inverses.json), [order-isomorphism-surjective-embedding](../corpus/nodes/order-isomorphism-surjective-embedding.json), [order-constant-monotone](../corpus/nodes/order-constant-monotone.json), [order-constant-not-injective](../corpus/nodes/order-constant-not-injective.json), [order-subtype-embedding](../corpus/nodes/order-subtype-embedding.json), [order-integer-translation](../corpus/nodes/order-integer-translation.json), [order-identity-monotone](../corpus/nodes/order-identity-monotone.json), [order-monotone-composition](../corpus/nodes/order-monotone-composition.json), [order-embedding-composition](../corpus/nodes/order-embedding-composition.json), [order-isomorphism-composition](../corpus/nodes/order-isomorphism-composition.json) |
| `monotone-bijection-question` | The identity between the two orders on {0,1}, its failed reflection and nonmonotone inverse; reflection for an injective monotone map with linear domain. | [equality-to-linear-monotone-bijection](../corpus/nodes/equality-to-linear-monotone-bijection.json), [order-injective-monotone-strict](../corpus/nodes/order-injective-monotone-strict.json), [order-linear-strict-reflects](../corpus/nodes/order-linear-strict-reflects.json), [order-embedding-from-comparisons](../corpus/nodes/order-embedding-from-comparisons.json), [order-isomorphism-surjective-embedding](../corpus/nodes/order-isomorphism-surjective-embedding.json) |
| `isomorphisms-preserve-bounds` | Preservation of suprema/infima, monotone images of upper bounds, and the specified full-set indicator counterexample. | [order-isomorphism-preserves-supremum](../corpus/nodes/order-isomorphism-preserves-supremum.json), [order-isomorphism-preserves-infimum](../corpus/nodes/order-isomorphism-preserves-infimum.json), [order-monotone-image-upper-bound](../corpus/nodes/order-monotone-image-upper-bound.json), [full-set-indicator](../corpus/nodes/full-set-indicator.json), [full-set-indicator-monotone](../corpus/nodes/full-set-indicator-monotone.json), [full-set-indicator-not-preserve-supremum](../corpus/nodes/full-set-indicator-not-preserve-supremum.json) |
| `preorders` | Reflexivity/transitivity; pullbacks; the real-plane example and its two distinct mutually comparable points; antisymmetry iff the inducing map is injective. | [order-preorder](../corpus/nodes/order-preorder.json), [order-partial](../corpus/nodes/order-partial.json), [order-induced-preorder](../corpus/nodes/order-induced-preorder.json), [real-plane-first-coordinate-preorder](../corpus/nodes/real-plane-first-coordinate-preorder.json), [real-plane-first-coordinate-not-antisymmetric](../corpus/nodes/real-plane-first-coordinate-not-antisymmetric.json), [order-induced-antisymmetric-iff-injective](../corpus/nodes/order-induced-antisymmetric-iff-injective.json), [order-monotone](../corpus/nodes/order-monotone.json) |
| `quotient-order` | Mutual-comparison equivalence, independence of representatives, quotient order, projection properties, vertical fibers and the specified isomorphism with R. | [ordered-quotient-equivalence](../corpus/nodes/ordered-quotient-equivalence.json), [ordered-quotient](../corpus/nodes/ordered-quotient.json), [ordered-quotient-partial-order](../corpus/nodes/ordered-quotient-partial-order.json), [ordered-quotient-representatives](../corpus/nodes/ordered-quotient-representatives.json), [ordered-quotient-comparison](../corpus/nodes/ordered-quotient-comparison.json), [ordered-quotient-projection-monotone](../corpus/nodes/ordered-quotient-projection-monotone.json), [quotient-projection-surjective](../corpus/nodes/quotient-projection-surjective.json), [quotient-projection-equality](../corpus/nodes/quotient-projection-equality.json), [real-plane-first-coordinate-classes](../corpus/nodes/real-plane-first-coordinate-classes.json), [real-plane-ordered-quotient-isomorphism](../corpus/nodes/real-plane-ordered-quotient-isomorphism.json) |
| `monotone-maps-from-quotients` | Existence, uniqueness, evaluation and converse for monotone factorization; failure for the plane-valued identity. | [ordered-quotient-universal-property](../corpus/nodes/ordered-quotient-universal-property.json), [order-identity-monotone](../corpus/nodes/order-identity-monotone.json), [real-plane-identity-not-factor](../corpus/nodes/real-plane-identity-not-factor.json) |
| `which-identifications-work` | The quotient of a poset, parity representative dependence, and the explicit 0≤1≤2 counterexample to existential comparison. | [order-mutual-comparison-equality](../corpus/nodes/order-mutual-comparison-equality.json), [ordered-quotient-poset-isomorphism](../corpus/nodes/ordered-quotient-poset-isomorphism.json), [int-parity-comparison-not-well-defined](../corpus/nodes/int-parity-comparison-not-well-defined.json), [int-parity-representative-comparison](../corpus/nodes/int-parity-representative-comparison.json), [int-parity-representative-comparison-not-antisymmetric](../corpus/nodes/int-parity-representative-comparison-not-antisymmetric.json) |

## New targets

Each new node is listed below. No existing node is rebound or retired. Reused
nodes are listed separately after this table. Module names identify the declaration's
actual defining source, including generated dual declarations.

| Node ID | Declaration | Defining module |
| --- | --- | --- |
| [divisors-twelve-bottom-top](../corpus/nodes/divisors-twelve-bottom-top.json) | `Lemmatheca.Entry.OrderedSets.divisor_bottom_top` | `Lemmatheca.Entry.OrderedSets` |
| [divisors-twelve-chain-antichain](../corpus/nodes/divisors-twelve-chain-antichain.json) | `Lemmatheca.Entry.OrderedSets.divisor_chain_antichain` | `Lemmatheca.Entry.OrderedSets` |
| [divisors-twelve-comparisons](../corpus/nodes/divisors-twelve-comparisons.json) | `Lemmatheca.Entry.OrderedSets.divisor_comparisons` | `Lemmatheca.Entry.OrderedSets` |
| [divisors-twelve-covers](../corpus/nodes/divisors-twelve-covers.json) | `Lemmatheca.Entry.OrderedSets.divisor_covers` | `Lemmatheca.Entry.OrderedSets` |
| [divisors-twelve-pair-bounds](../corpus/nodes/divisors-twelve-pair-bounds.json) | `Lemmatheca.Entry.OrderedSets.divisor_pair_bounds` | `Lemmatheca.Entry.OrderedSets` |
| [divisors-twelve-pair-extrema](../corpus/nodes/divisors-twelve-pair-extrema.json) | `Lemmatheca.Entry.OrderedSets.divisor_pair_extrema` | `Lemmatheca.Entry.OrderedSets` |
| [divisors-twelve-pair-supremum-infimum](../corpus/nodes/divisors-twelve-pair-supremum-infimum.json) | `Lemmatheca.Entry.OrderedSets.divisor_pair_lub_glb` | `Lemmatheca.Entry.OrderedSets` |
| [equality-to-linear-monotone-bijection](../corpus/nodes/equality-to-linear-monotone-bijection.json) | `Lemmatheca.Entry.OrderedSets.equality_to_linear_monotone_bijection` | `Lemmatheca.Entry.OrderedSets` |
| [four-point-bounds-no-supremum-infimum](../corpus/nodes/four-point-bounds-no-supremum-infimum.json) | `Lemmatheca.Entry.OrderedSets.four_point_bounds` | `Lemmatheca.Entry.OrderedSets` |
| [four-point-order](../corpus/nodes/four-point-order.json) | `Lemmatheca.Entry.OrderedSets.fourPointOrder` | `Lemmatheca.Entry.OrderedSets` |
| [full-set-indicator](../corpus/nodes/full-set-indicator.json) | `Lemmatheca.Entry.OrderedSets.fullSetIndicator` | `Lemmatheca.Entry.OrderedSets` |
| [full-set-indicator-monotone](../corpus/nodes/full-set-indicator-monotone.json) | `Lemmatheca.Entry.OrderedSets.full_set_indicator_monotone` | `Lemmatheca.Entry.OrderedSets` |
| [full-set-indicator-not-preserve-supremum](../corpus/nodes/full-set-indicator-not-preserve-supremum.json) | `Lemmatheca.Entry.OrderedSets.full_set_indicator_not_preserve_sup` | `Lemmatheca.Entry.OrderedSets` |
| [int-parity-comparison-not-well-defined](../corpus/nodes/int-parity-comparison-not-well-defined.json) | `Lemmatheca.Entry.OrderedSets.parity_comparison_not_well_defined` | `Lemmatheca.Entry.OrderedSets` |
| [int-parity-representative-comparison](../corpus/nodes/int-parity-representative-comparison.json) | `Lemmatheca.Entry.OrderedSets.parityRepresentativeLE` | `Lemmatheca.Entry.OrderedSets` |
| [int-parity-representative-comparison-not-antisymmetric](../corpus/nodes/int-parity-representative-comparison-not-antisymmetric.json) | `Lemmatheca.Entry.OrderedSets.parity_representative_order_not_antisymmetric` | `Lemmatheca.Entry.OrderedSets` |
| [isolated-integer-star-minimal-not-least](../corpus/nodes/isolated-integer-star-minimal-not-least.json) | `Lemmatheca.Entry.OrderedSets.isolated_star_minimal_not_least` | `Lemmatheca.Entry.OrderedSets` |
| [order-antichain](../corpus/nodes/order-antichain.json) | `IsAntichain` | `Mathlib.Order.Antichain` |
| [order-bottom](../corpus/nodes/order-bottom.json) | `IsBot` | `Mathlib.Order.Max` |
| [order-bounded-above](../corpus/nodes/order-bounded-above.json) | `BddAbove` | `Mathlib.Order.Bounds.Defs` |
| [order-bounded-below](../corpus/nodes/order-bounded-below.json) | `BddBelow` | `Mathlib.Order.Bounds.Defs` |
| [order-chain](../corpus/nodes/order-chain.json) | `IsChain` | `Mathlib.Order.Preorder.Chain` |
| [order-comparable](../corpus/nodes/order-comparable.json) | `Relation.SymmGen` | `Mathlib.Logic.Relation` |
| [order-complete-infimum](../corpus/nodes/order-complete-infimum.json) | `isGLB_sInf` | `Mathlib.Order.CompleteLattice.Defs` |
| [order-complete-lattice](../corpus/nodes/order-complete-lattice.json) | `CompleteLattice` | `Mathlib.Order.CompleteLattice.Defs` |
| [order-complete-supremum](../corpus/nodes/order-complete-supremum.json) | `isLUB_sSup` | `Mathlib.Order.CompleteLattice.Defs` |
| [order-constant-monotone](../corpus/nodes/order-constant-monotone.json) | `monotone_const` | `Mathlib.Order.Monotone.Defs` |
| [order-constant-not-injective](../corpus/nodes/order-constant-not-injective.json) | `Function.not_injective_const` | `Mathlib.Logic.Function.Basic` |
| [order-cover](../corpus/nodes/order-cover.json) | `CovBy` | `Mathlib.Order.Defs.PartialOrder` |
| [order-dense-no-covers](../corpus/nodes/order-dense-no-covers.json) | `not_covBy_of_denselyOrdered` | `Mathlib.Order.Cover` |
| [order-disjoint-union](../corpus/nodes/order-disjoint-union.json) | `Sum.instPartialOrder` | `Mathlib.Data.Sum.Order` |
| [order-embedding](../corpus/nodes/order-embedding.json) | `OrderEmbedding` | `Mathlib.Order.Hom.Basic` |
| [order-embedding-composition](../corpus/nodes/order-embedding-composition.json) | `OrderEmbedding.comp` | `Mathlib.Order.Hom.Basic` |
| [order-embedding-from-comparisons](../corpus/nodes/order-embedding-from-comparisons.json) | `OrderEmbedding.ofMapLEIff` | `Mathlib.Order.Hom.Basic` |
| [order-empty-infimum](../corpus/nodes/order-empty-infimum.json) | `isGLB_empty_iff` | `Mathlib.Order.Bounds.Basic` |
| [order-empty-lower-bounds](../corpus/nodes/order-empty-lower-bounds.json) | `lowerBounds_empty` | `Mathlib.Order.Bounds.Basic` |
| [order-empty-orders](../corpus/nodes/order-empty-orders.json) | `Lemmatheca.SetTheory.empty_orders` | `Lemmatheca.SetTheory.OrderedSets` |
| [order-empty-poset-extrema-bounds](../corpus/nodes/order-empty-poset-extrema-bounds.json) | `Lemmatheca.SetTheory.empty_poset_extrema_and_bounds` | `Lemmatheca.SetTheory.OrderedSets` |
| [order-empty-supremum](../corpus/nodes/order-empty-supremum.json) | `isLUB_empty_iff` | `Mathlib.Order.Bounds.Basic` |
| [order-empty-upper-bounds](../corpus/nodes/order-empty-upper-bounds.json) | `upperBounds_empty` | `Mathlib.Order.Bounds.Basic` |
| [order-equality](../corpus/nodes/order-equality.json) | `Lemmatheca.SetTheory.equality_partial_order` | `Lemmatheca.SetTheory.OrderedSets` |
| [order-equality-total-iff](../corpus/nodes/order-equality-total-iff.json) | `Lemmatheca.SetTheory.equality_order_total_iff` | `Lemmatheca.SetTheory.OrderedSets` |
| [order-finite-cover-paths](../corpus/nodes/order-finite-cover-paths.json) | `lt_iff_transGen_covBy` | `Mathlib.Order.Interval.Finset.Basic` |
| [order-finite-maximal-above](../corpus/nodes/order-finite-maximal-above.json) | `Set.Finite.exists_le_maximal` | `Mathlib.Order.Preorder.Finite` |
| [order-finite-minimal-below](../corpus/nodes/order-finite-minimal-below.json) | `Set.Finite.exists_le_minimal` | `Mathlib.Order.Preorder.Finite` |
| [order-finite-unique-maximal-greatest](../corpus/nodes/order-finite-unique-maximal-greatest.json) | `Lemmatheca.SetTheory.finite_unique_maximal_isGreatest` | `Lemmatheca.SetTheory.OrderedSets` |
| [order-finite-unique-minimal-least](../corpus/nodes/order-finite-unique-minimal-least.json) | `Lemmatheca.SetTheory.finite_unique_minimal_isLeast` | `Lemmatheca.SetTheory.OrderedSets` |
| [order-four-comparisons](../corpus/nodes/order-four-comparisons.json) | `lt_or_eq_or_gt_or_incompRel` | `Mathlib.Order.Comparable` |
| [order-from-strict](../corpus/nodes/order-from-strict.json) | `partialOrderOfSO` | `Mathlib.Order.RelClasses` |
| [order-greatest](../corpus/nodes/order-greatest.json) | `IsGreatest` | `Mathlib.Order.Bounds.Defs` |
| [order-greatest-unique](../corpus/nodes/order-greatest-unique.json) | `IsGreatest.unique` | `Mathlib.Order.Bounds.Basic` |
| [order-identity-monotone](../corpus/nodes/order-identity-monotone.json) | `monotone_id` | `Mathlib.Order.Monotone.Defs` |
| [order-incomparable](../corpus/nodes/order-incomparable.json) | `IncompRel` | `Mathlib.Order.Comparable` |
| [order-induced-antisymmetric-iff-injective](../corpus/nodes/order-induced-antisymmetric-iff-injective.json) | `Lemmatheca.SetTheory.induced_order_antisymmetric_iff` | `Lemmatheca.SetTheory.OrderedSets` |
| [order-induced-preorder](../corpus/nodes/order-induced-preorder.json) | `Preorder.lift` | `Mathlib.Order.Basic` |
| [order-infimum](../corpus/nodes/order-infimum.json) | `IsGLB` | `Mathlib.Order.Bounds.Defs` |
| [order-infimum-member-least](../corpus/nodes/order-infimum-member-least.json) | `isLeast_iff_isGLB_and_mem` | `Mathlib.Order.Bounds.Basic` |
| [order-infimum-unique](../corpus/nodes/order-infimum-unique.json) | `IsGLB.unique` | `Mathlib.Order.Bounds.Basic` |
| [order-inherited](../corpus/nodes/order-inherited.json) | `Subtype.partialOrder` | `Mathlib.Order.Basic` |
| [order-injective-monotone-strict](../corpus/nodes/order-injective-monotone-strict.json) | `Monotone.strictMono_of_injective` | `Mathlib.Order.Monotone.Defs` |
| [order-int-linear](../corpus/nodes/order-int-linear.json) | `Int.instLinearOrder` | `Mathlib.Data.Int.Order.Basic` |
| [order-integer-translation](../corpus/nodes/order-integer-translation.json) | `OrderIso.addRight` | `Mathlib.Algebra.Order.Group.OrderIso` |
| [order-isomorphism](../corpus/nodes/order-isomorphism.json) | `OrderIso` | `Mathlib.Order.Hom.Basic` |
| [order-isomorphism-composition](../corpus/nodes/order-isomorphism-composition.json) | `OrderIso.trans` | `Mathlib.Order.Hom.Basic` |
| [order-isomorphism-from-monotone-inverses](../corpus/nodes/order-isomorphism-from-monotone-inverses.json) | `Equiv.toOrderIso` | `Mathlib.Order.Hom.Basic` |
| [order-isomorphism-preserves-infimum](../corpus/nodes/order-isomorphism-preserves-infimum.json) | `OrderIso.isGLB_image'` | `Mathlib.Order.Bounds.OrderIso` |
| [order-isomorphism-preserves-supremum](../corpus/nodes/order-isomorphism-preserves-supremum.json) | `OrderIso.isLUB_image'` | `Mathlib.Order.Bounds.OrderIso` |
| [order-isomorphism-surjective-embedding](../corpus/nodes/order-isomorphism-surjective-embedding.json) | `OrderIso.equivEmbeddingSurjective` | `Mathlib.Order.Hom.Basic` |
| [order-lattice](../corpus/nodes/order-lattice.json) | `Lattice` | `Mathlib.Order.Lattice` |
| [order-least](../corpus/nodes/order-least.json) | `IsLeast` | `Mathlib.Order.Bounds.Defs` |
| [order-least-only-minimal](../corpus/nodes/order-least-only-minimal.json) | `IsLeast.minimal_iff` | `Mathlib.Order.Minimal` |
| [order-least-unique](../corpus/nodes/order-least-unique.json) | `IsLeast.unique` | `Mathlib.Order.Bounds.Basic` |
| [order-linear](../corpus/nodes/order-linear.json) | `IsLinearOrder` | `Mathlib.Order.Defs.Unbundled` |
| [order-linear-maximal-greatest](../corpus/nodes/order-linear-maximal-greatest.json) | `maximal_iff_isGreatest` | `Mathlib.Order.Bounds.Basic` |
| [order-linear-minimal-least](../corpus/nodes/order-linear-minimal-least.json) | `minimal_iff_isLeast` | `Mathlib.Order.Bounds.Basic` |
| [order-linear-strict-reflects](../corpus/nodes/order-linear-strict-reflects.json) | `StrictMono.le_iff_le` | `Mathlib.Order.Monotone.Basic` |
| [order-lower-bounds](../corpus/nodes/order-lower-bounds.json) | `lowerBounds` | `Mathlib.Order.Bounds.Defs` |
| [order-maximal](../corpus/nodes/order-maximal.json) | `Maximal` | `Mathlib.Order.Defs.Unbundled` |
| [order-midpoint-above-left](../corpus/nodes/order-midpoint-above-left.json) | `left_lt_add_div_two` | `Mathlib.Algebra.Order.Field.Basic` |
| [order-midpoint-below-right](../corpus/nodes/order-midpoint-below-right.json) | `add_div_two_lt_right` | `Mathlib.Algebra.Order.Field.Basic` |
| [order-minimal](../corpus/nodes/order-minimal.json) | `Minimal` | `Mathlib.Order.Defs.Unbundled` |
| [order-monotone](../corpus/nodes/order-monotone.json) | `Monotone` | `Mathlib.Order.Monotone.Defs` |
| [order-monotone-composition](../corpus/nodes/order-monotone-composition.json) | `Monotone.comp` | `Mathlib.Order.Monotone.Defs` |
| [order-monotone-image-upper-bound](../corpus/nodes/order-monotone-image-upper-bound.json) | `Monotone.image_upperBounds_subset_upperBounds_image` | `Mathlib.Order.Bounds.Image` |
| [order-mutual-comparison-equality](../corpus/nodes/order-mutual-comparison-equality.json) | `antisymmRel_iff_eq` | `Mathlib.Order.Antisymmetrization` |
| [order-nat-linear](../corpus/nodes/order-nat-linear.json) | `Nat.instLinearOrder` | `Mathlib.Data.Nat.Basic` |
| [order-nonstrict-comparison](../corpus/nodes/order-nonstrict-comparison.json) | `le_iff_lt_or_eq` | `Mathlib.Order.Defs.PartialOrder` |
| [order-open-interval-excludes-left](../corpus/nodes/order-open-interval-excludes-left.json) | `Set.left_notMem_Ioo` | `Mathlib.Order.Interval.Set.Basic` |
| [order-open-interval-excludes-right](../corpus/nodes/order-open-interval-excludes-right.json) | `Set.right_notMem_Ioo` | `Mathlib.Order.Interval.Set.Basic` |
| [order-open-interval-infimum](../corpus/nodes/order-open-interval-infimum.json) | `isGLB_Ioo` | `Mathlib.Order.Bounds.Basic` |
| [order-open-interval-supremum](../corpus/nodes/order-open-interval-supremum.json) | `isLUB_Ioo` | `Mathlib.Order.Bounds.Basic` |
| [order-opposite](../corpus/nodes/order-opposite.json) | `OrderDual.instPartialOrder` | `Mathlib.Order.OrderDual` |
| [order-pair-infimum](../corpus/nodes/order-pair-infimum.json) | `isGLB_pair` | `Mathlib.Order.Bounds.Basic` |
| [order-pair-supremum](../corpus/nodes/order-pair-supremum.json) | `isLUB_pair` | `Mathlib.Order.Bounds.Basic` |
| [order-partial](../corpus/nodes/order-partial.json) | `IsPartialOrder` | `Mathlib.Order.Defs.Unbundled` |
| [order-power-set-complete-lattice](../corpus/nodes/order-power-set-complete-lattice.json) | `Set.instCompleteAtomicBooleanAlgebra` | `Mathlib.Data.Set.BooleanAlgebra` |
| [order-preorder](../corpus/nodes/order-preorder.json) | `IsPreorder` | `Mathlib.Order.Defs.Unbundled` |
| [order-rat-linear](../corpus/nodes/order-rat-linear.json) | `Rat.linearOrder` | `Mathlib.Algebra.Order.Ring.Unbundled.Rat` |
| [order-real-linear](../corpus/nodes/order-real-linear.json) | `Real.linearOrder` | `Mathlib.Basic.Real.Basic` |
| [order-strict](../corpus/nodes/order-strict.json) | `IsStrictOrder` | `Mathlib.Order.Defs.Unbundled` |
| [order-strict-asymmetric](../corpus/nodes/order-strict-asymmetric.json) | `lt_asymm` | `Mathlib.Order.Defs.PartialOrder` |
| [order-strict-comparison](../corpus/nodes/order-strict-comparison.json) | `lt_iff_le_and_ne` | `Mathlib.Order.Basic` |
| [order-strict-from-partial](../corpus/nodes/order-strict-from-partial.json) | `instIsStrictOrderLt` | `Mathlib.Order.RelClasses` |
| [order-subsingleton-bottom](../corpus/nodes/order-subsingleton-bottom.json) | `Subsingleton.isBot` | `Mathlib.Order.Max` |
| [order-subsingleton-top](../corpus/nodes/order-subsingleton-top.json) | `Subsingleton.isTop` | `Mathlib.Order.Max` |
| [order-subtype-embedding](../corpus/nodes/order-subtype-embedding.json) | `OrderEmbedding.subtype` | `Mathlib.Order.Hom.Basic` |
| [order-supremum](../corpus/nodes/order-supremum.json) | `IsLUB` | `Mathlib.Order.Bounds.Defs` |
| [order-supremum-member-greatest](../corpus/nodes/order-supremum-member-greatest.json) | `isGreatest_iff_isLUB_and_mem` | `Mathlib.Order.Bounds.Basic` |
| [order-supremum-unique](../corpus/nodes/order-supremum-unique.json) | `IsLUB.unique` | `Mathlib.Order.Bounds.Basic` |
| [order-top](../corpus/nodes/order-top.json) | `IsTop` | `Mathlib.Order.Max` |
| [order-trichotomy](../corpus/nodes/order-trichotomy.json) | `lt_trichotomy` | `Mathlib.Order.Defs.LinearOrder` |
| [order-upper-bounds](../corpus/nodes/order-upper-bounds.json) | `upperBounds` | `Mathlib.Order.Bounds.Defs` |
| [ordered-quotient](../corpus/nodes/ordered-quotient.json) | `Antisymmetrization` | `Mathlib.Order.Antisymmetrization` |
| [ordered-quotient-comparison](../corpus/nodes/ordered-quotient-comparison.json) | `toAntisymmetrization_le_toAntisymmetrization_iff` | `Mathlib.Order.Antisymmetrization` |
| [ordered-quotient-equivalence](../corpus/nodes/ordered-quotient-equivalence.json) | `AntisymmRel.setoid` | `Mathlib.Order.Antisymmetrization` |
| [ordered-quotient-partial-order](../corpus/nodes/ordered-quotient-partial-order.json) | `instPartialOrderAntisymmetrization` | `Mathlib.Order.Antisymmetrization` |
| [ordered-quotient-poset-isomorphism](../corpus/nodes/ordered-quotient-poset-isomorphism.json) | `Lemmatheca.SetTheory.partial_order_quotient_iso` | `Lemmatheca.SetTheory.OrderedSets` |
| [ordered-quotient-projection-monotone](../corpus/nodes/ordered-quotient-projection-monotone.json) | `toAntisymmetrization_mono` | `Mathlib.Order.Antisymmetrization` |
| [ordered-quotient-representatives](../corpus/nodes/ordered-quotient-representatives.json) | `AntisymmRel.le_congr` | `Mathlib.Order.Antisymmetrization` |
| [ordered-quotient-universal-property](../corpus/nodes/ordered-quotient-universal-property.json) | `preordToPartOrdForgetAdjunction` | `Mathlib.Order.Category.PartOrd` |
| [positive-divisibility-definition](../corpus/nodes/positive-divisibility-definition.json) | `dvd_def` | `Mathlib.Algebra.Divisibility.Basic` |
| [positive-divisibility-incomparable](../corpus/nodes/positive-divisibility-incomparable.json) | `Lemmatheca.Entry.OrderedSets.divisibility_incomparable` | `Lemmatheca.Entry.OrderedSets` |
| [positive-divisibility-order](../corpus/nodes/positive-divisibility-order.json) | `Lemmatheca.Entry.OrderedSets.pnatDivisibility` | `Lemmatheca.Entry.OrderedSets` |
| [positive-divisors-twelve](../corpus/nodes/positive-divisors-twelve.json) | `Lemmatheca.Entry.OrderedSets.divisors_twelve` | `Lemmatheca.Entry.OrderedSets` |
| [positive-gcd-greatest](../corpus/nodes/positive-gcd-greatest.json) | `PNat.dvd_gcd` | `Mathlib.Data.PNat.Prime` |
| [positive-gcd-lower-left](../corpus/nodes/positive-gcd-lower-left.json) | `PNat.gcd_dvd_left` | `Mathlib.Data.PNat.Prime` |
| [positive-gcd-lower-right](../corpus/nodes/positive-gcd-lower-right.json) | `PNat.gcd_dvd_right` | `Mathlib.Data.PNat.Prime` |
| [positive-lcm-least](../corpus/nodes/positive-lcm-least.json) | `PNat.lcm_dvd` | `Mathlib.Data.PNat.Prime` |
| [positive-lcm-upper-left](../corpus/nodes/positive-lcm-upper-left.json) | `PNat.dvd_lcm_left` | `Mathlib.Data.PNat.Prime` |
| [positive-lcm-upper-right](../corpus/nodes/positive-lcm-upper-right.json) | `PNat.dvd_lcm_right` | `Mathlib.Data.PNat.Prime` |
| [proper-divisors-twelve-no-upper-bound](../corpus/nodes/proper-divisors-twelve-no-upper-bound.json) | `Lemmatheca.Entry.OrderedSets.proper_divisors_no_upper_bound` | `Lemmatheca.Entry.OrderedSets` |
| [real-open-unit-interval-lower-witness](../corpus/nodes/real-open-unit-interval-lower-witness.json) | `Lemmatheca.Entry.OrderedSets.open_unit_interval_lower_witness` | `Lemmatheca.Entry.OrderedSets` |
| [real-open-unit-interval-upper-witness](../corpus/nodes/real-open-unit-interval-upper-witness.json) | `Lemmatheca.Entry.OrderedSets.open_unit_interval_upper_witness` | `Lemmatheca.Entry.OrderedSets` |
| [real-plane-first-coordinate-classes](../corpus/nodes/real-plane-first-coordinate-classes.json) | `Lemmatheca.Entry.OrderedSets.plane_classes` | `Lemmatheca.Entry.OrderedSets` |
| [real-plane-first-coordinate-not-antisymmetric](../corpus/nodes/real-plane-first-coordinate-not-antisymmetric.json) | `Lemmatheca.Entry.OrderedSets.plane_not_antisymmetric` | `Lemmatheca.Entry.OrderedSets` |
| [real-plane-first-coordinate-preorder](../corpus/nodes/real-plane-first-coordinate-preorder.json) | `Lemmatheca.Entry.OrderedSets.planePreorder` | `Lemmatheca.Entry.OrderedSets` |
| [real-plane-identity-not-factor](../corpus/nodes/real-plane-identity-not-factor.json) | `Lemmatheca.Entry.OrderedSets.plane_identity_not_factor` | `Lemmatheca.Entry.OrderedSets` |
| [real-plane-ordered-quotient-isomorphism](../corpus/nodes/real-plane-ordered-quotient-isomorphism.json) | `Lemmatheca.Entry.OrderedSets.plane_quotient_order_iso` | `Lemmatheca.Entry.OrderedSets` |
| [set-singleton-inclusion](../corpus/nodes/set-singleton-inclusion.json) | `Set.singleton_subset_singleton` | `Mathlib.Data.Set.Insert` |

Reused nodes: [empty-relation-equivalence](../corpus/nodes/empty-relation-equivalence.json), [equality-equivalence-relation](../corpus/nodes/equality-equivalence-relation.json), [quotient-projection-equality](../corpus/nodes/quotient-projection-equality.json), [quotient-projection-surjective](../corpus/nodes/quotient-projection-surjective.json), [set-empty-family-intersection](../corpus/nodes/set-empty-family-intersection.json), [set-empty-family-union](../corpus/nodes/set-empty-family-union.json), [set-powerset-empty](../corpus/nodes/set-powerset-empty.json), [set-proper-subset](../corpus/nodes/set-proper-subset.json).

## Correspondence review on GitHub

Review the mathematical descriptions against the actual signatures and source
bodies, particularly these representation choices:

- Does the complete-lattice binding faithfully express the relative universe U,
  including the empty-family intersection and the singleton power set of the empty set?
- Do the divisor labels and cover-pair list agree with the SVG, and is 12 removed
  from the ambient type in the unboundedness example?
- Does the categorical `homEquiv` make existence, uniqueness and the explicit
  evaluation rule sufficiently clear to readers of the factorization node?
- Do the counterexample statements retain the intended witnesses and distinguish
  arbitrary-representative comparison from existential-representative comparison?

Lean compilation and axiom checks establish well-formedness and recorded proof
status; they do not approve the correspondence to the prose. No review state is
stored in the corpus.

## Checks performed

The corpus build and `app/manage.py test catalog` pass. The build supplies every
new node's signature, defining module, declaration line and verification flag,
and refreshes the entry summary. All new theorem stubs remain unverified.
Additional Lean checks confirm the actual comparisons on the custom order types,
the finite-poset specialization of the cover-path theorem, and empty power-set bounds.
The hint graph has no new cycles, missing targets or transitive duplicates.
The entry's mathematical prose is unchanged. The rendered entry disclosure and
an unfinished node's source-line navigation were checked in the browser; the reader
tests exercise every registered node page and every entry's formal links.
