# Mathlib binding audit

The sets-and-maps audit uses the pinned mathlib v4.34.0 and Lean 4.34.0 sources.
The first pass replaced 48 local declarations with existing library targets and
removed their duplicate wrappers, preserving node IDs and dependency edges. The general
`SetsAndElements.lean` module is removed because both its declarations already
exist in mathlib; callers now import mathlib directly.

Lean checked each replacement against the previous statement, using specialization,
equality symmetry, or the conversions described below where necessary. For strict
inclusion and disjointness, the library characterization theorems establish the
previous definitions. This checks the mathematical correspondence; it does not
record human approval. Replacement reviews were cleared for explicit review.

Two retained examples now state their claims using standard predicates:

- `nat-disjoint-sets-example` uses `Disjoint` instead of the local `setsDisjoint`.
- `set-preimage-image-strict-example` uses `⊂` instead of the local `properSubset`.

These two reviews were also retracted because their elaborated statements changed.
The follow-up below splits bundled claims into standard library nodes and updates
their references. All 127 current nodes pass Lean verification. Changed nodes await
explicit review; approved nodes can still await their dependencies.

## Replacement targets

An empty note means the mathematical statement is unchanged, apart from implicit
arguments or argument order. Core Lean targets are imported through a mathlib module;
verification records their actual defining source and line.

| Node | Library declaration | Correspondence to the previous target |
| --- | --- | --- |
| [map-bijective-iff-unique-preimages](../formal/nodes/map-bijective-iff-unique-preimages.json) | `Function.bijective_iff_existsUnique` |  |
| [map-composition](../formal/nodes/map-composition.json) | `Function.comp` | Same definition, generalized from Type to Sort. |
| [map-composition-associative](../formal/nodes/map-composition-associative.json) | `Function.comp_assoc` |  |
| [map-empty-domain-injective](../formal/nodes/map-empty-domain-injective.json) | `Function.injective_of_subsingleton` | Stronger result: a subsingleton domain suffices; every empty type is a subsingleton. |
| [map-empty-domain-surjective-iff](../formal/nodes/map-empty-domain-surjective-iff.json) | `Function.surjective_iff_isEmpty` |  |
| [map-equality](../formal/nodes/map-equality.json) | `funext_iff` | Dependent function extensionality specializes to ordinary maps. |
| [map-identity](../formal/nodes/map-identity.json) | `id` | Same definition; the ambient type becomes implicit and may be any Sort. |
| [map-inverse-exists-iff-bijective](../formal/nodes/map-inverse-exists-iff-bijective.json) | `Function.bijective_iff_has_inverse` | Same equivalence, reversed; inverse laws are pointwise instead of composition equalities. |
| [map-inverse-unique](../formal/nodes/map-inverse-unique.json) | `Function.LeftInverse.eq_rightInverse` | Stronger result: a left inverse equals a right inverse; two two-sided inverses specialize to these hypotheses. |
| [map-range-is-image-universe](../formal/nodes/map-range-is-image-universe.json) | `Set.image_univ` | Same equality, reversed. |
| [map-restriction](../formal/nodes/map-restriction.json) | `Set.domRestrict` | Dependent-domain restriction specializes to the constant codomain β; set argument comes first. |
| [map-surjective-iff-range-universe](../formal/nodes/map-surjective-iff-range-universe.json) | `Set.range_eq_univ` | Same equivalence, reversed. |
| [nat-initial-segments-union](../formal/nodes/nat-initial-segments-union.json) | `Set.iUnion_Iic` | Specialize to ℕ; Iic n is the set {k \| k ≤ n}. |
| [nat-zero-in-even-set](../formal/nodes/nat-zero-in-even-set.json) | `Even.zero` | Specialize to ℕ and unfold evenNaturals; the general theorem assumes AddZeroClass. |
| [ordered-pair-equality](../formal/nodes/ordered-pair-equality.json) | `Prod.ext_iff` | Applies to arbitrary pairs; specialize to (a, b) and (a′, b′). |
| [set-complement-intersection](../formal/nodes/set-complement-intersection.json) | `Set.compl_inter` |  |
| [set-complement-union](../formal/nodes/set-complement-union.json) | `Set.compl_union` |  |
| [set-empty-family-intersection](../formal/nodes/set-empty-family-intersection.json) | `Set.iInter_of_empty` |  |
| [set-empty-family-union](../formal/nodes/set-empty-family-union.json) | `Set.iUnion_of_empty` |  |
| [set-empty-subset](../formal/nodes/set-empty-subset.json) | `Set.empty_subset` |  |
| [set-equality-iff-two-inclusions](../formal/nodes/set-equality-iff-two-inclusions.json) | `Set.Subset.antisymm_iff` |  |
| [set-extensionality](../formal/nodes/set-extensionality.json) | `Set.ext_iff` |  |
| [set-image-intersection-subset](../formal/nodes/set-image-intersection-subset.json) | `Set.image_inter_subset` |  |
| [set-image-preimage](../formal/nodes/set-image-preimage.json) | `Set.image_preimage_eq_inter_range` |  |
| [set-image-preimage-of-surjective](../formal/nodes/set-image-preimage-of-surjective.json) | `Set.image_preimage_eq` |  |
| [set-image-union](../formal/nodes/set-image-union.json) | `Set.image_union` |  |
| [set-indexed-intersection-membership](../formal/nodes/set-indexed-intersection-membership.json) | `Set.mem_iInter` |  |
| [set-indexed-union-membership](../formal/nodes/set-indexed-union-membership.json) | `Set.mem_iUnion` |  |
| [set-insert-commute](../formal/nodes/set-insert-commute.json) | `Set.insert_comm` |  |
| [set-insert-repeat](../formal/nodes/set-insert-repeat.json) | `Set.insert_idem` |  |
| [set-intersection-commutative](../formal/nodes/set-intersection-commutative.json) | `Set.inter_comm` |  |
| [set-intersection-distributes-over-union](../formal/nodes/set-intersection-distributes-over-union.json) | `Set.inter_union_distrib_left` |  |
| [set-intersection-empty](../formal/nodes/set-intersection-empty.json) | `Set.inter_empty` |  |
| [set-powerset-empty](../formal/nodes/set-powerset-empty.json) | `Set.powerset_empty` |  |
| [set-preimage-complement](../formal/nodes/set-preimage-complement.json) | `Set.preimage_compl` |  |
| [set-preimage-empty](../formal/nodes/set-preimage-empty.json) | `Set.preimage_empty` |  |
| [set-preimage-image-of-injective](../formal/nodes/set-preimage-image-of-injective.json) | `Set.preimage_image_eq` |  |
| [set-preimage-intersection](../formal/nodes/set-preimage-intersection.json) | `Set.preimage_inter` |  |
| [set-preimage-is-inverse-image](../formal/nodes/set-preimage-is-inverse-image.json) | `Set.image_eq_preimage_of_inverse` | Swap f and g and evaluate the equality of set operators at T; inverse laws are pointwise. |
| [set-preimage-union](../formal/nodes/set-preimage-union.json) | `Set.preimage_union` |  |
| [set-preimage-universe](../formal/nodes/set-preimage-universe.json) | `Set.preimage_univ` |  |
| [set-proper-subset](../formal/nodes/set-proper-subset.json) | `Set.ssubset_iff_subset_ne` | Characterizes standard strict inclusion by exactly the subset-and-inequality condition in the entry. |
| [set-subset-preimage-image](../formal/nodes/set-subset-preimage-image.json) | `Set.subset_preimage_image` |  |
| [set-subset-reflexive](../formal/nodes/set-subset-reflexive.json) | `Set.Subset.refl` |  |
| [set-subset-transitive](../formal/nodes/set-subset-transitive.json) | `Set.Subset.trans` |  |
| [set-union-commutative](../formal/nodes/set-union-commutative.json) | `Set.union_comm` |  |
| [set-union-empty](../formal/nodes/set-union-empty.json) | `Set.union_empty` |  |
| [sets-disjoint](../formal/nodes/sets-disjoint.json) | `Set.disjoint_iff_inter_eq_empty` | Characterizes standard Disjoint by exactly the empty-intersection condition in the entry. |

## Split bundles and further standardization

This pass creates 14 nodes, rebinds two existing nodes, updates four dependent
nodes, and retires eight bundled nodes. All 20 new or updated records have
`review: null`; unchanged node records retain their reviews. Ten local wrappers
are removed. Lean checked that the listed library statements together recover
every claim in the removed bundles, including the existence part of uniqueness.

| Retired node | Replacement nodes |
| --- | --- |
| `map-composition-identity` | [map-composition-left-identity](../formal/nodes/map-composition-left-identity.json), [map-composition-right-identity](../formal/nodes/map-composition-right-identity.json) |
| `set-empty-quantifiers` | [set-empty-forall](../formal/nodes/set-empty-forall.json), [set-empty-exists](../formal/nodes/set-empty-exists.json) |
| `set-powerset-contains-empty-and-self` | [set-empty-subset](../formal/nodes/set-empty-subset.json), [set-subset-reflexive](../formal/nodes/set-subset-reflexive.json) |
| `set-empty-cartesian-products` | [set-cartesian-product-empty-left](../formal/nodes/set-cartesian-product-empty-left.json), [set-cartesian-product-empty-right](../formal/nodes/set-cartesian-product-empty-right.json) |
| `set-empty-or-singleton-answer` | [set-empty-ne-singleton](../formal/nodes/set-empty-ne-singleton.json), [set-singleton-contains-self](../formal/nodes/set-singleton-contains-self.json), [set-empty-subset](../formal/nodes/set-empty-subset.json) |
| `map-empty-self-bijective-and-inverse` | [map-empty-self-bijective](../formal/nodes/map-empty-self-bijective.json), [map-empty-domain-equality](../formal/nodes/map-empty-domain-equality.json) |
| `nat-successor-injective-not-surjective` | [nat-successor-injective](../formal/nodes/nat-successor-injective.json), [nat-successor-ne-zero](../formal/nodes/nat-successor-ne-zero.json) |
| `map-inverse` | [map-left-inverse](../formal/nodes/map-left-inverse.json), [map-right-inverse](../formal/nodes/map-right-inverse.json) |

The power-set membership claims reuse `set-empty-subset` and `set-subset-reflexive`:
membership in a powerset is definitionally the subset relation. Neither existing
node is changed or duplicated. The entry maps both claims, and the empty-set/singleton
question similarly reuses `set-empty-subset` for its inclusion answer.

New and rebound library targets for review:

| Node | Library declaration | Review note |
| --- | --- | --- |
| [map-composition-left-identity](../formal/nodes/map-composition-left-identity.json) | `Function.id_comp` | Identity after a map: id ∘ f = f. |
| [map-composition-right-identity](../formal/nodes/map-composition-right-identity.json) | `Function.comp_id` | Identity before a map: f ∘ id = f. |
| [set-empty-forall](../formal/nodes/set-empty-forall.json) | `Set.forall_mem_empty` | Mathlib expresses the universally quantified statement as equivalent to True. |
| [set-empty-exists](../formal/nodes/set-empty-exists.json) | `Set.exists_mem_empty` | Mathlib expresses the existentially quantified statement as equivalent to False. |
| [set-cartesian-product-empty-left](../formal/nodes/set-cartesian-product-empty-left.json) | `Set.empty_prod` | The left Cartesian factor is empty. |
| [set-cartesian-product-empty-right](../formal/nodes/set-cartesian-product-empty-right.json) | `Set.prod_empty` | The right Cartesian factor is empty. |
| [set-empty-ne-singleton](../formal/nodes/set-empty-ne-singleton.json) | `Set.empty_ne_singleton` | Specialize the singleton element to the empty set. |
| [set-singleton-contains-self](../formal/nodes/set-singleton-contains-self.json) | `Set.mem_singleton` | Specialize the element to the empty set; reuse set-empty-subset for the third answer. |
| [map-empty-self-bijective](../formal/nodes/map-empty-self-bijective.json) | `Function.Bijective.of_isEmpty` | Specialize the codomain-empty theorem to an empty self-map. |
| [map-empty-domain-equality](../formal/nodes/map-empty-domain-equality.json) | `IsEmpty.congr_fun` | Two maps from an empty domain to a fixed codomain are equal. Apply to f ∘ f and id to obtain both self-inverse identities. |
| [nat-successor-injective](../formal/nodes/nat-successor-injective.json) | `Nat.succ_injective` | Injectivity of successor. |
| [nat-successor-ne-zero](../formal/nodes/nat-successor-ne-zero.json) | `Nat.succ_ne_zero` | Every successor is nonzero, so zero is outside the range and successor is not surjective. |
| [map-left-inverse](../formal/nodes/map-left-inverse.json) | `Function.LeftInverse` | The pointwise law g (f x) = x; both inverse predicates are required together. |
| [map-right-inverse](../formal/nodes/map-right-inverse.json) | `Function.RightInverse` | The pointwise law f (g y) = y; both inverse predicates are required together. |
| [map-empty-domain-unique](../formal/nodes/map-empty-domain-unique.json) | `Pi.uniqueOfIsEmpty` | The Unique instance contains both a map and uniqueness. Specialize the dependent codomain to a constant type. |
| [map-nonempty-to-empty-impossible](../formal/nodes/map-nonempty-to-empty-impossible.json) | `isEmpty_fun` | Characterizes emptiness of the function type by nonempty domain and empty codomain; IsEmpty is equivalent to absence of inhabitants. |

Also review these four updated records:

- [map-inverse-exists-iff-bijective](../formal/nodes/map-inverse-exists-iff-bijective.json): dependency on `map-inverse` replaced by both standard inverse nodes; the library target is unchanged.
- [map-inverse-unique](../formal/nodes/map-inverse-unique.json): dependency on `map-inverse` replaced by both standard inverse nodes; the library target is unchanged.
- [set-preimage-is-inverse-image](../formal/nodes/set-preimage-is-inverse-image.json): dependency on `map-inverse` replaced by both standard inverse nodes; the library target is unchanged.
- [nat-one-sided-inverse-counterexample](../formal/nodes/nat-one-sided-inverse-counterexample.json): dependency links now use the separate inverse and successor nodes. Its statement uses `Function.LeftInverse` and `Function.RightInverse` instead of the removed local predicate.

## Retained local declarations

The remaining nine general declarations describe maps, relation types, total
single-valued graphs, fibers and their characterizations, and the graph of an
empty-domain map. This audit found no direct standard declaration for those
particular presentations. The remaining 33 entry declarations specify concrete
sets, the diagram, counterexamples, or answers with additional conditions and witnesses.
Bundled examples remain local when decomposing them would still require custom claims.

After the subsequent source-layout cleanup, the nine general declarations share
`formal/Lemmatheca/SetTheory/Basic.lean`, with node module
`Lemmatheca.SetTheory.Basic`. The 33 entry declarations share
`formal/Lemmatheca/Entry/SetsAndMaps.lean`, with node module
`Lemmatheca.Entry.SetsAndMaps`. Declaration names, statements, and proofs are
unchanged. `SetTheory.lean` imports the theory modules; the entry module imports
the basic theory and its mathlib prerequisites. The maintainer authorized
refreshing first-entry approvals affected by these module moves; this does not
approve the new equivalence-relations nodes.
