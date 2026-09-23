# Equivalence-relations formal bindings

This is the preparation record for pipeline step 4, not an independent
correspondence review. Every one of the entry’s 15 blocks has a nonempty mapping.
There are 72 distinct linked nodes: 62 new nodes and 10 reused nodes. No existing
node is rebound or retired. All new nodes have `review: null` and need human review.

Of the new nodes, 41 bind directly to Lean or mathlib and have complete proof
evidence. The other 21 are new theorem statements with `by sorry`: seven reusable
statements in `Lemmatheca.SetTheory.EquivalenceRelations` and fourteen examples in
`Lemmatheca.Entry.EquivalenceRelations`. These declarations compile, but their
proofs are unfinished. No production theorem was proved or review accepted at this stage.

## Representations

- An ambient type represents the entry’s set A; a specified subset of a larger
  type can instead be its subtype. Curried predicates `A → A → Prop` represent
  relations contained in A × A. A `Setoid A` bundles such a relation with its
  equivalence proof.
- `Setoid.classes` is literally a set of subsets, matching the human quotient
  as a set. For map domains and codomains we use `Quotient s`, together with
  `Setoid.quotientEquivClasses` and its computation rule. The subset `{x | s x a}`
  equals `{x | s a x}` by symmetry; class subtypes do not identify the original
  elements of A.
- `Setoid.IsPartition` excludes the empty part and asserts unique membership.
  The disjoint-cover characterization is covered collectively by the four
  linked library consequences/converse. The partition order isomorphism’s
  inverse uses universal membership preservation (`mkClasses`); its inverse
  law plus `rel_iff_exists_classes` gives precisely the human existential
  common-part rule. No extra equivalence assumption is needed.
- Parity uses `Int.ModEq 2`, definitionally the kernel of `n ↦ n % 2`. Mathlib’s
  difference is b − a; negating a divisibility witness gives a − b = 2k. The
  finite examples use `Fin 3`, with the original `diagramMap` and `MapLabel`
  from the sets-and-maps entry. The working parity label has codomain `Fin 2`.
- `Setoid.liftEquiv` includes existence, necessity, uniqueness, and evaluation
  on representatives. The range and injectivity lemmas use its canonical lift;
  uniqueness transfers them to the arbitrary factor map in the text.
  `Quotient.map` preserves equivalence in the output relation. Necessity follows
  by applying the same universal property to `q_B ∘ h`, using `Quotient.eq`.
- `Setoid.quotientKerEquivRange` returns an actual element of the range subtype,
  so the codomain restriction is explicit. Its value at `[a]` is `f(a)`, and
  composing with subtype inclusion recovers f by computation. The separate
  inverse-fiber statement records the explicit inverse in the set-of-classes
  representation. The universal-relation singleton requires nonempty A;
  empty quotients are treated separately.

Temporary Lean checks outside the tracked sources validate the class equality
criterion, argument-order convention, common-part interpretation of `mkClasses`,
parity divisibility convention, unique factorization in both directions,
preservation of the output relation, equality-quotient class formula, projection
injectivity criterion, and the quotient-to-range evaluation/factorization.
They use library results and do not prove any pending production theorem.

## Coverage by block

| Human block and claims | Covering nodes | Representation and coverage notes |
| --- | --- | --- |
| [Equivalence relations](../corpus/entries/equivalence-relations/entry.html#relation-properties) | [set-relation-between](../formal/nodes/set-relation-between.json), [relation-reflexive](../formal/nodes/relation-reflexive.json), [relation-symmetric](../formal/nodes/relation-symmetric.json), [relation-transitive](../formal/nodes/relation-transitive.json), [equivalence-relation](../formal/nodes/equivalence-relation.json), [relation-not-symmetric-iff-witness](../formal/nodes/relation-not-symmetric-iff-witness.json), [equality-equivalence-relation](../formal/nodes/equality-equivalence-relation.json), [universal-equivalence-relation](../formal/nodes/universal-equivalence-relation.json), [int-congruence](../formal/nodes/int-congruence.json), [int-congruence-equivalence](../formal/nodes/int-congruence-equivalence.json), [int-congruence-iff-divides-difference](../formal/nodes/int-congruence-iff-divides-difference.json), [int-parity-distinct-equivalent](../formal/nodes/int-parity-distinct-equivalent.json), [fin-three-two-block-relation](../formal/nodes/fin-three-two-block-relation.json), [map-kernel-relation](../formal/nodes/map-kernel-relation.json) | Relations as predicates on the type A represent subsets of A × A. The three properties, their conjunction, and the witness criterion for failure of symmetry are covered. Int.ModEq 2 is parity: divisibility of b − a is equivalent to a − b = 2k by negating the witness. The finite relation is the kernel of the already registered diagramMap; its equivalence proof is supplied by Setoid.ker. |
| [Can one condition be omitted?](../corpus/entries/equivalence-relations/entry.html#are-all-three-needed) | [fin-three-empty-relation-not-reflexive](../formal/nodes/fin-three-empty-relation-not-reflexive.json), [fin-three-le-not-symmetric](../formal/nodes/fin-three-le-not-symmetric.json), [fin-three-adjacency-not-transitive](../formal/nodes/fin-three-adjacency-not-transitive.json) | The three specified counterexamples use Fin 3, with explicit asymmetry/transitivity witnesses and the overlapping neighbourhoods in the last example. The empty relation has no pairs, in particular (0,0). |
| [Classes and representatives](../corpus/entries/equivalence-relations/entry.html#equivalence-classes) | [equivalence-classes](../formal/nodes/equivalence-classes.json), [quotient-class-of-representative](../formal/nodes/quotient-class-of-representative.json), [equivalence-class-contains-self](../formal/nodes/equivalence-class-contains-self.json), [fin-three-two-block-classes](../formal/nodes/fin-three-two-block-classes.json), [int-even-or-odd-exclusively](../formal/nodes/int-even-or-odd-exclusively.json), [int-parity-classes](../formal/nodes/int-parity-classes.json), [int-parity-classes-infinite](../formal/nodes/int-parity-classes-infinite.json) | The class {x \| R x a} equals the text’s {x \| R a x} by symmetry. Covers membership/nonemptiness, all finite classes, exclusive even/odd alternatives, the two parity classes and their infinitude. |
| [Classes are equal or disjoint](../corpus/entries/equivalence-relations/entry.html#equal-or-disjoint-classes) | [quotient-projection-equality](../formal/nodes/quotient-projection-equality.json), [quotient-equivalence-classes](../formal/nodes/quotient-equivalence-classes.json), [quotient-class-of-representative](../formal/nodes/quotient-class-of-representative.json), [equivalence-relations-partitions-correspondence](../formal/nodes/equivalence-relations-partitions-correspondence.json), [set-partition-parts-disjoint](../formal/nodes/set-partition-parts-disjoint.json) | Quotient.eq plus the injective equivalence to class subtypes gives class equality iff related. The partition corresponding to a setoid has these classes; distinct parts are disjoint. Changing representatives is already included in the iff. |
| [Partitions of a set](../corpus/entries/equivalence-relations/entry.html#partitions) | [set-partition](../formal/nodes/set-partition.json), [set-partition-parts-nonempty](../formal/nodes/set-partition-parts-nonempty.json), [set-partition-parts-disjoint](../formal/nodes/set-partition-parts-disjoint.json), [set-partition-covers](../formal/nodes/set-partition-covers.json), [disjoint-cover-unique-membership](../formal/nodes/disjoint-cover-unique-membership.json), [equivalence-relations-partitions-correspondence](../formal/nodes/equivalence-relations-partitions-correspondence.json), [fin-three-two-block-classes](../formal/nodes/fin-three-two-block-classes.json), [fin-three-overlapping-parts-not-partition](../formal/nodes/fin-three-overlapping-parts-not-partition.json), [fin-three-missing-part-not-partition](../formal/nodes/fin-three-missing-part-not-partition.json), [set-insert-repeat](../formal/nodes/set-insert-repeat.json) | IsPartition uses no empty part plus unique membership. The three forward properties and converse disjoint-cover theorem establish the text’s equivalent definition. The finite class computation plus the correspondence yields the valid partition. Counterexamples cover overlap and omitted 2; the definition excludes adding ∅. Set.insert_idem covers duplicate listing. |
| [Equivalence relations and partitions determine each other](../corpus/entries/equivalence-relations/entry.html#partition-correspondence) | [equivalence-relations-partitions-correspondence](../formal/nodes/equivalence-relations-partitions-correspondence.json), [equivalent-iff-common-class](../formal/nodes/equivalent-iff-common-class.json) | The order isomorphism contains both constructions and both inverse laws; refinement preservation is extra generality. Its inverse uses mkClasses (universal membership preservation). Applying rel_iff_exists_classes and the inverse law identifies this with the text’s existential common-part predicate. |
| [The quotient set and its projection](../corpus/entries/equivalence-relations/entry.html#quotient-set) | [equivalence-classes](../formal/nodes/equivalence-classes.json), [quotient-equivalence-classes](../formal/nodes/quotient-equivalence-classes.json), [quotient-class-of-representative](../formal/nodes/quotient-class-of-representative.json), [quotient-projection](../formal/nodes/quotient-projection.json), [quotient-projection-surjective](../formal/nodes/quotient-projection-surjective.json), [quotient-projection-equality](../formal/nodes/quotient-projection-equality.json), [fin-three-two-block-classes](../formal/nodes/fin-three-two-block-classes.json), [int-parity-classes](../formal/nodes/int-parity-classes.json) | Setoid.classes is literally a set of subsets; Quotient is the equivalent type used for map domains. quotientEquivClasses and its computation rule supply the bridge. The finite classes recover every arrow and label in the figure; parity classes recover {E,O}. No separate duplicate diagram nodes. |
| [What happens at the extremes?](../corpus/entries/equivalence-relations/entry.html#extreme-and-empty-cases) | [equality-quotient-equivalence](../formal/nodes/equality-quotient-equivalence.json), [universal-relation-classes](../formal/nodes/universal-relation-classes.json), [map-injective-iff-kernel-equality](../formal/nodes/map-injective-iff-kernel-equality.json), [quotient-projection-kernel](../formal/nodes/quotient-projection-kernel.json), [empty-relation-equivalence](../formal/nodes/empty-relation-equivalence.json), [empty-equivalence-classes](../formal/nodes/empty-equivalence-classes.json), [empty-partition-iff](../formal/nodes/empty-partition-iff.json), [empty-quotient](../formal/nodes/empty-quotient.json), [map-empty-domain-unique](../formal/nodes/map-empty-domain-unique.json), [map-empty-self-bijective](../formal/nodes/map-empty-self-bijective.json), [set-empty-ne-singleton](../formal/nodes/set-empty-ne-singleton.json) | Bottom setoid is equality and its classes are singletons by unfolding; quotientBotEquiv has inverse the projection. The universal case assumes Nonempty A. Apply injective_iff_ker_bot to the projection and ker_mk_eq. Empty relations all equal False, so equality and the universal relation coincide. The empty partition characterization excludes {∅}; the empty quotient and existing unique-map/bijection nodes cover its projection. |
| [Does a rule on representatives define a map?](../corpus/entries/equivalence-relations/entry.html#rules-on-representatives) | [int-parity-identity-not-descend](../formal/nodes/int-parity-identity-not-descend.json), [int-parity-label-descends](../formal/nodes/int-parity-label-descends.json), [quotient-map-universal-property](../formal/nodes/quotient-map-universal-property.json) | The failed rule includes [0]=[2] and the incompatible outputs. The working rule has codomain Fin 2, representing {0,1}. Composing with the natural inclusion Fin 2 → ℤ gives the alternative chosen-representative map, not the failed identity rule. The universal property defines agreement on representatives. |
| [When a map passes to the quotient](../corpus/entries/equivalence-relations/entry.html#maps-from-quotients) | [quotient-map-universal-property](../formal/nodes/quotient-map-universal-property.json) | liftEquiv bijects class-constant maps with quotient maps, with inverse g ↦ g ∘ q. Its two inverse laws give necessity, existence and uniqueness; its forward definition is Quotient.lift, which computes to f(a) at q(a). Thus no separate weaker existence or uniqueness wrappers are registered. |
| [Which properties survive the quotient?](../corpus/entries/equivalence-relations/entry.html#induced-map-properties) | [quotient-lift-range](../formal/nodes/quotient-lift-range.json), [quotient-lift-surjective-iff](../formal/nodes/quotient-lift-surjective-iff.json), [quotient-lift-injective-iff](../formal/nodes/quotient-lift-injective-iff.json), [quotient-map-universal-property](../formal/nodes/quotient-map-universal-property.json) | The canonical lift has the same range and the stated surjectivity criterion. With R ≤ ker f already assumed, ker f = R is equivalent to the displayed reverse implication. Uniqueness transfers these statements to any factor map satisfying the text’s equation. |
| [What if the output is also a class?](../corpus/entries/equivalence-relations/entry.html#maps-between-quotients) | [map-between-quotients](../formal/nodes/map-between-quotients.json), [quotient-map-universal-property](../formal/nodes/quotient-map-universal-property.json), [quotient-projection-equality](../formal/nodes/quotient-projection-equality.json), [int-parity-successor-descends](../formal/nodes/int-parity-successor-descends.json) | Quotient.map supplies the induced map. The universal property for f = q_B ∘ h and Quotient.eq give necessity as well as sufficiency of preservation of equivalence. The parity theorem specifies all representative values, swaps the two classes and includes involutivity. |
| [A map groups its inputs into fibers](../corpus/entries/equivalence-relations/entry.html#relation-from-a-map) | [map-kernel-relation](../formal/nodes/map-kernel-relation.json), [map-kernel-class-fiber](../formal/nodes/map-kernel-class-fiber.json), [map-kernel-classes-nonempty-fibers](../formal/nodes/map-kernel-classes-nonempty-fibers.json), [map-fiber-nonempty-iff-in-range](../formal/nodes/map-fiber-nonempty-iff-in-range.json), [map-injective-iff-fibers-subsingleton](../formal/nodes/map-injective-iff-fibers-subsingleton.json), [map-surjective-iff-fibers-nonempty](../formal/nodes/map-surjective-iff-fibers-nonempty.json), [quotient-projection-kernel](../formal/nodes/quotient-projection-kernel.json) | Kernel equivalence, pointwise class/fiber equality, and the exact family of nonempty fibers are covered. A fiber at a missed value is empty by negating the nonempty criterion. Injectivity plus nonempty fibers gives singletons; surjectivity gives every fiber nonempty. ker_mk_eq recovers any original relation. |
| [Recovering the finite example](../corpus/entries/equivalence-relations/entry.html#finite-fibres-question) | [map-diagram-values](../formal/nodes/map-diagram-values.json), [map-diagram-images-and-preimages](../formal/nodes/map-diagram-images-and-preimages.json), [map-diagram-fiber-p-and-range](../formal/nodes/map-diagram-fiber-p-and-range.json), [fin-three-two-block-classes](../formal/nodes/fin-three-two-block-classes.json), [map-kernel-lift](../formal/nodes/map-kernel-lift.json), [quotient-lift-injective-iff](../formal/nodes/quotient-lift-injective-iff.json), [quotient-lift-surjective-iff](../formal/nodes/quotient-lift-surjective-iff.json), [map-diagram-neither-injective-nor-surjective](../formal/nodes/map-diagram-neither-injective-nor-surjective.json), [quotient-kernel-equiv-range](../formal/nodes/quotient-kernel-equiv-range.json) | Reuse the original map, q/r fibers and failure of surjectivity. The new calculation supplies only the missing p fiber and range. kerLift computes to the existing map values; the generic injectivity criterion specializes with R = ker f. The surjectivity iff retains the missed r; quotientKerEquivRange covers the restricted codomain bijection. |
| [The quotient by fibers is in bijection with the image](../corpus/entries/equivalence-relations/entry.html#quotient-is-image) | [quotient-kernel-equiv-range](../formal/nodes/quotient-kernel-equiv-range.json), [quotient-image-inverse-fiber](../formal/nodes/quotient-image-inverse-fiber.json), [quotient-projection-surjective](../formal/nodes/quotient-projection-surjective.json), [subtype-inclusion-injective](../formal/nodes/subtype-inclusion-injective.json), [quotient-kernel-equiv-codomain](../formal/nodes/quotient-kernel-equiv-codomain.json), [empty-quotient](../formal/nodes/empty-quotient.json), [map-empty-domain-range](../formal/nodes/map-empty-domain-range.json), [map-empty-domain-unique](../formal/nodes/map-empty-domain-unique.json) | The library equivalence sends [a] to f(a) in the range subtype. Composing with its inclusion gives f by computation. The inverse-fiber statement records the explicit set returned, without imposing a representative choice. Projection surjectivity, inclusion injectivity, the surjective case and the unique empty case are covered. |

## New targets needing review

Every row below needs human declaration review. Descriptions are in the linked
JSON records; current Lean signatures and source locations are in the node pages
and `formal/checks/nodes.json`. Library nodes have no manually planned proof
prerequisites: their existing proofs and the checker’s transitive axiom audit
supply the evidence without recreating mathlib’s dependency graph.

| Node | Target declaration | Evidence | Planned proof prerequisites |
| --- | --- | --- | --- |
| [disjoint-cover-unique-membership](../formal/nodes/disjoint-cover-unique-membership.json) | `Setoid.eqv_classes_of_disjoint_union` | Library proof complete | None |
| [empty-equivalence-classes](../formal/nodes/empty-equivalence-classes.json) | `Lemmatheca.SetTheory.empty_equivalence_classes` | Proof pending | None |
| [empty-partition-iff](../formal/nodes/empty-partition-iff.json) | `Lemmatheca.SetTheory.empty_partition_iff` | Proof pending | None |
| [empty-quotient](../formal/nodes/empty-quotient.json) | `Quotient.instIsEmpty` | Library proof complete | None |
| [empty-relation-equivalence](../formal/nodes/empty-relation-equivalence.json) | `Lemmatheca.SetTheory.empty_relation` | Proof pending | [map-empty-domain-equality](../formal/nodes/map-empty-domain-equality.json) |
| [equality-equivalence-relation](../formal/nodes/equality-equivalence-relation.json) | `eq_equivalence` | Library proof complete | None |
| [equality-quotient-equivalence](../formal/nodes/equality-quotient-equivalence.json) | `Setoid.quotientBotEquiv` | Library proof complete | None |
| [equivalence-class-contains-self](../formal/nodes/equivalence-class-contains-self.json) | `Setoid.refl'` | Library proof complete | None |
| [equivalence-classes](../formal/nodes/equivalence-classes.json) | `Setoid.classes` | Library proof complete | None |
| [equivalence-relation](../formal/nodes/equivalence-relation.json) | `Equivalence` | Library proof complete | None |
| [equivalence-relations-partitions-correspondence](../formal/nodes/equivalence-relations-partitions-correspondence.json) | `Setoid.Partition.orderIso` | Library proof complete | None |
| [equivalent-iff-common-class](../formal/nodes/equivalent-iff-common-class.json) | `Setoid.rel_iff_exists_classes` | Library proof complete | None |
| [fin-three-adjacency-not-transitive](../formal/nodes/fin-three-adjacency-not-transitive.json) | `Lemmatheca.Entry.EquivalenceRelations.adjacent_not_transitive` | Proof pending | None |
| [fin-three-empty-relation-not-reflexive](../formal/nodes/fin-three-empty-relation-not-reflexive.json) | `Lemmatheca.Entry.EquivalenceRelations.empty_relation_not_reflexive` | Proof pending | None |
| [fin-three-le-not-symmetric](../formal/nodes/fin-three-le-not-symmetric.json) | `Lemmatheca.Entry.EquivalenceRelations.le_relation_not_symmetric` | Proof pending | None |
| [fin-three-missing-part-not-partition](../formal/nodes/fin-three-missing-part-not-partition.json) | `Lemmatheca.Entry.EquivalenceRelations.missing_part_not_partition` | Proof pending | [set-partition-covers](../formal/nodes/set-partition-covers.json) |
| [fin-three-overlapping-parts-not-partition](../formal/nodes/fin-three-overlapping-parts-not-partition.json) | `Lemmatheca.Entry.EquivalenceRelations.overlapping_parts_not_partition` | Proof pending | [set-partition-parts-disjoint](../formal/nodes/set-partition-parts-disjoint.json) |
| [fin-three-two-block-classes](../formal/nodes/fin-three-two-block-classes.json) | `Lemmatheca.Entry.EquivalenceRelations.finite_classes` | Proof pending | [fin-three-two-block-relation](../formal/nodes/fin-three-two-block-relation.json) |
| [fin-three-two-block-relation](../formal/nodes/fin-three-two-block-relation.json) | `Lemmatheca.Entry.EquivalenceRelations.finite_relation_iff` | Proof pending | [map-diagram-values](../formal/nodes/map-diagram-values.json) |
| [int-congruence](../formal/nodes/int-congruence.json) | `Int.ModEq` | Library proof complete | None |
| [int-congruence-equivalence](../formal/nodes/int-congruence-equivalence.json) | `Int.ModEq.instIsEquiv` | Library proof complete | None |
| [int-congruence-iff-divides-difference](../formal/nodes/int-congruence-iff-divides-difference.json) | `Int.modEq_iff_dvd` | Library proof complete | None |
| [int-even-or-odd-exclusively](../formal/nodes/int-even-or-odd-exclusively.json) | `Int.even_xor_odd` | Library proof complete | None |
| [int-parity-classes](../formal/nodes/int-parity-classes.json) | `Lemmatheca.Entry.EquivalenceRelations.parity_classes` | Proof pending | [int-congruence-iff-divides-difference](../formal/nodes/int-congruence-iff-divides-difference.json), [int-even-or-odd-exclusively](../formal/nodes/int-even-or-odd-exclusively.json) |
| [int-parity-classes-infinite](../formal/nodes/int-parity-classes-infinite.json) | `Lemmatheca.Entry.EquivalenceRelations.parity_classes_infinite` | Proof pending | None |
| [int-parity-distinct-equivalent](../formal/nodes/int-parity-distinct-equivalent.json) | `Lemmatheca.Entry.EquivalenceRelations.parity_distinct_equivalent` | Proof pending | None |
| [int-parity-identity-not-descend](../formal/nodes/int-parity-identity-not-descend.json) | `Lemmatheca.Entry.EquivalenceRelations.parity_identity_not_descend` | Proof pending | [quotient-projection-equality](../formal/nodes/quotient-projection-equality.json) |
| [int-parity-label-descends](../formal/nodes/int-parity-label-descends.json) | `Lemmatheca.Entry.EquivalenceRelations.parity_label_descends` | Proof pending | [quotient-map-universal-property](../formal/nodes/quotient-map-universal-property.json), [int-parity-classes](../formal/nodes/int-parity-classes.json) |
| [int-parity-successor-descends](../formal/nodes/int-parity-successor-descends.json) | `Lemmatheca.Entry.EquivalenceRelations.parity_successor_descends` | Proof pending | [map-between-quotients](../formal/nodes/map-between-quotients.json), [int-parity-classes](../formal/nodes/int-parity-classes.json) |
| [map-between-quotients](../formal/nodes/map-between-quotients.json) | `Quotient.map` | Library proof complete | None |
| [map-diagram-fiber-p-and-range](../formal/nodes/map-diagram-fiber-p-and-range.json) | `Lemmatheca.Entry.EquivalenceRelations.diagram_fiber_p_and_range` | Proof pending | [map-diagram-values](../formal/nodes/map-diagram-values.json) |
| [map-empty-domain-range](../formal/nodes/map-empty-domain-range.json) | `Set.range_eq_empty` | Library proof complete | None |
| [map-fiber-nonempty-iff-in-range](../formal/nodes/map-fiber-nonempty-iff-in-range.json) | `Set.preimage_singleton_nonempty` | Library proof complete | None |
| [map-injective-iff-kernel-equality](../formal/nodes/map-injective-iff-kernel-equality.json) | `Setoid.injective_iff_ker_bot` | Library proof complete | None |
| [map-kernel-class-fiber](../formal/nodes/map-kernel-class-fiber.json) | `Setoid.ker_iff_mem_preimage` | Library proof complete | None |
| [map-kernel-classes-nonempty-fibers](../formal/nodes/map-kernel-classes-nonempty-fibers.json) | `Lemmatheca.SetTheory.kernel_classes_eq_nonempty_fibers` | Proof pending | [map-kernel-class-fiber](../formal/nodes/map-kernel-class-fiber.json) |
| [map-kernel-lift](../formal/nodes/map-kernel-lift.json) | `Setoid.kerLift` | Library proof complete | None |
| [map-kernel-relation](../formal/nodes/map-kernel-relation.json) | `Setoid.ker` | Library proof complete | None |
| [quotient-class-of-representative](../formal/nodes/quotient-class-of-representative.json) | `Setoid.quotientEquivClasses_mk_eq` | Library proof complete | None |
| [quotient-equivalence-classes](../formal/nodes/quotient-equivalence-classes.json) | `Setoid.quotientEquivClasses` | Library proof complete | None |
| [quotient-image-inverse-fiber](../formal/nodes/quotient-image-inverse-fiber.json) | `Lemmatheca.SetTheory.quotient_image_inverse_fiber` | Proof pending | [quotient-kernel-equiv-range](../formal/nodes/quotient-kernel-equiv-range.json), [map-kernel-class-fiber](../formal/nodes/map-kernel-class-fiber.json) |
| [quotient-kernel-equiv-codomain](../formal/nodes/quotient-kernel-equiv-codomain.json) | `Setoid.quotientKerEquivOfSurjective` | Library proof complete | None |
| [quotient-kernel-equiv-range](../formal/nodes/quotient-kernel-equiv-range.json) | `Setoid.quotientKerEquivRange` | Library proof complete | None |
| [quotient-lift-injective-iff](../formal/nodes/quotient-lift-injective-iff.json) | `Setoid.lift_injective_iff_ker_eq_of_le` | Library proof complete | None |
| [quotient-lift-range](../formal/nodes/quotient-lift-range.json) | `Set.range_quotient_lift` | Library proof complete | None |
| [quotient-lift-surjective-iff](../formal/nodes/quotient-lift-surjective-iff.json) | `Quotient.lift_surjective_iff` | Library proof complete | None |
| [quotient-map-universal-property](../formal/nodes/quotient-map-universal-property.json) | `Setoid.liftEquiv` | Library proof complete | None |
| [quotient-projection](../formal/nodes/quotient-projection.json) | `Quotient.mk` | Library proof complete | None |
| [quotient-projection-equality](../formal/nodes/quotient-projection-equality.json) | `Quotient.eq` | Library proof complete | None |
| [quotient-projection-kernel](../formal/nodes/quotient-projection-kernel.json) | `Setoid.ker_mk_eq` | Library proof complete | None |
| [quotient-projection-surjective](../formal/nodes/quotient-projection-surjective.json) | `Quotient.mk_surjective` | Library proof complete | None |
| [relation-not-symmetric-iff-witness](../formal/nodes/relation-not-symmetric-iff-witness.json) | `Lemmatheca.SetTheory.not_symmetric_iff_witness` | Proof pending | None |
| [relation-reflexive](../formal/nodes/relation-reflexive.json) | `Std.Refl` | Library proof complete | None |
| [relation-symmetric](../formal/nodes/relation-symmetric.json) | `Std.Symm` | Library proof complete | None |
| [relation-transitive](../formal/nodes/relation-transitive.json) | `IsTrans` | Library proof complete | None |
| [set-partition](../formal/nodes/set-partition.json) | `Setoid.IsPartition` | Library proof complete | None |
| [set-partition-covers](../formal/nodes/set-partition-covers.json) | `Setoid.IsPartition.sUnion_eq_univ` | Library proof complete | None |
| [set-partition-parts-disjoint](../formal/nodes/set-partition-parts-disjoint.json) | `Setoid.IsPartition.pairwiseDisjoint` | Library proof complete | None |
| [set-partition-parts-nonempty](../formal/nodes/set-partition-parts-nonempty.json) | `Setoid.nonempty_of_mem_partition` | Library proof complete | None |
| [subtype-inclusion-injective](../formal/nodes/subtype-inclusion-injective.json) | `Subtype.val_injective` | Library proof complete | None |
| [universal-equivalence-relation](../formal/nodes/universal-equivalence-relation.json) | `equivalence_true` | Library proof complete | None |
| [universal-relation-classes](../formal/nodes/universal-relation-classes.json) | `Lemmatheca.SetTheory.universal_relation_classes` | Proof pending | None |

## Why local statements remain

- The symmetry-witness criterion and universal/empty set descriptions have no
  matching direct declaration in the searched quotient/partition API.
- `kernel_classes_eq_nonempty_fibers` identifies the *entire* family of classes
  with exactly the fibers indexed by the range. The existing
  `classes_ker_subset_fiber_set` only gives inclusion in all fibers, which can
  include the empty fiber and therefore does not cover the human equality.
- `quotient_image_inverse_fiber` records the underlying set of the inverse value;
  a bare equivalence signature does not state this explicit inverse formula.
- The fourteen concrete statements record the entry’s witnesses, finite classes,
  integer parity calculations, failed and successful representative rules,
  successor involution, and missing finite-map calculation. Existing map values
  and q/r fibers are reused; only the p fiber and range need a new calculation.
  `adjacent`, `parityLabel`, and the two setoid abbreviations are unregistered
  helpers whose bodies remain part of their targets’ review hashes.

Proof prerequisites are direct planned proof uses, not reading order. The finite
relation and p-fiber/range calculation use the existing diagram values; the finite
classes use the relation characterization. The parity classes use the congruence
criterion and exclusive even/odd alternatives. The two partition counterexamples
use the corresponding necessary partition condition. The representative rules use
quotient equality or the induced-map constructions, with parity classes for their
values. The empty-relation statement uses uniqueness of functions from an empty
domain. The family-of-fibers and inverse-fiber statements use the library kernel
class description and, for the inverse, the range equivalence. Other proofs can
use definitions, elementary logic, finite case analysis, or library results without
adding registry edges.

## Reused nodes

[map-diagram-images-and-preimages](../formal/nodes/map-diagram-images-and-preimages.json), [map-diagram-neither-injective-nor-surjective](../formal/nodes/map-diagram-neither-injective-nor-surjective.json), [map-diagram-values](../formal/nodes/map-diagram-values.json), [map-empty-domain-unique](../formal/nodes/map-empty-domain-unique.json), [map-empty-self-bijective](../formal/nodes/map-empty-self-bijective.json), [map-injective-iff-fibers-subsingleton](../formal/nodes/map-injective-iff-fibers-subsingleton.json), [map-surjective-iff-fibers-nonempty](../formal/nodes/map-surjective-iff-fibers-nonempty.json), [set-empty-ne-singleton](../formal/nodes/set-empty-ne-singleton.json), [set-insert-repeat](../formal/nodes/set-insert-repeat.json), [set-relation-between](../formal/nodes/set-relation-between.json).

## Validation

- `validate_corpus`: two entries and 36 blocks validated.
- `lake build`: aggregate library and entry imports compile; only the expected
  warnings for unfinished new proofs remain.
- `test catalog`: all 59 tests pass.
- `check_formalizations`: 189 declarations checked, 127 ready and 62 awaiting
  review. Of the new targets, 41 have complete Lean evidence and 21 have `sorry`.
- Every new declaration has a checked signature and defining source line.
- The initial binding preparation preserved all 127 existing node files and
  target hashes. A subsequent layout cleanup moved 42 first-entry node modules
  and refreshed their approvals with the maintainer's authorization. The new
  equivalence-relations nodes remain unreviewed. Lean and mathlib pins are
  unchanged. There are no duplicate target declarations or unlinked new nodes.

Proof completion and independent correspondence review are later pipeline steps.
