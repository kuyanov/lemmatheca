import Lemmatheca.SetTheory.SetsAndElements
import Mathlib.Data.Set.Lattice.Indexed
import Mathlib.Data.Set.Prod

/-!
# Subsets, operations, families, and relations

Reviewed declarations and proofs for the sets-and-maps entry.

An ambient type represents the specified universe U; a smaller universe can be
represented by a subtype. Thus `Set.univ` and complements always refer to a
specified type. For the empty-set question, both outer sets have type
`Set (Set α)`, and their possible element `∅` has type `Set α`.
-/

namespace Lemmatheca.SetsAndMaps

universe u v w

variable {α : Type u} {β : Type v} {ι : Type w}

/-- Proper inclusion, with the inequality required by the human definition. -/
def properSubset (A B : Set α) : Prop := A ⊆ B ∧ A ≠ B

theorem subset_reflexive (A : Set α) : A ⊆ A := by
  intro x hx
  exact hx

theorem set_extensionality (A B : Set α) : A = B ↔ ∀ x, x ∈ A ↔ x ∈ B := by
  constructor
  · intro h x
    rw [h]
  · intro h
    exact Set.ext h

theorem membership_and_inclusion_example :
    2 ∈ ({2, 5} : Set ℕ) ∧ ({2} : Set ℕ) ⊆ {2, 5} := by
  simp

theorem naturals_below_three : {n : ℕ | n < 3} = {0, 1, 2} := by
  apply (set_extensionality _ _).mpr
  intro n
  simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  omega

theorem empty_subset (A : Set α) : ∅ ⊆ A := by
  intro x hx
  exact hx.elim

theorem empty_quantifiers (P : α → Prop) :
    (∀ x ∈ (∅ : Set α), P x) ∧ ¬ (∃ x ∈ (∅ : Set α), P x) := by
  constructor
  · intro x hx
    exact hx.elim
  · rintro ⟨x, hx, _⟩
    exact hx

theorem equality_iff_two_inclusions (A B : Set α) :
    A = B ↔ A ⊆ B ∧ B ⊆ A := by
  constructor
  · intro h
    subst B
    exact ⟨fun _ hx => hx, fun _ hx => hx⟩
  · rintro ⟨hAB, hBA⟩
    apply (set_extensionality A B).mpr
    intro x
    exact ⟨fun hx => hAB hx, fun hx => hBA hx⟩

theorem subset_transitive (A B C : Set α) (hAB : A ⊆ B) (hBC : B ⊆ C) : A ⊆ C := by
  intro x hx
  exact hBC (hAB hx)

theorem empty_or_singleton_answer :
    (∅ : Set (Set α)) ≠ {∅} ∧
      (∅ : Set α) ∈ ({∅} : Set (Set α)) ∧
      (∅ : Set (Set α)) ⊆ {∅} := by
  refine ⟨?_, rfl, empty_subset _⟩
  intro h
  have hm : (∅ : Set α) ∈ ({∅} : Set (Set α)) := rfl
  rw [← h] at hm
  exact hm

/-- Disjointness expressed by the intersection condition used in the entry. -/
def setsDisjoint (A B : Set α) : Prop := A ∩ B = ∅

theorem set_operations_example :
    ({0, 2} : Set ℕ) ∪ {2, 3} = {0, 2, 3} ∧
      ({0, 2} : Set ℕ) ∩ {2, 3} = {2} ∧
      ({0, 2} : Set ℕ) \ {2, 3} = {0} ∧
      ({0, 1, 2, 3, 4} : Set ℕ) \ {0, 2} = {1, 3, 4} := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ext n <;>
    simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_sdiff,
      Set.mem_insert_iff, Set.mem_singleton_iff] <;> omega

theorem complement_depends_on_universe :
    (∀ n : ℕ, 5 ≤ n → n ∈ ({0, 2} : Set ℕ)ᶜ) ∧
      5 ∉ (({0, 1, 2, 3, 4} : Set ℕ) \ {0, 2}) := by
  constructor
  · intro n hn
    change ¬ (n = 0 ∨ n = 2)
    omega
  · simp

theorem disjoint_sets_example : setsDisjoint ({0, 2} : Set ℕ) {1, 3} := by
  unfold setsDisjoint
  ext n
  change ((n = 0 ∨ n = 2) ∧ (n = 1 ∨ n = 3)) ↔ False
  simp only [iff_false]
  rintro ⟨hA | hA, hB | hB⟩ <;> omega

theorem intersection_distributes_over_union (A B C : Set α) :
    A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) := by
  apply (equality_iff_two_inclusions _ _).mpr
  constructor
  · rintro x ⟨hA, hB | hC⟩
    · exact Or.inl ⟨hA, hB⟩
    · exact Or.inr ⟨hA, hC⟩
  · rintro x (⟨hA, hB⟩ | ⟨hA, hC⟩)
    · exact ⟨hA, Or.inl hB⟩
    · exact ⟨hA, Or.inr hC⟩

theorem complement_union (A B : Set α) : (A ∪ B)ᶜ = Aᶜ ∩ Bᶜ := by
  apply (set_extensionality _ _).mpr
  intro x
  constructor
  · intro h
    exact ⟨fun hA => h (Or.inl hA), fun hB => h (Or.inr hB)⟩
  · rintro ⟨hA, hB⟩ (hxA | hxB)
    · exact hA hxA
    · exact hB hxB

theorem complement_intersection (A B : Set α) : (A ∩ B)ᶜ = Aᶜ ∪ Bᶜ := by
  classical
  apply (set_extensionality _ _).mpr
  intro x
  constructor
  · intro h
    by_cases hA : x ∈ A
    · exact Or.inr (fun hB => h ⟨hA, hB⟩)
    · exact Or.inl hA
  · rintro (hA | hB) ⟨hxA, hxB⟩
    · exact hA hxA
    · exact hB hxB

theorem union_commutative (A B : Set α) : A ∪ B = B ∪ A := by
  apply (set_extensionality _ _).mpr
  intro x
  exact or_comm

theorem intersection_commutative (A B : Set α) : A ∩ B = B ∩ A := by
  apply (set_extensionality _ _).mpr
  intro x
  exact and_comm

theorem union_empty (A : Set α) : A ∪ ∅ = A := by
  apply (set_extensionality _ _).mpr
  intro x
  constructor
  · rintro (hx | hx)
    · exact hx
    · exact hx.elim
  · exact Or.inl

theorem intersection_empty (A : Set α) : A ∩ ∅ = ∅ := by
  apply (set_extensionality _ _).mpr
  intro x
  constructor
  · exact fun hx => hx.2
  · intro hx
    exact hx.elim

theorem powerset_pair_example :
    Set.powerset ({0, 1} : Set ℕ) = {∅, {0}, {1}, {0, 1}} ∧
      (Set.powerset ({0, 1} : Set ℕ)).ncard = 4 ∧
      ({0} : Set ℕ) ∈ Set.powerset ({0, 1} : Set ℕ) := by
  -- A subset of the pair is empty, one of the singletons, or the whole pair.
  have hP : Set.powerset ({0, 1} : Set ℕ) = {∅, {0}, {1}, {0, 1}} := by
    apply (set_extensionality _ _).mpr
    intro S
    change S ⊆ ({0, 1} : Set ℕ) ↔ S = ∅ ∨ S = {0} ∨ S = {1} ∨ S = {0, 1}
    exact Set.subset_pair_iff_eq
  refine ⟨hP, ?_, ?_⟩
  · norm_num
  · intro n hn
    exact Or.inl hn

theorem powerset_contains_empty_and_self (A : Set α) :
    ∅ ∈ Set.powerset A ∧ A ∈ Set.powerset A := by
  exact ⟨empty_subset A, subset_reflexive A⟩

theorem powerset_empty : Set.powerset (∅ : Set α) = {∅} := by
  apply (set_extensionality _ _).mpr
  intro S
  change S ⊆ ∅ ↔ S = ∅
  constructor
  · intro hS
    exact (equality_iff_two_inclusions S ∅).mpr ⟨hS, fun _ hx => hx.elim⟩
  · intro hS
    subst S
    exact fun _ hx => hx

theorem indexed_union_membership (A : ι → Set α) (x : α) :
    x ∈ (⋃ i, A i) ↔ ∃ i, x ∈ A i := by
  exact Set.mem_iUnion

theorem indexed_intersection_membership (A : ι → Set α) (x : α) :
    x ∈ (⋂ i, A i) ↔ ∀ i, x ∈ A i := by
  exact Set.mem_iInter

theorem initial_segments_union : (⋃ n : ℕ, {k : ℕ | k ≤ n}) = Set.univ := by
  apply (set_extensionality _ _).mpr
  intro k
  constructor
  · intro _
    trivial
  · intro _
    exact (indexed_union_membership _ k).mpr ⟨k, show k ≤ k from le_rfl⟩

theorem initial_segments_intersection : (⋂ n : ℕ, {k : ℕ | k ≤ n}) = {0} := by
  apply (set_extensionality _ _).mpr
  intro k
  rw [indexed_intersection_membership]
  change (∀ n : ℕ, k ≤ n) ↔ k = 0
  constructor
  · intro h
    exact Nat.eq_zero_of_le_zero (h 0)
  · rintro rfl n
    exact Nat.zero_le n

theorem empty_family_union [IsEmpty ι] (A : ι → Set α) : (⋃ i, A i) = ∅ := by
  apply (set_extensionality _ _).mpr
  intro x
  rw [indexed_union_membership]
  constructor
  · rintro ⟨i, _⟩
    exact isEmptyElim i
  · intro hx
    exact hx.elim

theorem empty_family_intersection [IsEmpty ι] (A : ι → Set α) :
    (⋂ i, A i) = Set.univ := by
  apply (set_extensionality _ _).mpr
  intro x
  rw [indexed_intersection_membership]
  constructor
  · intro _
    trivial
  · intro _ i
    exact isEmptyElim i

theorem ordered_pair_equality (a a' : α) (b b' : β) :
    (a, b) = (a', b') ↔ a = a' ∧ b = b' := by
  constructor
  · intro h
    exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem pairs_and_sets_example :
    ((0, 1) : ℕ × ℕ) ≠ (1, 0) ∧ ({0, 1} : Set ℕ) = {1, 0} := by
  constructor
  · intro h
    have hfirst := (ordered_pair_equality _ _ _ _).mp h
    omega
  · simpa using (insert_order (α := ℕ) 0 1 ∅)

theorem cartesian_product_example (p q : β) :
    ({0, 1} : Set ℕ) ×ˢ ({p, q} : Set β) = {(0, p), (0, q), (1, p), (1, q)} := by
  ext ⟨a, b⟩
  simp only [Set.mem_prod, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
  constructor
  · rintro ⟨(rfl | rfl), (rfl | rfl)⟩ <;> simp
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> simp

theorem empty_cartesian_products (A : Set α) (B : Set β) :
    (∅ : Set α) ×ˢ B = ∅ ∧ A ×ˢ (∅ : Set β) = ∅ := by
  constructor <;> ext ⟨a, b⟩ <;> simp

/-- A relation between specified sets, with its containment recorded in the type. -/
def RelationBetween (A : Set α) (B : Set β) := {R : Set (α × β) // R ⊆ A ×ˢ B}

theorem less_than_relation_example :
    {z : ℕ × ℕ | z.1 ∈ ({0, 1, 2} : Set ℕ) ∧
      z.2 ∈ ({0, 1, 2} : Set ℕ) ∧ z.1 < z.2} = {(0, 1), (0, 2), (1, 2)} := by
  ext ⟨a, b⟩
  simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
  omega

end Lemmatheca.SetsAndMaps
