import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Disjoint
import Mathlib.Data.Set.Prod
import Mathlib.Tactic.NormNum

/-!
# Sets-and-maps entry: set operations and relations

Concrete set operations, families, and relation examples from the entry.
Standard set laws are imported directly from mathlib.
-/

namespace Lemmatheca.Entry.SetsAndMaps

universe v

variable {β : Type v}

theorem membership_and_inclusion_example :
    2 ∈ ({2, 5} : Set ℕ) ∧ ({2} : Set ℕ) ⊆ {2, 5} := by
  simp

theorem naturals_below_three : {n : ℕ | n < 3} = {0, 1, 2} := by
  apply Set.ext_iff.mpr
  intro n
  simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  omega

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

theorem disjoint_sets_example : Disjoint ({0, 2} : Set ℕ) {1, 3} := by
  apply Set.disjoint_iff_inter_eq_empty.mpr
  ext n
  change ((n = 0 ∨ n = 2) ∧ (n = 1 ∨ n = 3)) ↔ False
  simp only [iff_false]
  rintro ⟨hA | hA, hB | hB⟩ <;> omega

theorem powerset_pair_example :
    Set.powerset ({0, 1} : Set ℕ) = {∅, {0}, {1}, {0, 1}} ∧
      (Set.powerset ({0, 1} : Set ℕ)).ncard = 4 ∧
      ({0} : Set ℕ) ∈ Set.powerset ({0, 1} : Set ℕ) := by
  -- A subset of the pair is empty, one of the singletons, or the whole pair.
  have hP : Set.powerset ({0, 1} : Set ℕ) = {∅, {0}, {1}, {0, 1}} := by
    apply Set.ext_iff.mpr
    intro S
    change S ⊆ ({0, 1} : Set ℕ) ↔ S = ∅ ∨ S = {0} ∨ S = {1} ∨ S = {0, 1}
    exact Set.subset_pair_iff_eq
  refine ⟨hP, ?_, ?_⟩
  · norm_num
  · intro n hn
    exact Or.inl hn

theorem initial_segments_intersection : (⋂ n : ℕ, {k : ℕ | k ≤ n}) = {0} := by
  apply Set.ext_iff.mpr
  intro k
  rw [Set.mem_iInter]
  change (∀ n : ℕ, k ≤ n) ↔ k = 0
  constructor
  · intro h
    exact Nat.eq_zero_of_le_zero (h 0)
  · rintro rfl n
    exact Nat.zero_le n

theorem pairs_and_sets_example :
    ((0, 1) : ℕ × ℕ) ≠ (1, 0) ∧ ({0, 1} : Set ℕ) = {1, 0} := by
  constructor
  · intro h
    have hfirst := Prod.ext_iff.mp h
    omega
  · simpa using (Set.insert_comm (α := ℕ) 0 1 ∅)

theorem cartesian_product_example (p q : β) :
    ({0, 1} : Set ℕ) ×ˢ ({p, q} : Set β) = {(0, p), (0, q), (1, p), (1, q)} := by
  ext ⟨a, b⟩
  simp only [Set.mem_prod, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
  constructor
  · rintro ⟨(rfl | rfl), (rfl | rfl)⟩ <;> simp
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> simp

theorem less_than_relation_example :
    {z : ℕ × ℕ | z.1 ∈ ({0, 1, 2} : Set ℕ) ∧
      z.2 ∈ ({0, 1, 2} : Set ℕ) ∧ z.1 < z.2} = {(0, 1), (0, 2), (1, 2)} := by
  ext ⟨a, b⟩
  simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
  omega

end Lemmatheca.Entry.SetsAndMaps
