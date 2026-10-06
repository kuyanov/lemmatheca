import Lemmatheca.SetTheory.RealMaps
import Lemmatheca.SetTheory.Basic

/-! Particular examples and counterexamples for the human entry. -/

namespace Lemmatheca.Entry.SetsAndMaps
open Lemmatheca.SetTheory Lemmatheca.SetTheory.RealMaps

section SetsAndElements

/-- The concrete set {2, 5, 8} in the human text has three elements. -/
theorem three_element_example_card : ({2, 5, 8} : Set ℕ).ncard = 3 := by
  norm_num

end SetsAndElements

section SetOperations

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

end SetOperations

section Maps

theorem equal_real_formulas :
    (fun x : ℝ => 2 * (x + 1)) = (fun x : ℝ => 2 * x + 2) := by
  apply funext_iff.mpr
  intro x
  ring

/-- The three distinct labels in the diagram's codomain. -/
inductive MapLabel where
  | p | q | r
  deriving DecidableEq

/-- The displayed map: 0 goes to p, and 1 and 2 go to q. -/
def diagramMap (x : Fin 3) : MapLabel := if x = 0 then .p else .q

theorem diagram_map_values :
    diagramMap 0 = .p ∧ diagramMap 1 = .q ∧ diagramMap 2 = .q := by
  simp [diagramMap]

theorem diagram_map_graph :
    Set.graphOn diagramMap Set.univ = {(0, .p), (1, .q), (2, .q)} := by
  ext ⟨x, y⟩
  fin_cases x <;> cases y <;> simp [diagramMap]

theorem four_has_two_square_roots :
    (2 : ℝ) ^ 2 = 4 ∧ (-2 : ℝ) ^ 2 = 4 ∧ (2 : ℝ) ≠ -2 := by
  norm_num

theorem composition_order_example :
    (∀ x : ℝ, ((fun y => 2 * y) ∘ (fun y => y + 1)) x = 2 * x + 2) ∧
      (∀ x : ℝ, ((fun y => y + 1) ∘ (fun y => 2 * y)) x = 2 * x + 1) ∧
      ((fun y : ℝ => 2 * y) ∘ (fun y => y + 1)) ≠
        ((fun y : ℝ => y + 1) ∘ (fun y => 2 * y)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x
    dsimp
    ring
  · intro x
    rfl
  · intro h
    have hzero := congrFun h 0
    norm_num at hzero

theorem diagram_images_and_preimages :
    diagramMap '' {1, 2} = {.q} ∧
      diagramMap ⁻¹' {.q} = {1, 2} ∧ diagramMap ⁻¹' {.r} = ∅ := by
  refine ⟨?_, ?_, ?_⟩
  · simp [diagramMap]
  · ext x
    fin_cases x <;> simp [diagramMap]
  · ext x
    fin_cases x <;> simp [diagramMap]

theorem image_intersection_counterexample :
    ({1} : Set (Fin 3)) ∩ {2} = ∅ ∧
      diagramMap '' (({1} : Set (Fin 3)) ∩ {2}) = ∅ ∧
      diagramMap '' {1} = {.q} ∧ diagramMap '' {2} = {.q} ∧
      (diagramMap '' {1}) ∩ (diagramMap '' {2}) = {.q} ∧
      diagramMap '' (({1} : Set (Fin 3)) ∩ {2}) ≠
        (diagramMap '' {1}) ∩ (diagramMap '' {2}) := by
  have hdisjoint : ({1} : Set (Fin 3)) ∩ {2} = ∅ := by
    ext x
    fin_cases x <;> simp
  simp [hdisjoint, diagramMap]

theorem diagram_map_neither_injective_nor_surjective :
    ¬ Function.Injective diagramMap ∧ ¬ Function.Surjective diagramMap := by
  constructor
  · intro h
    have hinputs := h (show diagramMap 1 = diagramMap 2 by decide)
    norm_num at hinputs
  · intro h
    obtain ⟨x, hx⟩ := h .r
    fin_cases x <;> simp [diagramMap] at hx

theorem real_translation_bijective :
    Function.Bijective (fun x : ℝ => x + 1) ∧
      ∀ y : ℝ, (y - 1) + 1 = y ∧ ∀ x : ℝ, x + 1 = y → x = y - 1 := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro a b h
    linarith
  · intro y
    refine ⟨y - 1, ?_⟩
    ring
  · intro y
    constructor
    · ring
    · intro x h
      linarith

/-- Range equality expresses surjectivity onto the nonnegative reals. -/
theorem square_map_codomain_example :
    ¬ Function.Surjective (fun x : ℝ => x ^ 2) ∧
      Set.range (fun x : ℝ => x ^ 2) = {y : ℝ | 0 ≤ y} ∧
      ¬ Function.Injective (fun x : ℝ => x ^ 2) ∧
      (1 : ℝ) ^ 2 = (-1 : ℝ) ^ 2 ∧ (1 : ℝ) ≠ -1 := by
  refine ⟨?_, ?_, ?_, by norm_num, by norm_num⟩
  · intro h
    exact (negative_has_no_square_root (-1) (by norm_num)) (h (-1))
  · ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact sq_nonneg x
    · intro hy
      obtain ⟨x, hx, _⟩ := nonnegative_square_root_unique ⟨y, hy⟩
      exact ⟨x.val, hx⟩
  · intro h
    have hinputs := h (show (1 : ℝ) ^ 2 = (-1 : ℝ) ^ 2 by norm_num)
    norm_num at hinputs

theorem preimage_image_strict_example :
    ({1} : Set (Fin 3)) ⊂ diagramMap ⁻¹' (diagramMap '' {1}) := by
  apply Set.ssubset_iff_subset_ne.mpr
  rw [Set.image_singleton, diagram_map_values.2.1, diagram_images_and_preimages.2.1]
  constructor
  · intro x hx
    exact Or.inl hx
  · intro h
    have htwo : (2 : Fin 3) ∈ ({1} : Set (Fin 3)) := by rw [h]; simp
    norm_num at htwo

theorem one_sided_inverse_counterexample :
    Nat.pred ∘ Nat.succ = id ∧ Nat.succ (Nat.pred 0) = 1 ∧
      Nat.succ (Nat.pred 0) ≠ 0 ∧ Nat.succ ∘ Nat.pred ≠ id ∧
      ¬ ∃ g : ℕ → ℕ, Function.LeftInverse g Nat.succ ∧
        Function.RightInverse g Nat.succ := by
  refine ⟨?_, rfl, by decide, ?_, ?_⟩
  · funext n
    exact Nat.pred_succ n
  · intro h
    have hzero := congrFun h 0
    norm_num at hzero
  · intro h
    obtain ⟨g, _, hg⟩ := h
    exact Nat.succ_ne_zero (g 0) (hg 0)

end Maps

end Lemmatheca.Entry.SetsAndMaps
