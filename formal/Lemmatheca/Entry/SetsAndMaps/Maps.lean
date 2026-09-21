import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Set.Prod
import Mathlib.Tactic.Choose
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Sets-and-maps entry: map examples and question answers

The diagram uses `Fin 3` for {0, 1, 2} and `MapLabel` for {p, q, r}.
Standard map laws are imported directly from mathlib.

Lean's real division is total, with 1 / 0 = 0. The formula question therefore
uses the relation x * y = 1 to express the required reciprocal. Square roots
are specified by their relation and the required nonnegative domain and codomain.
-/

namespace Lemmatheca.Entry.SetsAndMaps

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

theorem reciprocal_at_zero_impossible : ¬ ∃ y : ℝ, (0 : ℝ) * y = 1 := by
  simp

/-- The reciprocal with the nonzero domain required in the answer. -/
noncomputable def reciprocalNonzero (x : {x : ℝ // x ≠ 0}) : ℝ := 1 / x.val

theorem reciprocal_nonzero_unique (x : {x : ℝ // x ≠ 0}) :
    x.val * reciprocalNonzero x = 1 ∧ ∃! y : ℝ, x.val * y = 1 := by
  have hmul : x.val * reciprocalNonzero x = 1 := by
    simpa [reciprocalNonzero, one_div] using mul_inv_cancel₀ x.property
  refine ⟨hmul, reciprocalNonzero x, hmul, ?_⟩
  intro y hy
  apply mul_left_cancel₀ x.property
  exact hy.trans hmul.symm

theorem negative_has_no_square_root (x : ℝ) (hx : x < 0) :
    ¬ ∃ y : ℝ, y ^ 2 = x := by
  rintro ⟨y, hy⟩
  nlinarith [sq_nonneg y]

theorem positive_has_two_square_roots (x : ℝ) (hx : 0 < x) :
    ∃ y z : ℝ, y ≠ z ∧ ∀ t : ℝ, t ^ 2 = x ↔ t = y ∨ t = z := by
  have hs := Real.sq_sqrt hx.le
  refine ⟨Real.sqrt x, -Real.sqrt x, ?_, ?_⟩
  · have hpos := Real.sqrt_pos.mpr hx
    linarith
  · intro t
    constructor
    · intro ht
      have hprod : (t - Real.sqrt x) * (t + Real.sqrt x) = 0 := by nlinarith
      rcases mul_eq_zero.mp hprod with h | h
      · left
        linarith
      · right
        linarith
    · rintro (rfl | rfl) <;> nlinarith

theorem four_has_two_square_roots :
    (2 : ℝ) ^ 2 = 4 ∧ (-2 : ℝ) ^ 2 = 4 ∧ (2 : ℝ) ≠ -2 := by
  norm_num

theorem nonnegative_square_root_unique (x : {x : ℝ // 0 ≤ x}) :
    ∃! y : {y : ℝ // 0 ≤ y}, y.val ^ 2 = x.val := by
  refine ⟨⟨Real.sqrt x.val, Real.sqrt_nonneg _⟩, Real.sq_sqrt x.property, ?_⟩
  intro y hy
  apply Subtype.ext
  have hy0 := y.property
  have hs0 := Real.sqrt_nonneg x.val
  have hs := Real.sq_sqrt x.property
  dsimp at *
  nlinarith

theorem nonnegative_square_root_map_exists :
    ∃ g : {x : ℝ // 0 ≤ x} → {y : ℝ // 0 ≤ y}, ∀ x, (g x).val ^ 2 = x.val := by
  classical
  choose g hg using fun x => (nonnegative_square_root_unique x).exists
  exact ⟨g, hg⟩

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

end Lemmatheca.Entry.SetsAndMaps
