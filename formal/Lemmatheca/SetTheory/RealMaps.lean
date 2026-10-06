import Mathlib.Data.Set.Card
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FinCases

/-! Reusable RealMaps definitions and results. -/

/-! Real reciprocal and square-root relations. Division is total in Lean;
nonzero inputs are recorded in the reciprocal's domain, and square roots
are specified with their nonnegative domain and codomain. -/

namespace Lemmatheca.SetTheory.RealMaps
open Lemmatheca.SetTheory

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


end Lemmatheca.SetTheory.RealMaps
