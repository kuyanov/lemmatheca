import Lemmatheca.SetTheory.NumberSystems

/-! Particular examples and counterexamples for the human entry. -/

set_option autoImplicit false

namespace Lemmatheca.Entry.ConstructingNumberSystems
open Lemmatheca.SetTheory.NumberSystems
open Set
universe u

theorem zero_denominator_failure :
    let R := fun p q : ℤ × ℤ => p.1 * q.2 = q.1 * p.2
    R (0, 1) (0, 0) ∧ R (0, 0) (1, 1) ∧ ¬ R (0, 1) (1, 1) ∧
      ¬ (∀ p q r, R p q → R q r → R p r) := by
  dsimp
  refine ⟨by norm_num,by norm_num,by norm_num,?_⟩
  intro h
  have he := h (0,1) (0,0) (1,1) (by norm_num) (by norm_num)
  norm_num at he

def sqrtTwoLower : Set ℚ := {q | q < 0 ∨ q ^ 2 < 2}

private theorem sqrtTwo_realLower : sqrtTwoLower = realLower (Real.sqrt 2) := by
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hs2 : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
  ext q
  change (q < 0 ∨ q^2 < 2) ↔ (q:ℝ) < Real.sqrt 2
  constructor
  · rintro (hq | hq)
    · exact (by exact_mod_cast hq : (q:ℝ)<0).trans hs
    · have hq' : (q:ℝ)^2<2 := by exact_mod_cast hq
      nlinarith
  · intro hq
    by_cases hn : q<0
    · exact Or.inl hn
    · have hn' : 0≤(q:ℝ) := by exact_mod_cast le_of_not_gt hn
      have : (q:ℝ)^2<2 := by nlinarith
      exact Or.inr (by exact_mod_cast this)

theorem sqrtTwo_isCut : IsCut sqrtTwoLower := by
  rw [sqrtTwo_realLower]
  exact realLower_isCut _

theorem sqrtTwo_not_rational : ∀ q : ℚ, sqrtTwoLower ≠ rationalLower q := by
  intro q h
  rw [sqrtTwo_realLower,← realLower_rat] at h
  exact irrational_sqrt_two.ne_rat q (realLower_injective h)

theorem sqrtTwo_improvement (q : ℚ) (hq : 0 ≤ q) (hq2 : q ^ 2 < 2) :
    q < (2 * q + 2) / (q + 2) ∧ ((2 * q + 2) / (q + 2)) ^ 2 < 2 := by
  have hd : 0 < q+2 := by linarith
  constructor
  · rw [lt_div_iff₀ hd]
    nlinarith
  · rw [div_pow,div_lt_iff₀ (sq_pos_of_pos hd)]
    nlinarith [sq_nonneg q]

end Lemmatheca.Entry.ConstructingNumberSystems
