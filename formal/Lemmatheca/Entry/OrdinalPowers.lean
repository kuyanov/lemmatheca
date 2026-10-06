import Lemmatheca.SetTheory.OrdinalPowers

/-! Particular examples and counterexamples for the human entry. -/

namespace Lemmatheca.Entry.OrdinalPowers
open Lemmatheca.SetTheory.OrdinalPowers
open Ordinal Order Set
open scoped Ordinal
universe u

theorem normalForm_example :
    CNF ω (ω ^ (2 : Ordinal.{u}) + ω + ω + 5) = [(2, 1), (1, 2), (0, 5)] ∧
    ω ^ (2 : Ordinal.{u}) + ω + ω + 5 < ω ^ (2 : Ordinal.{u}) * 2 := by
  have hv : IsNormalForm ([(2, 1), (1, 2), (0, 5)] : List (Ordinal.{u} × Ordinal.{u})) := by
    norm_num [IsNormalForm, List.pairwise_cons]; exact ⟨natCast_lt_omega0 2, natCast_lt_omega0 5⟩
  constructor
  · simpa [evalNormalForm, Ordinal.mul_two, add_assoc] using cnf_eval_normalForm _ hv
  · have ht := finite_sum_lt_power (2 : Ordinal.{u}) (by norm_num)
      [(1, 2), (0, 5)] (by simp)
    have ht' : ω * 2 + (5 : Ordinal.{u}) < ω ^ (2 : Ordinal.{u}) := by
      simpa using ht
    simpa [Ordinal.mul_two, add_assoc] using
      (opow_mul_add_lt_opow_mul (b := ω) (u := (2 : Ordinal.{u})) ht'
        (show (1 : Ordinal.{u}) < 2 by norm_num))

theorem absorption_example :
    (ω ^ (2 : Ordinal.{u}) + ω * 3 + 7) + ω ^ (2 : Ordinal.{u}) =
      ω ^ (2 : Ordinal.{u}) * 2 := by
  have ht := finite_sum_lt_power (2 : Ordinal.{u}) (by norm_num)
    [(1, 3), (0, 7)] (by simp)
  have ht' : ω * 3 + (7 : Ordinal.{u}) < ω ^ (2 : Ordinal.{u}) := by simpa using ht
  calc
    _ = ω ^ (2 : Ordinal.{u}) + ((ω * 3 + 7) + ω ^ (2 : Ordinal.{u})) := by simp only [add_assoc]
    _ = ω ^ (2 : Ordinal.{u}) + ω ^ (2 : Ordinal.{u}) := by rw [Ordinal.add_omega0_opow ht']
    _ = _ := (Ordinal.mul_two _).symm

end Lemmatheca.Entry.OrdinalPowers
