import Lemmatheca.FiniteMindChanges.BooleanExpressions

/-! Initial-bit and non-optimal-budget examples. -/
namespace Lemmatheca.Entry.FiniteMindChanges

open ComputabilityTheory.UniversalComputation ComputabilityTheory.LimitComputability
  ComputabilityTheory.DifferenceEnumerable ComputabilityTheory.FiniteMindChanges

def evenApproximation (_s x : ℕ) : ℕ := 1 - x % 2

theorem even_zero_change_data :
    Computable₂ evenApproximation ∧ Binary evenApproximation ∧
      Converges evenApproximation {x | x % 2 = 0} ∧ AtMostChanges evenApproximation 0 ∧
      ¬ StartsZero evenApproximation := by
  classical
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact Primrec.nat_sub.to_comp.comp (Computable.const 1)
      (Primrec.nat_mod.to_comp.comp Computable.snd (Computable.const 2))
  · intro s x
    have hm := Nat.mod_lt x (by decide : 0 < 2)
    change 1 - x % 2 = 0 ∨ 1 - x % 2 = 1
    omega
  · intro x
    refine ⟨0, fun s _hs => ?_⟩
    simp only [evenApproximation, indicator, Set.ofPred]
    have hm := Nat.mod_lt x (by decide : 0 < 2)
    split_ifs <;> omega
  · intro s x
    induction s with
    | zero => rfl
    | succ s ih => simpa [changeCount, evenApproximation] using ih
  · intro hz
    have h := hz 0
    norm_num [evenApproximation] at h

def differenceUnionExpression : BooleanExpression :=
  .union (.inter (.atom 0) (.compl (.atom 1))) (.atom 2)

theorem difference_union_budget (U : ℕ → Set ℕ) :
    differenceUnionExpression.budget = 4 ∧
      differenceUnionExpression.eval U = (U 0 \ U 1) ∪ U 2 := by
  refine ⟨rfl, ?_⟩
  ext x
  simp [differenceUnionExpression, BooleanExpression.eval, Set.sdiff_eq]

theorem difference_union_improved (U V R : Set ℕ) (hu : REPred U) (hv : REPred V)
    (hr : REPred R) : NCE 3 ((U \ V) ∪ R) := by
  have hd : IsDifferenceEnumerable (U \ V) := ⟨U, V, hu, hv, rfl⟩
  have htwo : NCE 2 (U \ V) := (difference_iff_two_change (U \ V)).mp hd
  have hone : NCE 1 R := (enumerable_iff_one_change R).mp hr
  exact (nce_combination 2 1 (U \ V) R htwo hone).1

def duplicateExpression : BooleanExpression := .union (.atom 0) (.atom 0)

theorem duplicate_budget (U : ℕ → Set ℕ) (hu : REPred (U 0)) :
    duplicateExpression.budget = 2 ∧ duplicateExpression.eval U = U 0 ∧
      NCE 1 (duplicateExpression.eval U) := by
  have he : duplicateExpression.eval U = U 0 := by
    simp [duplicateExpression, BooleanExpression.eval]
  exact ⟨rfl, he, he.symm ▸ (enumerable_iff_one_change (U 0)).mp hu⟩

theorem duplicate_empty_zero (U : ℕ → Set ℕ) (hu : U 0 = ∅) :
    NCE 0 (duplicateExpression.eval U) := by
  apply (nce_zero_iff _).mpr
  simp [duplicateExpression, BooleanExpression.eval, hu]

end Lemmatheca.Entry.FiniteMindChanges
