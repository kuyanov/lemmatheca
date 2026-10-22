import Lemmatheca.TypesAndRealization.Types
import Mathlib.ModelTheory.Encoding
import Mathlib.SetTheory.Cardinal.Continuum

/-! Counting finite-context complete types in an arbitrary countable language. -/
namespace Lemmatheca.ModelTheory.NamedRationalOrder

open FirstOrder FirstOrder.Language
open Types

/-- The formula presentation injects complete types into subsets of the formula set. -/
theorem formula_presentation_injective {L : Language.{0, 0}} (U : L.Theory) (n : ℕ) :
    Function.Injective (fun p : U.CompleteType (Fin n) => formulas p) := by
  intro p q hp
  apply SetLike.ext'
  change p.toTheory = q.toTheory
  apply Set.ext
  intro γ
  have h := Set.ext_iff.mp hp (Formula.equivSentence.symm γ)
  change Formula.equivSentence (Formula.equivSentence.symm γ) ∈ p.toTheory ↔
    Formula.equivSentence (Formula.equivSentence.symm γ) ∈ q.toTheory at h
  simpa only [Equiv.apply_symm_apply] using h

/-- The bound requires neither completeness nor satisfiability of the theory. -/
theorem complete_types_cardinal_le_continuum {L : Language.{0, 0}}
    [Countable L.Symbols] (U : L.Theory) (n : ℕ) :
    Cardinal.mk (U.CompleteType (Fin n)) ≤ 2 ^ Cardinal.aleph0 := by
  calc
    Cardinal.mk (U.CompleteType (Fin n)) ≤ Cardinal.mk (Set (L.Formula (Fin n))) :=
      Cardinal.mk_le_of_injective (formula_presentation_injective U n)
    _ = 2 ^ Cardinal.mk (L.Formula (Fin n)) := Cardinal.mk_set
    _ ≤ 2 ^ Cardinal.aleph0 :=
      Cardinal.power_le_power_left (by simp) Cardinal.mk_le_aleph0

end Lemmatheca.ModelTheory.NamedRationalOrder
