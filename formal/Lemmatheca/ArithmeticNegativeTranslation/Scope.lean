import Lemmatheca.HeytingArithmetic.Axioms
import Lemmatheca.FirstOrderNegativeTranslation.Syntax

namespace Lemmatheca.ProofTheory.HeytingArithmetic.NegativeTranslation
open _root_.FirstOrder _root_.FirstOrder.Language
open Lemmatheca.ProofTheory.FirstOrder.NegativeTranslation (negative context)
open Lemmatheca.ProofTheory.FirstOrder.NegativeTranslation (negative_map negative_subst)
open Lemmatheca.ProofTheory.FirstOrder.BoundedFormula
universe u v
variable {α : Type u}
noncomputable section
local instance arithmeticNegativeScopeFormulaEq {β : Type*} : DecidableEq (Formula β) := Classical.decEq _

theorem negative_bindUnit (A : Formula (α ⊕ Unit)) :
    negative (bindUnit A) = bindUnit (negative A) := by
  exact negative_map A _

theorem negative_allUnit (A : Formula (α ⊕ Unit)) :
    negative (allUnit A) = allUnit (negative A) := by
  unfold allUnit
  simp only [negative, negative_bindUnit]

theorem negative_allSlots {n} (A : BF α n) :
    negative (allSlots A) = allSlots (negative A) := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih (.all A)

theorem negative_close {k} (A : Formula (Fin k)) :
    negative (close A) = close (negative A) := by
  unfold close
  rw [negative_allSlots, negative_map]

theorem negative_base {k} (A : Formula (Fin k ⊕ Unit)) :
    negative (base A) = base (negative A) := by
  exact negative_subst A _

theorem negative_next {k} (A : Formula (Fin k ⊕ Unit)) :
    negative (next A) = next (negative A) := by
  exact negative_subst A _

/-- All finite parameters and the full native body are retained literally. -/
theorem negative_inductionAxiom {k} (A : Formula (Fin k ⊕ Unit)) :
    negative (inductionAxiom A) = inductionAxiom (negative A) := by
  unfold inductionAxiom
  rw [negative_close]
  simp only [negative, negative_base, negative_allUnit, negative_next]

end
end Lemmatheca.ProofTheory.HeytingArithmetic.NegativeTranslation
