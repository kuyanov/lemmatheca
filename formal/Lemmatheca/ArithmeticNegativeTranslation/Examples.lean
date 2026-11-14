import Lemmatheca.ArithmeticNegativeTranslation.Conservation

namespace Lemmatheca.ProofTheory.HeytingArithmetic.NegativeTranslation
open _root_.FirstOrder _root_.FirstOrder.Language
open Lemmatheca.ProofTheory.FirstOrder.NegativeTranslation (negative context)
universe u v
variable {α : Type u}
noncomputable section
local instance arithmeticNegativeExamplesFormulaEq {β : Type*} : DecidableEq (Formula β) := Classical.decEq _

/-- Original parameter y, induction variable x, and the distinguished witness z. -/
def existentialMatrix : Formula ((Fin 1 ⊕ Unit) ⊕ Unit) :=
  termEqual
    (addTerm (.var (.inl (.inr ()))) (.var (.inr ())))
    (.var (.inl (.inl 0)))

def existentialBody : Formula (Fin 1 ⊕ Unit) := exUnit existentialMatrix

theorem negative_existentialBody :
    negative existentialBody =
      .neg (.neg (exUnit (.neg (.neg existentialMatrix)))) := by rfl

theorem existential_induction_translation :
    negative (inductionAxiom existentialBody) =
      inductionAxiom (.neg (.neg (exUnit (.neg (.neg existentialMatrix))))) := by
  rw [negative_inductionAxiom, negative_existentialBody]

/-- This is the literal native inclusion of the established small existential code. -/
theorem included_existential_code (E : LA.BoundedFormula α 1) :
    Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.ofClassical E.ex =
      .impl (.all (.impl
        (Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.ofClassical E) .falsum)) .falsum := by rfl

theorem native_existential_ne_code (E : LA.BoundedFormula α 1) :
    (Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.ex
      (Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.ofClassical E)) ≠
      Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.ofClassical E.ex := by
  intro h
  cases h

end
end Lemmatheca.ProofTheory.HeytingArithmetic.NegativeTranslation
