import Lemmatheca.MathematicalLogic.PropositionalNormalForms

namespace Lemmatheca.Entry.PropositionalNormalForms
open Lemmatheca.MathematicalLogic

def xorDnf : PropFormula (Fin 2) :=
  .disj (.conj (.neg (.atom 0)) (.atom 1)) (.conj (.atom 0) (.neg (.atom 1)))
def xorCnf : PropFormula (Fin 2) :=
  .conj (.disj (.atom 0) (.atom 1)) (.disj (.neg (.atom 0)) (.neg (.atom 1)))
theorem xor_normal_forms : IsDnf xorDnf ∧ IsCnf xorCnf ∧
    (∀ v, eval v xorDnf = (v 0 != v 1)) ∧
    (∀ v, eval v xorCnf = (v 0 != v 1)) := by
  refine ⟨⟨[[⟨0, false⟩, ⟨1, true⟩], [⟨0, true⟩, ⟨1, false⟩]], rfl⟩,
    ⟨[[⟨0, true⟩, ⟨1, true⟩], [⟨0, false⟩, ⟨1, false⟩]], rfl⟩, ?_, ?_⟩
  · intro v
    cases h0 : v 0 <;> cases h1 : v 1 <;> simp [xorDnf, eval, h0, h1]
  · intro v
    cases h0 : v 0 <;> cases h1 : v 1 <;> simp [xorCnf, eval, h0, h1]

def firstInputDnf : PropFormula (Fin 2) :=
  .disj (.conj (.atom 0) (.neg (.atom 1))) (.conj (.atom 0) (.atom 1))
theorem normal_forms_not_unique : IsDnf firstInputDnf ∧
    IsDnf (.atom 0 : PropFormula (Fin 2)) ∧
    SemEquivalent firstInputDnf (.atom 0) ∧ firstInputDnf ≠ .atom 0 := by
  refine ⟨⟨[[⟨0, true⟩, ⟨1, false⟩], [⟨0, true⟩, ⟨1, true⟩]], rfl⟩,
    ⟨[[⟨0, true⟩]], rfl⟩, ?_, ?_⟩
  · intro v
    cases h0 : v 0 <;> cases h1 : v 1 <;> simp [firstInputDnf, eval, h0, h1]
  · intro h
    cases h

end Lemmatheca.Entry.PropositionalNormalForms
