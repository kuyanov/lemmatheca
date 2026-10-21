import Lemmatheca.PaProofCheckers.PAProofSpecializationPrograms
import Lemmatheca.PaProofCheckers.PAProofReflexivity
import Lemmatheca.PaListsAndSyntax.PAModelSyntax
import Lemmatheca.PaListsAndSyntax.PAFixedFormulaCorrectness

open Lemmatheca.MathematicalLogic Lemmatheca.ModelTheory Lemmatheca.ComputabilityTheory

/-! Correctness of one universal specialization of an accepted proof. -/
namespace Lemmatheca.ProofTheory.PAComputations.ProofPrograms.CheckerPrograms.NumericalProofs
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic ArithmeticTheories ArithmeticRepresentability FirstOrderProofs
open SyntaxPrograms FixedSyntaxPrograms
noncomputable section
universe u
variable {M : Type u} [language.Structure M] [M ⊨ PA]

theorem specializeOne_model_value {r : ℕ} (p t : Program r) (x : Fin r → M) :
    (specializeOne p t).value x = forallEliminationCertificate.value
      ![p.value x, (argument 0).value ![conclusionValue (rootValue (p.value x))], t.value x] := by
  simp only [specializeOne, ternary_value, binary_value, unary_value, constant_value,
    numeral_value_zero]
  rfl

theorem certified_specializeOne (E : Program 2) {r : ℕ} (p t : Program r)
    (x : Fin r → M) (b : M) (hp : Certified E (p.value x) (modelNode 7 [b]))
    (hb : namedForm.value ![numeralValue M 1, b] = numeralValue M 1)
    (ht : namedTerm.value ![t.value x] = numeralValue M 1)
    (hout : isSentence.value ![instantiate.value ![b, t.value x] ] = numeralValue M 1) :
    Certified E ((specializeOne p t).value x) (instantiate.value ![b, t.value x]) := by
  have hroot := ((certified_iff E (p.value x) _).mp hp).2.2.1
  rw [specializeOne_model_value, hroot]
  have harg : (argument 0).value ![modelNode 7 [b] ] = b := by
    simpa only [List.getElem?_cons_zero, Option.getD_some] using
      argument_modelNode_value (M := M) 7 0 [b]
  rw [harg]
  exact certified_forallElimination E _ _ _ hp hb ht hout

end
end Lemmatheca.ProofTheory.PAComputations.ProofPrograms.CheckerPrograms.NumericalProofs
