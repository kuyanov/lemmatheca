import Lemmatheca.MathematicalLogic.PAProofCheckerEvaluation
import Lemmatheca.MathematicalLogic.FormalizedProvabilityTransformations

/-! The native and numerical modus-ponens operations are the same concrete
certificate transformation, rather than merely two accepted proof builders. -/
namespace Lemmatheca.MathematicalLogic.PAComputations.ProofPrograms.CheckerPrograms
open Lemmatheca.MathematicalLogic
open SyntaxPrograms
noncomputable section

theorem modusPonensRecord_eval (x : Fin 3 → ℕ) :
    modusPonensRecord.eval x = CodingFormalProofs.modusPonensRecord (x 0) (x 1) (x 2) := by
  simp only [modusPonensRecord, syntaxNode_eval, List.map_cons, List.map_nil,
    binary_eval, unary_eval, listAppend_eval, argument_eval, projection_eval,
    Matrix.cons_val_zero, Matrix.cons_val_one,
    CodingFormalProofs.modusPonensRecord, CodingFormalProofs.proofContext,
    FiniteSequenceCoding.append]

theorem modusPonensCertificate_eval (x : Fin 3 → ℕ) :
    modusPonensCertificate.eval x =
      CodingFormalProofs.modusPonensCertificate (x 0) (x 1) (x 2) := by
  simp only [modusPonensCertificate, list_eval, List.map_cons, List.map_nil,
    ternary_eval, binary_eval, modusPonensRecord_eval, listEntry_eval,
    listAppend_eval, projection_eval, constant_eval,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons,
    CodingFormalProofs.modusPonensCertificate]

end
end Lemmatheca.MathematicalLogic.PAComputations.ProofPrograms.CheckerPrograms
