import Lemmatheca.MathematicalLogic.PANativeSyntaxEvaluation
import Lemmatheca.MathematicalLogic.PANativeRewriteEvaluation

namespace Lemmatheca.MathematicalLogic.PAComputations.ProofPrograms.SyntaxPrograms
open Lemmatheca.MathematicalLogic
noncomputable section

private theorem substitutionRewrite_eval (x : Fin 4 → ℕ) :
    (Program.comp rewrite ![constant 0, .proj 2, .proj 3, .proj 1]).eval x =
      CodingFormalProofs.rewrite 0 (x 2) (x 3) (x 1) := by
  rw [Program.eval, rewrite_eval]
  rfl

set_option maxHeartbeats 1600000 in
set_option backward.dsimp.instances true in
theorem substitute_eval (x : Fin 4 → ℕ) :
    substitute.eval x = CodingFormalProofs.substitute CodingFormalProofs.arithmeticSignature
      (x 0) (x 1) (x 2) (x 3) := by
  simp only [substitute, ternary_eval, binary_eval, projection_eval, constant_eval,
    isForm_eval, isTerm_eval, multiplication_eval, substitutionRewrite_eval,
    select_eval_values, CodingFormalProofs.substitute, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  by_cases hf : CodingFormalProofs.isForm CodingFormalProofs.arithmeticSignature (x 0) (x 1) = true <;>
    by_cases ht : CodingFormalProofs.isTerm CodingFormalProofs.arithmeticSignature 0 (x 3) = true <;>
    simp only [Bool.and_eq_true, hf, ht, Bool.false_eq_true, ↓reduceIte, true_and,
      false_and, and_false, Nat.zero_mul, Nat.one_mul, Nat.reduceEqDiff]

end
end Lemmatheca.MathematicalLogic.PAComputations.ProofPrograms.SyntaxPrograms
