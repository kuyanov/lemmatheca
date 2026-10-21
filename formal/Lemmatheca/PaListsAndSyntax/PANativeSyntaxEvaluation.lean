import Lemmatheca.PaListsAndSyntax.PANativeSummaryEvaluation

open Lemmatheca.MathematicalLogic Lemmatheca.ModelTheory Lemmatheca.ComputabilityTheory

namespace Lemmatheca.ProofTheory.PAComputations.ProofPrograms.SyntaxPrograms
open Lemmatheca.MathematicalLogic
noncomputable section

theorem stats_eval (x : Fin 1 → ℕ) :
    stats.eval x = Encodable.encode (CodingFormalProofs.stats CodingFormalProofs.arithmeticSignature (x 0)) := by
  have hx : Fin.snoc (Fin.elim0 : Fin 0 → ℕ) (x 0) = x := by
    funext i
    fin_cases i
    rfl
  have hs : (fun i hist => summaryStep.eval
      (Fin.snoc (Fin.snoc (Fin.elim0 : Fin 0 → ℕ) i) hist)) =
      CodingFormalProofs.summaryStep CodingFormalProofs.arithmeticSignature := by
    funext i hist
    rw [summaryStep_eval]
    rfl
  have h := courseValue_eval summaryStep (Fin.elim0 : Fin 0 → ℕ) (x 0)
  rw [hx, hs] at h
  rw [CodingFormalProofs.stats, Denumerable.encode_ofNat]
  exact h

private theorem leq_eval_values (a b : ℕ) :
    leq.eval ![a, b] = flag (a ≤ b) := by
  simp only [leq, Program.eval, zeroTest_eval, subtraction_eval, Matrix.cons_val_zero,
    Matrix.cons_val_one, Nat.sub_eq_zero_iff_le]
  rfl

private theorem successor_eval_value (a : ℕ) : Program.succ.eval ![a] = a + 1 := rfl

theorem depthTest_eval_values (j : Fin 4) (n e : ℕ) :
    (depthTest j).eval ![n, e] = flag
      (0 < coordinate j (CodingFormalProofs.stats CodingFormalProofs.arithmeticSignature e) ∧
        coordinate j (CodingFormalProofs.stats CodingFormalProofs.arithmeticSignature e) ≤ n + 1) := by
  simp only [depthTest, binary_eval, unary_eval, projection_eval,
    multiplication_eval, sign_eval_values, leq_eval_values, part_eval, stats_eval,
    Denumerable.ofNat_encode, successor_eval_value, Matrix.cons_val_zero, Matrix.cons_val_one,
    flag_mul, Nat.pos_iff_ne_zero]

theorem isTerm_eval (x : Fin 2 → ℕ) :
    isTerm.eval x = if CodingFormalProofs.isTerm CodingFormalProofs.arithmeticSignature (x 0) (x 1)
      then 1 else 0 := by
  have hx : x = ![x 0, x 1] := by
    funext i
    fin_cases i <;> rfl
  conv_lhs => rw [hx]
  rw [isTerm, depthTest_eval_values]
  simp only [coordinate0, CodingFormalProofs.isTerm, Bool.and_eq_true, decide_eq_true_eq, flag]
  split_ifs with h <;> simp only [h, and_self, ↓reduceIte]

theorem isForm_eval (x : Fin 2 → ℕ) :
    isForm.eval x = if CodingFormalProofs.isForm CodingFormalProofs.arithmeticSignature (x 0) (x 1)
      then 1 else 0 := by
  have hx : x = ![x 0, x 1] := by
    funext i
    fin_cases i <;> rfl
  conv_lhs => rw [hx]
  rw [isForm, depthTest_eval_values]
  simp only [coordinate1, CodingFormalProofs.isForm, Bool.and_eq_true, decide_eq_true_eq, flag]
  split_ifs with h <;> simp only [h, and_self, ↓reduceIte]

end
end Lemmatheca.ProofTheory.PAComputations.ProofPrograms.SyntaxPrograms
