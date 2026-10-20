import Lemmatheca.MathematicalLogic.PAProofAxiomVerifier
import Lemmatheca.MathematicalLogic.PAProofAxiomScanEvaluation
import Lemmatheca.MathematicalLogic.PAProofDerivationEvaluation

/-! Standard numerical correctness of the explicit native checker.  This bridge
compares the two concrete algorithms, not their provability conditions. -/
namespace Lemmatheca.MathematicalLogic.PAComputations.ProofPrograms.CheckerPrograms
open Lemmatheca.MathematicalLogic ArithmeticProofPredicates
open SyntaxPrograms
noncomputable section

theorem certificateCheck_eval_values (E : Program 2) (f : ℕ → ℕ → Bool)
    (hE : ∀ a w, E.eval ![a, w] = boolNat (f a w)) (p a : ℕ) :
    (certificateCheck E).eval ![p, a] =
      boolNat (CodingFormalProofs.certificateCheck CodingFormalProofs.arithmeticSignature f p a) := by
  simp only [certificateCheck, conjunction_cons_eval, conjunction_nil_eval,
    ternary_eval, binary_eval, unary_eval, projection_eval, constant_eval,
    listLength_eval, listEntry_eval, argument_eval, equalTest_bool_values,
    derivationCheck_eval, isSentence_eval, Matrix.cons_val_zero, Matrix.cons_val_one,
    Nat.mul_one, FiniteSequenceCoding.length]
  by_cases hlen : (FiniteSequenceCoding.decode
      (CodingFormalProofs.arg (FiniteSequenceCoding.entry p 0) 0)).length =
      (FiniteSequenceCoding.decode (FiniteSequenceCoding.entry p 1)).length
  · rw [axiomScan_eval_lengths E f hE _ _ hlen]
    simp only [boolNat_mul, CodingFormalProofs.certificateCheck,
      CodingFormalProofs.proofContext, CodingFormalProofs.proofConclusion,
      FiniteSequenceCoding.entry, Bool.and_assoc]
    rfl
  · simp only [hlen, decide_false, boolNat_false, Nat.zero_mul, Nat.mul_zero]
    simp only [CodingFormalProofs.certificateCheck, CodingFormalProofs.proofContext,
      CodingFormalProofs.proofConclusion, FiniteSequenceCoding.entry] at hlen ⊢
    simp only [hlen, decide_false, Bool.and_false, Bool.false_and, boolNat_false]

theorem certificateCheck_eval (E : Program 2) (f : ℕ → ℕ → Bool)
    (hE : ∀ a w, E.eval ![a, w] = boolNat (f a w)) (x : Fin 2 → ℕ) :
    (certificateCheck E).eval x =
      boolNat (CodingFormalProofs.certificateCheck CodingFormalProofs.arithmeticSignature f (x 0) (x 1)) := by
  have hx : x = ![x 0, x 1] := by ext i; fin_cases i <;> rfl
  conv_lhs => rw [hx]
  exact certificateCheck_eval_values E f hE (x 0) (x 1)

theorem native_checker_eval (x : Fin 2 → ℕ) :
    (certificateCheck axiomVerifier).eval x =
      if CodingFormalProofs.certificateCheck CodingFormalProofs.arithmeticSignature paAxiomCertificate (x 0) (x 1)
      then 1 else 0 := by
  exact certificateCheck_eval axiomVerifier paAxiomCertificate
    (fun a w => axiomVerifier_eval ![a, w]) x

end
end Lemmatheca.MathematicalLogic.PAComputations.ProofPrograms.CheckerPrograms
