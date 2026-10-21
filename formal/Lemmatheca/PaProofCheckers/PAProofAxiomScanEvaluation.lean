import Lemmatheca.PaListsAndSyntax.PASyntaxEvaluation
import Lemmatheca.PaProofCheckers.PAProofAxiomScan

open Lemmatheca.MathematicalLogic Lemmatheca.ModelTheory Lemmatheca.ComputabilityTheory

namespace Lemmatheca.ProofTheory.PAComputations.ProofPrograms.CheckerPrograms
open Lemmatheca.MathematicalLogic ArithmeticTheories
noncomputable section
local instance proofAxiomScanEvaluationLocalInstance1 : ℕ ⊨ PA := nat_models_PA
private theorem zero_value_nat : zeroValue ℕ = 0 := rfl
private theorem mul_value_nat (a b : ℕ) : mulValue ℕ a b = a * b := rfl

theorem axiomScan_eval_codes (E : Program 2) (f : ℕ → ℕ → Bool)
    (hE : ∀ a w, E.eval ![a, w] = boolNat (f a w))
    (gamma ws : List ℕ) (hlen : gamma.length = ws.length) :
    (axiomScan E).eval ![FiniteSequenceCoding.code gamma, FiniteSequenceCoding.code ws, gamma.length] =
      boolNat ((gamma.zip ws).all (fun aw =>
        CodingFormalProofs.isSentence CodingFormalProofs.arithmeticSignature aw.1 && f aw.1 aw.2)) := by
  induction gamma generalizing ws with
  | nil =>
    have hw : ws = [] := List.length_eq_zero_iff.mp hlen.symm
    subst ws
    have h := axiomScan_zero_value (M := ℕ) E 0 0
    simpa only [Program.value_nat, zero_value_nat, numeral_value_nat,
      FiniteSequenceCoding.code, Encodable.encode_list_nil, List.length_nil,
      List.zip_nil_left, List.all_nil, boolNat_true] using h
  | cons a gamma ih =>
    cases ws with
    | nil => simp only [List.length_cons, List.length_nil] at hlen; omega
    | cons w ws =>
      have ht : gamma.length = ws.length := Nat.succ.inj hlen
      have h := axiomList_cons_value (M := ℕ) E a (FiniteSequenceCoding.code gamma) w (FiniteSequenceCoding.code ws)
      simp only [axiomListValue, axiomCondition, Program.value_nat, listCons_eval,
        Matrix.cons_val_zero, Matrix.cons_val_one, isSentence_eval, hE,
        mul_value_nat] at h
      simp only [← FiniteSequenceCoding.code_cons, listLength_eval,
        Matrix.cons_val_zero, FiniteSequenceCoding.length, FiniteSequenceCoding.decode_code] at h
      rw [h, ih ws ht, boolNat_mul, boolNat_mul]
      rfl


theorem axiomScan_eval_lengths (E : Program 2) (f : ℕ → ℕ → Bool)
    (hE : ∀ a w, E.eval ![a, w] = boolNat (f a w))
    (gamma ws : ℕ)
    (hlen : (FiniteSequenceCoding.decode gamma).length = (FiniteSequenceCoding.decode ws).length) :
    (axiomScan E).eval ![gamma, ws, (FiniteSequenceCoding.decode gamma).length] =
      boolNat (((FiniteSequenceCoding.decode gamma).zip (FiniteSequenceCoding.decode ws)).all
        (fun aw => CodingFormalProofs.isSentence CodingFormalProofs.arithmeticSignature aw.1 && f aw.1 aw.2)) := by
  simpa only [FiniteSequenceCoding.code_decode] using
    axiomScan_eval_codes E f hE (FiniteSequenceCoding.decode gamma) (FiniteSequenceCoding.decode ws) hlen

end
end Lemmatheca.ProofTheory.PAComputations.ProofPrograms.CheckerPrograms
