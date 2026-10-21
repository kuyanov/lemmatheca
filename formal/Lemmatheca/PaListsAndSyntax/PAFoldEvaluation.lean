import Lemmatheca.PaListsAndSyntax.PAListPrograms
import Lemmatheca.PaListsAndSyntax.PAParametricFold

open Lemmatheca.MathematicalLogic Lemmatheca.ModelTheory Lemmatheca.ComputabilityTheory

namespace Lemmatheca.ProofTheory.PAComputations.ProofPrograms
open Lemmatheca.MathematicalLogic ArithmeticTheories
noncomputable section
local instance foldEvaluationLocalInstance1 : ℕ ⊨ PA := nat_models_PA
private theorem zero_value_nat : zeroValue ℕ = 0 := rfl

theorem foldInto_eval_code (h : Program 2) (s : List ℕ) (z : ℕ) :
    (foldInto h).eval ![FiniteSequenceCoding.code s, z] =
      s.foldl (fun z a => h.eval ![a, z]) z := by
  induction s generalizing z with
  | nil =>
    have hz := foldInto_zero_value (M := ℕ) h z
    simpa only [value_nat_eq_eval, zero_value_nat, FiniteSequenceCoding.code,
      Encodable.encode_list_nil, List.foldl_nil] using hz
  | cons a s ih =>
    have hs := foldInto_cons_value (M := ℕ) h a (FiniteSequenceCoding.code s) z
    simp only [value_nat_eq_eval, listCons_eval, Matrix.cons_val_zero, Matrix.cons_val_one] at hs
    rw [FiniteSequenceCoding.code_cons, hs, ih]
    rfl

theorem paramFold_eval_code (h : Program 3) (p : ℕ) (s : List ℕ) (z : ℕ) :
    (paramFold h).eval ![p, FiniteSequenceCoding.code s, z] =
      s.foldl (fun z a => h.eval ![p, a, z]) z := by
  induction s generalizing z with
  | nil =>
    have hz := paramFold_zero_value (M := ℕ) h p z
    simpa only [value_nat_eq_eval, zero_value_nat, FiniteSequenceCoding.code,
      Encodable.encode_list_nil, List.foldl_nil] using hz
  | cons a s ih =>
    have hs := paramFold_cons_value (M := ℕ) h p a (FiniteSequenceCoding.code s) z
    simp only [value_nat_eq_eval, listCons_eval, Matrix.cons_val_zero, Matrix.cons_val_one] at hs
    rw [FiniteSequenceCoding.code_cons, hs, ih]
    rfl

theorem paramFold_eval (h : Program 3) (x : Fin 3 → ℕ) :
    (paramFold h).eval x = (FiniteSequenceCoding.decode (x 1)).foldl
      (fun z a => h.eval ![x 0, a, z]) (x 2) := by
  have hx : x = ![x 0, x 1, x 2] := by
    funext i
    fin_cases i <;> rfl
  conv_lhs => rw [hx, ← FiniteSequenceCoding.code_decode (x 1), paramFold_eval_code]

theorem listReverse_eval (x : Fin 1 → ℕ) :
    listReverse.eval x = FiniteSequenceCoding.reverse (x 0) := by
  have hv := listReverse_value (M := ℕ) (x 0)
  simp only [value_nat_eq_eval] at hv
  have hx : x = ![x 0] := by
    funext i
    fin_cases i
    rfl
  rw [hx, hv, ← FiniteSequenceCoding.code_decode (x 0), foldInto_eval_code]
  have hf (s : List ℕ) (t : List ℕ) :
      s.foldl (fun z a => listCons.eval ![a, z]) (FiniteSequenceCoding.code t) =
        FiniteSequenceCoding.code (s.reverse ++ t) := by
    induction s generalizing t with
    | nil => rfl
    | cons a s ih =>
      rw [List.foldl_cons]
      have he : listCons.eval ![a, FiniteSequenceCoding.code t] =
          FiniteSequenceCoding.code (a :: t) := by
        simp only [listCons_eval, Matrix.cons_val_zero, Matrix.cons_val_one,
          FiniteSequenceCoding.code_cons]
      rw [he, ih]
      simp only [List.reverse_cons, List.append_assoc, List.singleton_append]
  simpa only [zero_value_nat, FiniteSequenceCoding.code, Encodable.encode_list_nil,
    List.append_nil, FiniteSequenceCoding.reverse, Matrix.cons_val_zero,
    FiniteSequenceCoding.code_decode] using hf (FiniteSequenceCoding.decode (x 0)) []

end
end Lemmatheca.ProofTheory.PAComputations.ProofPrograms
