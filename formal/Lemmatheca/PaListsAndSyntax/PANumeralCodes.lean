import Lemmatheca.PaListsAndSyntax.PANativeSyntaxRecurrences
import Lemmatheca.PaListsAndSyntax.PANativeSyntaxEvaluation

open Lemmatheca.MathematicalLogic Lemmatheca.ModelTheory Lemmatheca.ComputabilityTheory

/-! Interpret fixed numerical list and syntax-node codes in PA models. -/
namespace Lemmatheca.ProofTheory.PAComputations.ProofPrograms.CheckerPrograms
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic ArithmeticTheories ArithmeticRepresentability FirstOrderProofs
open SyntaxPrograms
noncomputable section
universe u
variable {M : Type u} [language.Structure M] [M ⊨ PA]

omit [M ⊨ PA] in
theorem numeral_pair_vector (a b : ℕ) :
    (fun i : Fin 2 => numeralValue M (![a, b] i)) =
      ![numeralValue M a, numeralValue M b] := by
  funext i
  fin_cases i <;> rfl

theorem modelList_numerals (xs : List ℕ) :
    modelList (xs.map (numeralValue M)) = numeralValue M (FiniteSequenceCoding.code xs) := by
  induction xs with
  | nil => exact (numeral_value_zero M).symm
  | cons a xs ih =>
    rw [List.map_cons, modelList_cons, ih, FiniteSequenceCoding.code_cons]
    have h := listCons.value_numerals (M := M) ![a, FiniteSequenceCoding.code xs]
    simpa only [numeral_pair_vector, listCons_eval, Matrix.cons_val_zero, Matrix.cons_val_one] using h

theorem modelNode_numerals (k : ℕ) (xs : List ℕ) :
    modelNode k (xs.map (numeralValue M)) = numeralValue M (CodingFormalProofs.node k xs) := by
  rw [modelNode, modelList_numerals]
  have h := listCons.value_numerals (M := M) ![k, FiniteSequenceCoding.code xs]
  simpa only [numeral_pair_vector, listCons_eval, Matrix.cons_val_zero, Matrix.cons_val_one,
    CodingFormalProofs.node, FiniteSequenceCoding.cons, Nat.add_comm] using h

end
end Lemmatheca.ProofTheory.PAComputations.ProofPrograms.CheckerPrograms
