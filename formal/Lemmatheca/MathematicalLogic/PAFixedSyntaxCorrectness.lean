import Lemmatheca.MathematicalLogic.PAFixedSyntaxPrograms
import Lemmatheca.MathematicalLogic.PANativeInstantiation
import Lemmatheca.MathematicalLogic.PANumeralSyntax

namespace Lemmatheca.MathematicalLogic.PAComputations.ProofPrograms.FixedSyntaxPrograms
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic ArithmeticTheories ArithmeticRepresentability
open SyntaxPrograms
noncomputable section
universe u
variable {M : Type u} [language.Structure M] [M ⊨ PA]

def PureTerm (a : M) : Prop :=
  stats.value ![a] = modelSummary (numeralValue M 1) (zeroValue M) (zeroValue M) (zeroValue M) ∧
  ∀ i t : M, rewrite.value ![numeralValue M 2, i, t, a] = a

theorem PureTerm.numeral (n : M) : PureTerm (ProofPrograms.numeral.value ![n]) :=
  ⟨numeral_stats_value n, fun i t => rewrite_slot_numeral_value i t n⟩

theorem PureTerm.zero : PureTerm (modelNode 2 [zeroValue M]) := by
  simpa only [numeral_zero_modelNode_value] using PureTerm.numeral (zeroValue M)

private theorem statsPart_of_pure {a : M} (ha : PureTerm a) (i : Fin 4) :
    statsPart i a = ![numeralValue M 1, zeroValue M, zeroValue M, zeroValue M] i := by
  simp only [statsPart, ha.1, modelSummary_part_value]

theorem PureTerm.succ {a : M} (ha : PureTerm a) :
    PureTerm (modelNode 2 [numeralValue M 1, a]) := by
  let := modelLinearOrder M
  constructor
  · rw [stats_succ_modelNode_value]
    simp only [statsPart_of_pure ha, Matrix.cons_val_zero, Matrix.cons_val_two,
      Matrix.cons_val_three, numeral_eq_zero_iff_model, Nat.one_ne_zero, ↓reduceIte,
      Matrix.head_cons, Matrix.tail_cons, maximum_value, max_self]
  · intro i t
    rw [rewrite_slot_nonleaf_value 2 (by decide) (by decide) (by decide)]
    change modelNode 2 [numeralValue M 1, rewrite.value ![numeralValue M 2, i, t, a] ] = _
    rw [ha.2]

theorem PureTerm.binary (f : ℕ) (hf : f = 2 ∨ f = 3) {a b : M}
    (ha : PureTerm a) (hb : PureTerm b) :
    PureTerm (modelNode 2 [numeralValue M f, a, b]) := by
  let := modelLinearOrder M
  constructor
  · rw [stats_binary_modelNode_value f hf]
    simp only [statsPart_of_pure ha, statsPart_of_pure hb, Matrix.cons_val_zero,
      Matrix.cons_val_two, Matrix.cons_val_three, numeral_eq_zero_iff_model,
      Nat.one_ne_zero, false_or, ↓reduceIte, Matrix.head_cons, Matrix.tail_cons, maximum_value, max_self]
  · intro i t
    rw [rewrite_slot_nonleaf_value 2 (by decide) (by decide) (by decide)]
    change modelNode 2 [numeralValue M f,
      rewrite.value ![numeralValue M 2, i, t, a], rewrite.value ![numeralValue M 2, i, t, b] ] = _
    rw [ha.2, hb.2]

theorem PureTerm.namedTerm {a : M} (ha : PureTerm a) :
    CheckerPrograms.namedTerm.value ![a] = numeralValue M 1 :=
  CheckerPrograms.namedTerm_of_stats a (zeroValue M) ha.1

theorem PureTerm.equal_sentence {a b : M} (ha : PureTerm a) (hb : PureTerm b) :
    CheckerPrograms.isSentence.value ![modelNode 4 [a, b] ] = numeralValue M 1 := by
  let := modelLinearOrder M
  apply CheckerPrograms.isSentence_of_stats
  rw [stats_equal_modelNode_value]
  simp only [statsPart_of_pure ha, statsPart_of_pure hb, Matrix.cons_val_zero,
    Matrix.cons_val_two, Matrix.cons_val_three, numeral_eq_zero_iff_model,
    Nat.one_ne_zero, false_or, ↓reduceIte, Matrix.head_cons, Matrix.tail_cons, maximum_value, max_self]

theorem list_value {r : ℕ} (ps : List (Program r)) (x : Fin r → M) :
    (list ps).value x = modelList (ps.map (fun p => p.value x)) := by
  induction ps with
  | nil => exact list_nil_value x
  | cons p ps ih => rw [list_cons_value, ih]; rfl

theorem termCode_value {α : Type*} {r : ℕ} (name : α → Program r)
    (t : language.Term α) (x : Fin r → M) :
    (termCode name t).value x =
      match t with
      | .var i => (name i).value x
      | .func f ts => modelNode 2 (numeralValue M (CodingFormalProofs.arithFunctionCode f) ::
          List.ofFn (fun i => (termCode name (ts i)).value x)) := by
  cases t with
  | var i => rfl
  | func f ts =>
    simp only [termCode, syntaxNode_value, list_value, List.map_cons, constant_value,
      List.map_ofFn, Function.comp_def, modelNode, modelList_cons]

theorem termCode_pure {α : Type*} {r : ℕ} (name : α → Program r)
    (hn : ∀ i (x : Fin r → M), PureTerm ((name i).value x)) (t : language.Term α) (x : Fin r → M) :
    PureTerm ((termCode name t).value x) := by
  induction t with
  | var i => exact hn i x
  | func f ts ih =>
    rw [termCode_value]
    cases f with
    | zero => simpa only [CodingFormalProofs.arithFunctionCode, List.ofFn_zero,
        numeral_value_zero] using (PureTerm.zero (M := M))
    | succ => simpa only [CodingFormalProofs.arithFunctionCode, List.ofFn_succ,
        List.ofFn_zero] using (PureTerm.succ (ih 0))
    | add => simpa only [CodingFormalProofs.arithFunctionCode, List.ofFn_succ,
        List.ofFn_zero, Fin.succ_zero_eq_one] using (PureTerm.binary 2 (Or.inl rfl) (ih 0) (ih 1))
    | mul => simpa only [CodingFormalProofs.arithFunctionCode, List.ofFn_succ,
        List.ofFn_zero, Fin.succ_zero_eq_one] using (PureTerm.binary 3 (Or.inr rfl) (ih 0) (ih 1))

theorem termInstance_pure {r : ℕ} (t : language.Term (Fin r)) (x : Fin r → M) :
    PureTerm ((termInstance t).value x) := by
  apply termCode_pure numeralName
  intro i x
  simp only [numeralName, unary_value, Program.value_proj]
  exact PureTerm.numeral _

end
end Lemmatheca.MathematicalLogic.PAComputations.ProofPrograms.FixedSyntaxPrograms
