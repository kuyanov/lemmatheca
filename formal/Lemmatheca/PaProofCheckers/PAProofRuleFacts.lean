import Lemmatheca.PaProofCheckers.PAProofCheckerWellformed

open Lemmatheca.MathematicalLogic Lemmatheca.ModelTheory Lemmatheca.ComputabilityTheory

namespace Lemmatheca.ProofTheory.PAComputations.ProofPrograms.CheckerPrograms
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic ArithmeticTheories ArithmeticRepresentability
open SyntaxPrograms
noncomputable section
universe u
variable {M : Type u} [language.Structure M] [M ⊨ PA]
local instance proofRuleFactsLocalInstance1 (P : Prop) : Decidable P := Classical.propDecidable P

def proofHistoryValue (d : M) : M := (history localCheck).value ![d]

theorem derivation_history_entry_value (d c : M) (hc : leValue M (succValue M c) d) :
    sign.value ![listEntry.value ![proofHistoryValue d, c] ] = derivationCheck.value ![c] := by
  have hv (a : M) : Fin.snoc (Fin.elim0 : Fin 0 → M) a = ![a] := by
    ext i; fin_cases i; rfl
  have he := history_entry_value localCheck (Fin.elim0 : Fin 0 → M) d c hc
  simp only [hv] at he
  unfold proofHistoryValue
  rw [he]
  simp only [derivationCheck, unary_value]

theorem derivationCheck_of_local_one (d : M)
    (hd : localCheck.value ![d, proofHistoryValue d] = numeralValue M 1) :
    derivationCheck.value ![d] = numeralValue M 1 := by
  rw [derivationCheck_equation_value, show (history localCheck).value ![d] = proofHistoryValue d from rfl,
    hd, sign_value]
  simp only [numeral_eq_zero_iff_model, Nat.one_ne_zero, ↓reduceIte]

theorem checked_of_rule (d gamma a : M) (hd : d ≠ zeroValue M)
    (hgamma : contextValue d = gamma) (ha : conclusionValue d = a)
    (hform : namedForm.value ![zeroValue M, a] = numeralValue M 1)
    (hcontext : formList.value ![zeroValue M, gamma] = numeralValue M 1)
    (hrule : localRule.value ![d, proofHistoryValue d] = numeralValue M 1) :
    Checked d gamma a := by
  refine ⟨derivationCheck_of_local_one d ?_, hgamma, ha⟩
  simp only [localCheck, conjunction_cons_value, conjunction_nil_value,
    binary_value, unary_value, Program.value_proj, constant_value,
    Matrix.cons_val_zero, numeral_value_zero, sign_value, hd, ↓reduceIte,
    show (argument 0).value ![d] = gamma from hgamma,
    show (argument 1).value ![d] = a from ha, hform, hcontext, hrule,
    numeral_one_mul_model]

def Holds (hist d gamma a : M) : Prop :=
  sign.value ![listEntry.value ![hist, d] ] = numeralValue M 1 ∧
    conclusionValue d = a ∧ contextIncluded.value ![contextValue d, gamma] = numeralValue M 1

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1600000 in
theorem localRule_mp_one_iff (gamma b d e hist : M) :
    localRule.value ![modelNode 108 [gamma, b, d, e], hist] = numeralValue M 1 ↔
      Holds hist d gamma (implication.value ![conclusionValue e, b]) ∧
      Holds hist e gamma (conclusionValue e) := by
  simp only [localRule, ternary_value, binary_value, unary_value, Program.value_proj,
    Matrix.cons_val_zero, Matrix.cons_val_one, tag_modelNode_value,
    argument_modelNode_value, args_modelNode_value, modelList_length_value,
    constant_value, equalTest_value, numeral_eq_iff_model, numeral_eq_zero_iff_model,
    Nat.reduceEqDiff, ↓reduceIte, select_value, conjunction_cons_one_iff,
    conjunction_nil_value, Holds, conclusionValue, contextValue, impCode, and_true,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
    List.length_cons, List.length_nil]
  simp only [ite_eq_left_iff, zero_eq_numeral_iff_model, Nat.reduceEqDiff,
    imp_false, not_not, true_and]


theorem allCode_value {n : ℕ} (p : Program n) (x : Fin n → M) :
    (allCode p).value x = modelNode 7 [p.value x] := by
  simp only [allCode, syntaxNode_value, list_cons_value, list_nil_value,
    modelNode, modelList_cons, modelList_nil]

theorem equalCode_value {n : ℕ} (p q : Program n) (x : Fin n → M) :
    (equalCode p q).value x = modelNode 4 [p.value x, q.value x] := by
  simp only [equalCode, syntaxNode_value, list_cons_value, list_nil_value,
    modelNode, modelList_cons, modelList_nil]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1600000 in
theorem localRule_allElim_one_iff (gamma a d b t hist : M) :
    localRule.value ![modelNode 113 [gamma, a, d, b, t], hist] = numeralValue M 1 ↔
      namedForm.value ![numeralValue M 1, b] = numeralValue M 1 ∧
      namedTerm.value ![t] = numeralValue M 1 ∧
      a = instantiate.value ![b, t] ∧ Holds hist d gamma (modelNode 7 [b]) := by
  simp only [localRule, ternary_value, binary_value, unary_value, Program.value_proj,
    Matrix.cons_val_zero, Matrix.cons_val_one, tag_modelNode_value,
    argument_modelNode_value, args_modelNode_value, modelList_length_value,
    constant_value, equalTest_value, numeral_eq_iff_model, numeral_eq_zero_iff_model,
    Nat.reduceEqDiff, ↓reduceIte, select_value, conjunction_cons_one_iff,
    conjunction_nil_value, Holds, conclusionValue, contextValue, allCode_value, and_true,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
    List.length_cons, List.length_nil]
  simp only [ite_eq_left_iff, zero_eq_numeral_iff_model, Nat.reduceEqDiff,
    imp_false, not_not, true_and]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1600000 in
theorem localRule_eqSubst_one_iff (gamma a d e b s t hist : M) :
    localRule.value ![modelNode 118 [gamma, a, d, e, b, s, t], hist] = numeralValue M 1 ↔
      namedForm.value ![numeralValue M 1, b] = numeralValue M 1 ∧
      namedTerm.value ![s] = numeralValue M 1 ∧
      namedTerm.value ![t] = numeralValue M 1 ∧
      a = instantiate.value ![b, t] ∧ Holds hist d gamma (modelNode 4 [s, t]) ∧
      Holds hist e gamma (instantiate.value ![b, s]) := by
  simp only [localRule, ternary_value, binary_value, unary_value, Program.value_proj,
    Matrix.cons_val_zero, Matrix.cons_val_one, tag_modelNode_value,
    argument_modelNode_value, args_modelNode_value, modelList_length_value,
    constant_value, equalTest_value, numeral_eq_iff_model, numeral_eq_zero_iff_model,
    Nat.reduceEqDiff, ↓reduceIte, select_value, conjunction_cons_one_iff,
    conjunction_nil_value, Holds, conclusionValue, contextValue, equalCode_value, and_true,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
    List.length_cons, List.length_nil]
  simp only [ite_eq_left_iff, zero_eq_numeral_iff_model, Nat.reduceEqDiff,
    imp_false, not_not, true_and]

end
end Lemmatheca.ProofTheory.PAComputations.ProofPrograms.CheckerPrograms
