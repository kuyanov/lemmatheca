import Lemmatheca.PaProofCheckers.PAProofRuleFacts

open Lemmatheca.MathematicalLogic Lemmatheca.ModelTheory Lemmatheca.ComputabilityTheory

/-! Each equivalence is the corresponding branch of the actual shared
19-rule checker, evaluated at a numerical record with arbitrary PA-model
fields.  These are code equations, not additional inference rules. -/
namespace Lemmatheca.ProofTheory.PAComputations.ProofPrograms.CheckerPrograms
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic ArithmeticTheories ArithmeticRepresentability
open SyntaxPrograms
noncomputable section
universe u
variable {M : Type u} [language.Structure M] [M ⊨ PA]
local instance proofLocalRulesLocalInstance1 (P : Prop) : Decidable P := Classical.propDecidable P

def negValue (a : M) : M := implication.value ![a, modelNode 3 [] ]
def andValue (a b : M) : M := negValue (implication.value ![a, negValue b])
def orValue (a b : M) : M := implication.value ![negValue a, b]
def exValue (a : M) : M := negValue (modelNode 7 [negValue a])

theorem bottom_value {n : ℕ} (x : Fin n → M) :
    (bottom : Program n).value x = modelNode 3 [] := by
  simp only [bottom, syntaxNode_value, list_nil_value, modelNode, modelList_nil]

theorem negCode_value {n : ℕ} (p : Program n) (x : Fin n → M) :
    (negCode p).value x = negValue (p.value x) := by
  simp only [negCode, impCode, binary_value, bottom_value, negValue]

theorem andCode_value {n : ℕ} (p q : Program n) (x : Fin n → M) :
    (andCode p q).value x = andValue (p.value x) (q.value x) := by
  simp only [andCode, negCode_value, impCode, binary_value, andValue]

theorem orCode_value {n : ℕ} (p q : Program n) (x : Fin n → M) :
    (orCode p q).value x = orValue (p.value x) (q.value x) := by
  simp only [orCode, impCode, binary_value, negCode_value, orValue]

theorem exCode_value {n : ℕ} (p : Program n) (x : Fin n → M) :
    (exCode p).value x = exValue (p.value x) := by
  simp only [exCode, negCode_value, allCode_value, exValue]

theorem auxCode_value {n : ℕ} (p : Program n) (x : Fin n → M) :
    (auxCode p).value x = modelNode 8 [p.value x] := by
  simp only [auxCode, syntaxNode_value, list_cons_value, list_nil_value,
    modelNode, modelList_cons, modelList_nil]

syntax "local_rule_simp" : tactic
macro_rules
| `(tactic| local_rule_simp) => `(tactic|
  (simp only [localRule, ternary_value, binary_value, unary_value, Program.value_proj,
    Matrix.cons_val_zero, Matrix.cons_val_one, tag_modelNode_value,
    argument_modelNode_value, args_modelNode_value, modelList_length_value,
    constant_value, equalTest_value, numeral_eq_iff_model, numeral_eq_zero_iff_model,
    Nat.reduceEqDiff, ↓reduceIte, select_value, conjunction_cons_one_iff,
    conjunction_nil_value, Holds, conclusionValue, contextValue, impCode, allCode_value,
    equalCode_value, bottom_value, negCode_value, andCode_value, orCode_value, exCode_value,
    auxCode_value, booleanNot_value, and_true, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.getD_some, List.length_cons, List.length_nil]
   simp only [ite_eq_left_iff, zero_eq_numeral_iff_model, Nat.reduceEqDiff,
    imp_false, not_not, true_and, and_true, numeral_value_zero]))

set_option maxRecDepth 8000
set_option maxHeartbeats 1600000

theorem localRule_assumption_one_iff (gamma a hist : M) :
    localRule.value ![modelNode 100 [gamma, a], hist] = numeralValue M 1 ↔
      listMember.value ![a, gamma] = numeralValue M 1 := by
  local_rule_simp

theorem localRule_andIntro_one_iff (gamma a d e hist : M) :
    localRule.value ![modelNode 101 [gamma, a, d, e], hist] = numeralValue M 1 ↔
      Holds hist d gamma (conclusionValue d) ∧ Holds hist e gamma (conclusionValue e) ∧
        a = andValue (conclusionValue d) (conclusionValue e) := by
  local_rule_simp

theorem localRule_andLeft_one_iff (gamma a d b hist : M) :
    localRule.value ![modelNode 102 [gamma, a, d, b], hist] = numeralValue M 1 ↔
      namedForm.value ![zeroValue M, b] = numeralValue M 1 ∧ Holds hist d gamma (andValue a b) := by
  local_rule_simp

theorem localRule_andRight_one_iff (gamma a d b hist : M) :
    localRule.value ![modelNode 103 [gamma, a, d, b], hist] = numeralValue M 1 ↔
      namedForm.value ![zeroValue M, b] = numeralValue M 1 ∧ Holds hist d gamma (andValue b a) := by
  local_rule_simp

theorem localRule_orLeft_one_iff (gamma a d b hist : M) :
    localRule.value ![modelNode 104 [gamma, a, d, b], hist] = numeralValue M 1 ↔
      Holds hist d gamma (conclusionValue d) ∧ namedForm.value ![zeroValue M, b] = numeralValue M 1 ∧
        a = orValue (conclusionValue d) b := by
  local_rule_simp

theorem localRule_orRight_one_iff (gamma a d b hist : M) :
    localRule.value ![modelNode 105 [gamma, a, d, b], hist] = numeralValue M 1 ↔
      Holds hist d gamma (conclusionValue d) ∧ namedForm.value ![zeroValue M, b] = numeralValue M 1 ∧
        a = orValue b (conclusionValue d) := by
  local_rule_simp

theorem localRule_orElim_one_iff (gamma a d e f b c hist : M) :
    localRule.value ![modelNode 106 [gamma, a, d, e, f, b, c], hist] = numeralValue M 1 ↔
      namedForm.value ![zeroValue M, b] = numeralValue M 1 ∧
      namedForm.value ![zeroValue M, c] = numeralValue M 1 ∧
      Holds hist d gamma (orValue b c) ∧
      Holds hist e (listCons.value ![b, gamma]) a ∧ Holds hist f (listCons.value ![c, gamma]) a := by
  local_rule_simp

theorem localRule_impIntro_one_iff (gamma a d b hist : M) :
    localRule.value ![modelNode 107 [gamma, a, d, b], hist] = numeralValue M 1 ↔
      namedForm.value ![zeroValue M, b] = numeralValue M 1 ∧
      a = implication.value ![b, conclusionValue d] ∧
      Holds hist d (listCons.value ![b, gamma]) (conclusionValue d) := by
  local_rule_simp

theorem localRule_notIntro_one_iff (gamma a d b hist : M) :
    localRule.value ![modelNode 109 [gamma, a, d, b], hist] = numeralValue M 1 ↔
      namedForm.value ![zeroValue M, b] = numeralValue M 1 ∧
      a = negValue b ∧ Holds hist d (listCons.value ![b, gamma]) (modelNode 3 []) := by
  local_rule_simp

theorem localRule_notElim_one_iff (gamma a d e hist : M) :
    localRule.value ![modelNode 110 [gamma, a, d, e], hist] = numeralValue M 1 ↔
      a = modelNode 3 [] ∧ Holds hist d gamma (conclusionValue d) ∧
      Holds hist e gamma (negValue (conclusionValue d)) := by
  local_rule_simp

theorem localRule_falseElim_one_iff (gamma a d hist : M) :
    localRule.value ![modelNode 111 [gamma, a, d], hist] = numeralValue M 1 ↔
      Holds hist d gamma (modelNode 3 []) := by
  local_rule_simp

theorem localRule_byContra_one_iff (gamma a d hist : M) :
    localRule.value ![modelNode 112 [gamma, a, d], hist] = numeralValue M 1 ↔
      Holds hist d (listCons.value ![negValue a, gamma]) (modelNode 3 []) := by
  local_rule_simp

theorem localRule_exIntro_one_iff (gamma a d b t hist : M) :
    localRule.value ![modelNode 114 [gamma, a, d, b, t], hist] = numeralValue M 1 ↔
      namedForm.value ![numeralValue M 1, b] = numeralValue M 1 ∧
      namedTerm.value ![t] = numeralValue M 1 ∧ a = exValue b ∧
      Holds hist d gamma (instantiate.value ![b, t]) := by
  local_rule_simp

theorem localRule_allIntro_one_iff (gamma a d b c hist : M) :
    localRule.value ![modelNode 115 [gamma, a, d, b, c], hist] = numeralValue M 1 ↔
      namedForm.value ![numeralValue M 1, b] = numeralValue M 1 ∧ a = modelNode 7 [b] ∧
      Holds hist d gamma (instantiate.value ![b, modelNode 8 [c] ]) ∧
      occursAux.value ![c, b] = zeroValue M ∧ contextFresh.value ![c, gamma] = numeralValue M 1 := by
  local_rule_simp

theorem localRule_exElim_one_iff (gamma a d e b c hist : M) :
    localRule.value ![modelNode 116 [gamma, a, d, e, b, c], hist] = numeralValue M 1 ↔
      namedForm.value ![numeralValue M 1, b] = numeralValue M 1 ∧ Holds hist d gamma (exValue b) ∧
      Holds hist e (listCons.value ![instantiate.value ![b, modelNode 8 [c] ], gamma]) a ∧
      occursAux.value ![c, b] = zeroValue M ∧ occursAux.value ![c, a] = zeroValue M ∧
      contextFresh.value ![c, gamma] = numeralValue M 1 := by
  local_rule_simp

theorem localRule_eqRefl_one_iff (gamma a t hist : M) :
    localRule.value ![modelNode 117 [gamma, a, t], hist] = numeralValue M 1 ↔
      namedTerm.value ![t] = numeralValue M 1 ∧ a = modelNode 4 [t, t] := by
  local_rule_simp


theorem holds_of_checked (m d gamma delta a : M)
    (hd : Checked d gamma a) (hbound : leValue M (succValue M d) m)
    (hinc : contextIncluded.value ![gamma, delta] = numeralValue M 1) :
    Holds (proofHistoryValue m) d delta a := by
  refine ⟨?_, hd.2.2, ?_⟩
  · rw [derivation_history_entry_value m d hbound]
    exact hd.1
  · rw [show contextValue d = gamma from hd.2.1]
    exact hinc

end
end Lemmatheca.ProofTheory.PAComputations.ProofPrograms.CheckerPrograms
