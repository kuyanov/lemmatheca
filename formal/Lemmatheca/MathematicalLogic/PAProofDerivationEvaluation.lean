import Lemmatheca.MathematicalLogic.PAProofCheckerEvaluation

namespace Lemmatheca.MathematicalLogic.PAComputations.ProofPrograms.CheckerPrograms
open Lemmatheca.MathematicalLogic ArithmeticTheories
open SyntaxPrograms
noncomputable section

theorem equalTest_bool_eval (x : Fin 2 → ℕ) :
    equalTest.eval x = boolNat (decide (x 0 = x 1)) := by
  rw [equalTest_eval]
  simp only [boolNat, decide_eq_true_eq]

theorem sign_bool_eval (x : Fin 1 → ℕ) :
    sign.eval x = boolNat (decide (0 < x 0)) := by
  rw [sign_eval]
  simp only [boolNat, decide_eq_true_eq]
  split_ifs <;> simp_all

theorem member_bool_eval (x : Fin 2 → ℕ) :
    listMember.eval x = boolNat (decide (x 0 ∈ FiniteSequenceCoding.decode (x 1))) := by
  rw [listMember_eval]
  simp only [boolNat, decide_eq_true_eq]

theorem booleanNot_bool_eval {n : ℕ} (p : Program n) (f : Bool) (x : Fin n → ℕ)
    (hp : p.eval x = boolNat f) : (booleanNot p).eval x = boolNat (!f) := by
  rw [booleanNot_eval, hp, boolNat_not]

theorem equalTest_bool_values (a b : ℕ) :
    equalTest.eval ![a, b] = boolNat (decide (a = b)) := equalTest_bool_eval ![a, b]

theorem sign_bool_values (a : ℕ) :
    sign.eval ![a] = boolNat (decide (0 < a)) := sign_bool_eval ![a]

theorem member_bool_values (a c : ℕ) :
    listMember.eval ![a, c] = boolNat (decide (a ∈ FiniteSequenceCoding.decode c)) :=
  member_bool_eval ![a, c]

theorem conjunction_cons_eval {n : ℕ} (p : Program n) (ps : List (Program n)) (x : Fin n → ℕ) :
    (conjunction (p :: ps)).eval x = p.eval x * (conjunction ps).eval x := by
  simp only [conjunction, List.foldr_cons, binary_eval, multiplication_eval,
    Matrix.cons_val_zero, Matrix.cons_val_one]

theorem conjunction_nil_eval {n : ℕ} (x : Fin n → ℕ) :
    (conjunction []).eval x = 1 := by
  rw [conjunction, List.foldr_nil, constant_eval]

theorem dispatch_eval (n d hist : ℕ) (body rest : Program 2) :
    (ternary select (binary equalTest (unary tag (.proj 0)) (constant n)) body rest).eval ![d, hist] =
      if CodingFormalProofs.tag d = n then body.eval ![d, hist] else rest.eval ![d, hist] := by
  simp only [ternary_eval, binary_eval, unary_eval, tag_eval, constant_eval,
    projection_eval, Matrix.cons_val_zero, equalTest_eval_values, select_eval_values,
    flag_eq_zero, ite_not]

syntax "checker_std_simp" : tactic
macro_rules
| `(tactic| checker_std_simp) => `(tactic| (simp only [localCheck, conjunction_cons_eval, conjunction_nil_eval] <;>
   simp_all only [localRule, dispatch_eval, Nat.reduceEqDiff, ↓reduceIte] <;>
   simp_all only [conjunction_cons_eval, conjunction_nil_eval,
    ternary_eval, binary_eval, unary_eval, projection_eval, constant_eval,
    namedForm_eval, namedTerm_eval, instantiate_eval,
    formList_eval, contextIncluded_eval, contextFresh_eval, occursAux_eval,
    equalTest_bool_values, sign_bool_values, member_bool_values,
    booleanNot_eval, boolNat_not, boolNat_mul, boolNat_select,
    andCode_eval, orCode_eval, impCode_eval, negCode_eval, bottom_eval,
    allCode_eval, exCode_eval, equalCode_eval, auxCode_eval,
    tag_eval, args_eval, argument_eval, listLength_eval, listCons_eval,
    listEntry_eval, multiplication_eval, Nat.mul_one,
    Matrix.cons_val_zero, Matrix.cons_val_one, FiniteSequenceCoding.length,
    FiniteSequenceCoding.decode_code, CodingFormalProofs.localCheck,
    CodingFormalProofs.proofContext, CodingFormalProofs.proofConclusion,
    CodingFormalProofs.contextInsert, Bool.and_assoc, Nat.reduceEqDiff, decide_eq_true_eq,
    Bool.false_eq_true, Bool.and_false, Bool.false_and, boolNat_false, Nat.mul_zero, Nat.zero_mul] <;> rfl))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
set_option backward.dsimp.instances true in
theorem localCheck_eval_values (d hist : ℕ) :
    localCheck.eval ![d, hist] = boolNat
      (CodingFormalProofs.localCheck CodingFormalProofs.arithmeticSignature d hist) := by
  by_cases htag : CodingFormalProofs.tag d = 100 ∨
      CodingFormalProofs.tag d = 101 ∨
      CodingFormalProofs.tag d = 102 ∨
      CodingFormalProofs.tag d = 103 ∨
      CodingFormalProofs.tag d = 104 ∨
      CodingFormalProofs.tag d = 105 ∨
      CodingFormalProofs.tag d = 106 ∨
      CodingFormalProofs.tag d = 107 ∨
      CodingFormalProofs.tag d = 108 ∨
      CodingFormalProofs.tag d = 109 ∨
      CodingFormalProofs.tag d = 110 ∨
      CodingFormalProofs.tag d = 111 ∨
      CodingFormalProofs.tag d = 112 ∨
      CodingFormalProofs.tag d = 113 ∨
      CodingFormalProofs.tag d = 114 ∨
      CodingFormalProofs.tag d = 115 ∨
      CodingFormalProofs.tag d = 116 ∨
      CodingFormalProofs.tag d = 117 ∨
      CodingFormalProofs.tag d = 118
  · rcases htag with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    all_goals checker_std_simp
  · simp only [not_or] at htag
    rcases htag with ⟨h100, h101, h102, h103, h104, h105, h106, h107, h108, h109, h110, h111, h112, h113, h114, h115, h116, h117, h118⟩
    have hold : CodingFormalProofs.localCheck CodingFormalProofs.arithmeticSignature d hist = false := by
      unfold CodingFormalProofs.localCheck
      split <;> simp_all
    checker_std_simp

theorem localCheck_eval (x : Fin 2 → ℕ) :
    localCheck.eval x = boolNat
      (CodingFormalProofs.localCheck CodingFormalProofs.arithmeticSignature (x 0) (x 1)) := by
  have hx : x = ![x 0, x 1] := by ext i; fin_cases i <;> rfl
  conv_lhs => rw [hx]
  exact localCheck_eval_values (x 0) (x 1)


theorem derivationCheck_eval (x : Fin 1 → ℕ) :
    derivationCheck.eval x = boolNat
      (CodingFormalProofs.derivationCheck CodingFormalProofs.arithmeticSignature (x 0)) := by
  have hx : Fin.snoc (Fin.elim0 : Fin 0 → ℕ) (x 0) = x := by
    ext i; fin_cases i; rfl
  have hs : (fun i hist => localCheck.eval
      (Fin.snoc (Fin.snoc (Fin.elim0 : Fin 0 → ℕ) i) hist)) =
      (fun i hist => if CodingFormalProofs.localCheck CodingFormalProofs.arithmeticSignature i hist
        then 1 else 0) := by
    funext i hist
    rw [localCheck_eval]
    rfl
  have he := courseValue_eval localCheck (Fin.elim0 : Fin 0 → ℕ) (x 0)
  rw [hx, hs] at he
  simp only [derivationCheck, unary_eval, he, sign_eval, Matrix.cons_val_zero,
    CodingFormalProofs.derivationCheck, CodingFormalProofs.earlierFold, boolNat,
    decide_eq_true_eq, Nat.pos_iff_ne_zero]
  split_ifs <;> simp_all

end
end Lemmatheca.MathematicalLogic.PAComputations.ProofPrograms.CheckerPrograms
