import Lemmatheca.PaListsAndSyntax.PANativeSyntaxEvaluation
import Lemmatheca.PaListsAndSyntax.PANativeRewriteEvaluation
import Lemmatheca.PaListsAndSyntax.PASyntaxOperations

open Lemmatheca.MathematicalLogic Lemmatheca.ModelTheory Lemmatheca.ComputabilityTheory

namespace Lemmatheca.ProofTheory.PAComputations.ProofPrograms.CheckerPrograms
open Lemmatheca.MathematicalLogic ArithmeticTheories
open SyntaxPrograms
noncomputable section
local instance syntaxEvaluationLocalInstance1 : ℕ ⊨ PA := nat_models_PA

private theorem zero_value_nat : zeroValue ℕ = 0 := rfl

def boolNat (b : Bool) : ℕ := if b then 1 else 0

@[simp] theorem boolNat_true : boolNat true = 1 := rfl
@[simp] theorem boolNat_false : boolNat false = 0 := rfl

theorem boolNat_mul (a b : Bool) : boolNat a * boolNat b = boolNat (a && b) := by
  cases a <;> cases b <;> rfl

theorem boolNat_zero_iff (a : Bool) : boolNat a = 0 ↔ a = false := by
  cases a <;> decide

theorem boolNat_select (c : Bool) (a b : ℕ) :
    select.eval ![boolNat c, a, b] = if c then a else b := by
  cases c <;> simp [select_eval, boolNat]

theorem conjunction_eval {n : ℕ} (ps : List (Program n)) (x : Fin n → ℕ) :
    (conjunction ps).eval x = (ps.map (fun p => p.eval x)).prod := by
  induction ps with
  | nil => simp only [conjunction, List.foldr_nil, constant_eval, List.map_nil, List.prod_nil]
  | cons p ps ih =>
    have h := conjunction_cons_value (M := ℕ) p ps x
    simp only [Program.value_nat] at h
    change (conjunction (p :: ps)).eval x = p.eval x * (conjunction ps).eval x at h
    rw [ih] at h
    exact h

private theorem product_bool_fold (s : List ℕ) (f : ℕ → Bool) (z : ℕ) :
    s.foldl (fun z a => z * boolNat (f a)) z =
      z * boolNat (s.all f) := by
  induction s generalizing z with
  | nil => simp only [List.foldl_nil, List.all_nil, boolNat_true, Nat.mul_one]
  | cons a s ih =>
    rw [List.foldl_cons, ih]
    simp only [List.all_cons]
    cases ha : f a <;> cases hs : s.all f <;>
      simp only [boolNat, Bool.false_eq_true, ↓reduceIte, Bool.false_and,
        Bool.true_and, Nat.mul_zero, Nat.mul_one]

theorem listAllStep_eval (h : Program 2) (x : Fin 3 → ℕ) :
    (listAllStep h).eval x = x 2 * h.eval ![x 0, x 1] := by
  simp only [listAllStep, binary_eval, multiplication_eval, projection_eval,
    Matrix.cons_val_zero, Matrix.cons_val_one]

theorem listAll_eval (h : Program 2) (f : ℕ → ℕ → Bool)
    (hh : ∀ p a, h.eval ![p, a] = boolNat (f p a)) (x : Fin 2 → ℕ) :
    (listAll h).eval x = boolNat ((FiniteSequenceCoding.decode (x 1)).all (f (x 0))) := by
  simp only [listAll, ternary_eval, paramFold_eval, projection_eval, constant_eval,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.head_cons, listAllStep_eval, hh, product_bool_fold,
    Nat.one_mul]

theorem listMember_eval_code (s : List ℕ) (p : ℕ) :
    listMember.eval ![p, FiniteSequenceCoding.code s] = if p ∈ s then 1 else 0 := by
  induction s with
  | nil =>
    have h := listMember_zero_value (M := ℕ) p
    simpa only [Program.value_nat, zero_value_nat, FiniteSequenceCoding.code,
      Encodable.encode_list_nil, List.not_mem_nil, ↓reduceIte] using h
  | cons a s ih =>
    have h := listMember_cons_value (M := ℕ) p a (FiniteSequenceCoding.code s)
    simp only [Program.value_nat, listCons_eval, numeral_value_nat,
      Matrix.cons_val_zero, Matrix.cons_val_one] at h
    rw [FiniteSequenceCoding.code_cons, h, ih]
    by_cases he : p = a <;> simp [he]

theorem listMember_eval (x : Fin 2 → ℕ) :
    listMember.eval x = if x 0 ∈ FiniteSequenceCoding.decode (x 1) then 1 else 0 := by
  have hx : x = ![x 0, x 1] := by ext i; fin_cases i <;> rfl
  conv_lhs => rw [hx, ← FiniteSequenceCoding.code_decode (x 1), listMember_eval_code]

theorem contextIncluded_eval (x : Fin 2 → ℕ) :
    contextIncluded.eval x = boolNat (CodingFormalProofs.contextIncluded (x 0) (x 1)) := by
  simp only [contextIncluded, binary_eval, projection_eval]
  have hh (p a : ℕ) : (binary listMember (.proj 1) (.proj 0)).eval ![p, a] =
      boolNat (decide (a ∈ FiniteSequenceCoding.decode p)) := by
    simp only [binary_eval, projection_eval, listMember_eval, Matrix.cons_val_zero,
      Matrix.cons_val_one, boolNat, decide_eq_true_eq]
    split_ifs with hh <;> simp only [hh, ↓reduceIte]
  rw [listAll_eval _ _ hh]
  rfl


theorem booleanNot_eval {n : ℕ} (p : Program n) (x : Fin n → ℕ) :
    (booleanNot p).eval x = if p.eval x = 0 then 1 else 0 := by
  simp only [booleanNot, unary_eval, zeroTest_eval, Matrix.cons_val_zero]
  split_ifs with h <;> simp only [h, ↓reduceIte]

theorem namedForm_eval (x : Fin 2 → ℕ) :
    namedForm.eval x = boolNat
      (CodingFormalProofs.namedForm CodingFormalProofs.arithmeticSignature (x 0) (x 1)) := by
  simp only [namedForm, binary_eval, unary_eval, multiplication_eval, projection_eval,
    Matrix.cons_val_zero, Matrix.cons_val_one, SyntaxPrograms.isForm_eval,
    booleanNot_eval, part_eval, stats_eval, Denumerable.ofNat_encode, coordinate2]
  simp only [CodingFormalProofs.namedForm, boolNat, Bool.and_eq_true, decide_eq_true_eq]
  split_ifs <;> simp_all

theorem namedTerm_eval (x : Fin 1 → ℕ) :
    namedTerm.eval x = boolNat
      (CodingFormalProofs.namedTerm CodingFormalProofs.arithmeticSignature (x 0)) := by
  simp only [namedTerm, binary_eval, unary_eval, multiplication_eval, projection_eval,
    Matrix.cons_val_zero, constant_eval, SyntaxPrograms.isTerm_eval,
    booleanNot_eval, part_eval, stats_eval, Denumerable.ofNat_encode, coordinate2]
  simp only [CodingFormalProofs.namedTerm, boolNat, Bool.and_eq_true, decide_eq_true_eq]
  split_ifs <;> simp_all

theorem isSentence_eval (x : Fin 1 → ℕ) :
    isSentence.eval x = boolNat
      (CodingFormalProofs.isSentence CodingFormalProofs.arithmeticSignature (x 0)) := by
  simp only [isSentence, binary_eval, unary_eval, multiplication_eval, projection_eval,
    Matrix.cons_val_zero, constant_eval, namedForm_eval,
    booleanNot_eval, part_eval, stats_eval, Denumerable.ofNat_encode, coordinate3]
  simp only [CodingFormalProofs.isSentence, boolNat, Bool.and_eq_true, decide_eq_true_eq]
  split_ifs <;> simp_all

theorem instantiate_eval (x : Fin 2 → ℕ) :
    instantiate.eval x = CodingFormalProofs.instantiate CodingFormalProofs.arithmeticSignature (x 0) (x 1) := by
  simp only [instantiate, ternary_eval, binary_eval, namedForm_eval,
    multiplication_eval, constant_eval, projection_eval,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  simp only [unary_eval, namedTerm_eval, boolNat_mul, boolNat_select, Program.eval, rewrite_eval, constant_eval, projection_eval,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Matrix.head_cons, CodingFormalProofs.instantiate]

private theorem disjoin_boolNat (a b : Bool) :
    disjoin.eval ![boolNat a, boolNat b] = boolNat (a || b) := by
  cases a <;> cases b <;> simp [disjoin_eval, boolNat]

private theorem fold_disjoin_bool (s : List ℕ) (f : ℕ → Bool) (b : Bool) :
    s.foldl (fun z a => disjoin.eval ![z, boolNat (f a)]) (boolNat b) =
      boolNat (b || s.any f) := by
  induction s generalizing b with
  | nil => cases b <;> rfl
  | cons a s ih =>
    rw [List.foldl_cons, disjoin_boolNat, ih, List.any_cons, Bool.or_assoc]

private theorem fold_disjoin_bool_zero (s : List ℕ) (f : ℕ → Bool) :
    s.foldl (fun z a => disjoin.eval ![z, boolNat (f a)]) 0 = boolNat (s.any f) := by
  simpa only [boolNat_false, Bool.false_or] using fold_disjoin_bool s f false

theorem occurrenceChild_eval (x : Fin 3 → ℕ) :
    occurrenceChild.eval x = disjoin.eval
      ![x 2, boolNat (decide (0 < FiniteSequenceCoding.entry (x 0) (x 1)))] := by
  simp only [occurrenceChild, binary_eval, unary_eval, sign_eval, listEntry_eval,
    projection_eval, Matrix.cons_val_zero, Matrix.cons_val_one]
  simp only [boolNat, decide_eq_true_eq, Nat.pos_iff_ne_zero]
  split_ifs <;> simp_all

private theorem occurrenceFold_eval (hist : ℕ) (s : List ℕ) :
    (paramFold occurrenceChild).eval ![hist, FiniteSequenceCoding.code s, 0] =
      boolNat (s.any (fun a => decide (0 < FiniteSequenceCoding.entry hist a))) := by
  simp only [paramFold_eval, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.head_cons, FiniteSequenceCoding.decode_code, occurrenceChild_eval]
  exact fold_disjoin_bool_zero s (fun a => decide (0 < FiniteSequenceCoding.entry hist a))

theorem occursStep_eval (x : Fin 3 → ℕ) :
    occursStep.eval x = CodingFormalProofs.occursStep (x 0) (x 1) (x 2) := by
  simp only [occursStep, ternary_eval, binary_eval, unary_eval, equalTest_eval_values,
    select_eval_values, tag_eval, argument_eval, children_eval, constant_eval, projection_eval,
    Matrix.cons_val_zero,
    occurrenceFold_eval, CodingFormalProofs.occursStep, flag, boolNat,
    List.any_eq_true, FiniteSequenceCoding.entry]
  split_ifs <;> simp_all [Nat.pos_iff_ne_zero]

theorem occursAux_eval (x : Fin 2 → ℕ) :
    occursAux.eval x = boolNat (CodingFormalProofs.occursAux (x 0) (x 1)) := by
  have hx : Fin.snoc (![x 0] : Fin 1 → ℕ) (x 1) = x := by
    ext i; fin_cases i <;> rfl
  have hs : (fun i hist => occursStep.eval
      (Fin.snoc (Fin.snoc (![x 0] : Fin 1 → ℕ) i) hist)) =
      CodingFormalProofs.occursStep (x 0) := by
    funext i hist
    rw [occursStep_eval]
    rfl
  have he := courseValue_eval occursStep (![x 0] : Fin 1 → ℕ) (x 1)
  rw [hx, hs] at he
  simp only [occursAux, unary_eval, he, sign_eval, Matrix.cons_val_zero,
    CodingFormalProofs.occursAux, CodingFormalProofs.earlierFold, boolNat,
    decide_eq_true_eq, Nat.pos_iff_ne_zero]
  split_ifs <;> simp_all


theorem boolNat_not (b : Bool) :
    (if boolNat b = 0 then 1 else 0) = boolNat (!b) := by
  cases b <;> rfl

theorem contextFresh_eval (x : Fin 2 → ℕ) :
    contextFresh.eval x = boolNat (CodingFormalProofs.contextFresh (x 0) (x 1)) := by
  unfold contextFresh
  have hh (p a : ℕ) : (booleanNot occursAux).eval ![p, a] =
      boolNat (!CodingFormalProofs.occursAux p a) := by
    simp only [booleanNot_eval, occursAux_eval, Matrix.cons_val_zero, Matrix.cons_val_one, boolNat_not]
  rw [listAll_eval _ _ hh]
  rfl

theorem formList_eval (x : Fin 2 → ℕ) :
    formList.eval x = boolNat ((FiniteSequenceCoding.decode (x 1)).all
      (CodingFormalProofs.namedForm CodingFormalProofs.arithmeticSignature 0)) := by
  unfold formList
  have hh (p a : ℕ) : (binary namedForm (constant 0) (.proj 1)).eval ![p, a] =
      boolNat (CodingFormalProofs.namedForm CodingFormalProofs.arithmeticSignature 0 a) := by
    simp only [binary_eval, namedForm_eval, constant_eval, projection_eval,
      Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [listAll_eval _ _ hh]

theorem bottom_eval {n : ℕ} (x : Fin n → ℕ) :
    (bottom : Program n).eval x = CodingFormalProofs.botCode := by
  simp only [bottom, syntaxNode_eval, List.map_nil]
  rfl

theorem equalCode_eval {n : ℕ} (a b : Program n) (x : Fin n → ℕ) :
    (equalCode a b).eval x = CodingFormalProofs.equalCode (a.eval x) (b.eval x) := by
  simp only [equalCode, syntaxNode_eval, List.map_cons, List.map_nil]
  rfl

theorem impCode_eval {n : ℕ} (a b : Program n) (x : Fin n → ℕ) :
    (impCode a b).eval x = CodingFormalProofs.impCode (a.eval x) (b.eval x) := by
  simp only [impCode, binary_eval, implication_eval, Matrix.cons_val_zero, Matrix.cons_val_one]

theorem allCode_eval {n : ℕ} (a : Program n) (x : Fin n → ℕ) :
    (allCode a).eval x = CodingFormalProofs.allCode (a.eval x) := by
  simp only [allCode, syntaxNode_eval, List.map_cons, List.map_nil]
  rfl

theorem negCode_eval {n : ℕ} (a : Program n) (x : Fin n → ℕ) :
    (negCode a).eval x = CodingFormalProofs.negCode (a.eval x) := by
  simp only [negCode, impCode_eval, bottom_eval, CodingFormalProofs.negCode]

theorem andCode_eval {n : ℕ} (a b : Program n) (x : Fin n → ℕ) :
    (andCode a b).eval x = CodingFormalProofs.andCode (a.eval x) (b.eval x) := by
  simp only [andCode, negCode_eval, impCode_eval, CodingFormalProofs.andCode]

theorem orCode_eval {n : ℕ} (a b : Program n) (x : Fin n → ℕ) :
    (orCode a b).eval x = CodingFormalProofs.orCode (a.eval x) (b.eval x) := by
  simp only [orCode, negCode_eval, impCode_eval, CodingFormalProofs.orCode]

theorem exCode_eval {n : ℕ} (a : Program n) (x : Fin n → ℕ) :
    (exCode a).eval x = CodingFormalProofs.exCode (a.eval x) := by
  simp only [exCode, negCode_eval, allCode_eval, CodingFormalProofs.exCode]

theorem auxCode_eval {n : ℕ} (a : Program n) (x : Fin n → ℕ) :
    (auxCode a).eval x = CodingFormalProofs.auxName (a.eval x) := by
  simp only [auxCode, syntaxNode_eval, List.map_cons, List.map_nil]
  rfl

end
end Lemmatheca.ProofTheory.PAComputations.ProofPrograms.CheckerPrograms
