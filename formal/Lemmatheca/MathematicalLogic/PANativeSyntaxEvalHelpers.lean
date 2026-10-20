import Lemmatheca.MathematicalLogic.PANativeSyntax
import Lemmatheca.MathematicalLogic.PAFoldEvaluation

namespace Lemmatheca.MathematicalLogic.PAComputations.ProofPrograms.SyntaxPrograms
open Lemmatheca.MathematicalLogic
noncomputable section

@[simp] theorem unary_eval {n : ℕ} (p : Program 1) (a : Program n) (x : Fin n → ℕ) :
    (unary p a).eval x = p.eval ![a.eval x] := by
  unfold unary
  rw [Program.eval]
  congr 1
  funext i
  fin_cases i
  rfl

@[simp] theorem binary_eval {n : ℕ} (p : Program 2) (a b : Program n) (x : Fin n → ℕ) :
    (binary p a b).eval x = p.eval ![a.eval x, b.eval x] := by
  unfold binary
  rw [Program.eval]
  congr 1
  funext i
  fin_cases i <;> rfl

@[simp] theorem ternary_eval {n : ℕ} (p : Program 3) (a b c : Program n) (x : Fin n → ℕ) :
    (ternary p a b c).eval x = p.eval ![a.eval x, b.eval x, c.eval x] := by
  unfold ternary
  rw [Program.eval]
  congr 1
  funext i
  fin_cases i <;> rfl

@[simp] theorem equalTest_eval (x : Fin 2 → ℕ) :
    equalTest.eval x = if x 0 = x 1 then 1 else 0 := by
  simp only [equalTest, unary_eval, binary_eval, zeroTest_eval, addition_eval,
    subtraction_eval, Program.eval, Matrix.cons_val_zero, Matrix.cons_val_one]
  have he : (x 0 - x 1 + (x 1 - x 0) = 0) ↔ x 0 = x 1 := by omega
  simp only [he]

@[simp] theorem maximum_eval (x : Fin 2 → ℕ) :
    maximum.eval x = max (x 0) (x 1) := by
  simp only [maximum, ternary_eval, select_eval, less_eval, Program.eval,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  by_cases h : x 0 < x 1 <;> simp [h, Nat.max_def] <;> omega

@[simp] theorem disjoin_eval (x : Fin 2 → ℕ) :
    disjoin.eval x = if x 0 = 0 ∧ x 1 = 0 then 0 else 1 := by
  simp only [disjoin, unary_eval, sign_eval, addition_eval, Matrix.cons_val_zero]
  simp only [Nat.add_eq_zero_iff]

@[simp] theorem quad_eval {n : ℕ} (a b c d : Program n) (x : Fin n → ℕ) :
    (quad a b c d).eval x = Encodable.encode (a.eval x, b.eval x, c.eval x, d.eval x) := by
  simp only [quad, binary_eval, squarePair_eval, Matrix.cons_val_zero, Matrix.cons_val_one,
    Encodable.encode_prod_val, Encodable.encode_nat]

def coordinate (i : Fin 4) (s : CodingFormalProofs.Stats) : ℕ := ![s.1, s.2.1, s.2.2.1, s.2.2.2] i

@[simp] theorem part_eval (i : Fin 4) (x : Fin 1 → ℕ) :
    (part i).eval x = coordinate i (Denumerable.ofNat CodingFormalProofs.Stats (x 0)) := by
  fin_cases i <;>
    simp only [part, unary_eval, unpairLeft_eval, unpairRight_eval,
      Matrix.cons_val_zero, coordinate, Denumerable.prod_ofNat_val, Denumerable.ofNat_nat,
      ] <;> rfl

@[simp] theorem tag_eval (x : Fin 1 → ℕ) :
    tag.eval x = CodingFormalProofs.tag (x 0) := by
  simp only [tag, unary_eval, unpairLeft_eval, predecessor_eval, Matrix.cons_val_zero,
    CodingFormalProofs.tag]

@[simp] theorem args_eval (x : Fin 1 → ℕ) :
    args.eval x = FiniteSequenceCoding.code (CodingFormalProofs.args (x 0)) := by
  simp only [args, unary_eval, unpairRight_eval, predecessor_eval, Matrix.cons_val_zero,
    CodingFormalProofs.args, FiniteSequenceCoding.code_decode]

@[simp] theorem argument_eval (i : ℕ) (x : Fin 1 → ℕ) :
    (argument i).eval x = CodingFormalProofs.arg (x 0) i := by
  simp only [argument, binary_eval, listEntry_eval, args_eval, constant_eval,
    Matrix.cons_val_zero, Matrix.cons_val_one, FiniteSequenceCoding.entry,
    FiniteSequenceCoding.decode_code, CodingFormalProofs.arg]

@[simp] theorem children_eval (x : Fin 1 → ℕ) :
    children.eval x = FiniteSequenceCoding.code (CodingFormalProofs.children (x 0)) := by
  simp only [children, ternary_eval, binary_eval, unary_eval, disjoin_eval, equalTest_eval,
    constant_eval, tag_eval, args_eval, select_eval, tail_eval,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, CodingFormalProofs.children,
    FiniteSequenceCoding.tail_code]
  by_cases h2 : CodingFormalProofs.tag (x 0) = 2 <;>
    by_cases h5 : CodingFormalProofs.tag (x 0) = 5 <;> simp [h2, h5]

theorem mapStep_eval (h : Program 2) (x : Fin 3 → ℕ) :
    (mapStep h).eval x = FiniteSequenceCoding.cons (h.eval ![x 0, x 1]) (x 2) := by
  simp only [mapStep, binary_eval, listCons_eval, Program.eval,
    Matrix.cons_val_zero, Matrix.cons_val_one]

theorem listMap_eval (h : Program 2) (x : Fin 2 → ℕ) :
    (listMap h).eval x = FiniteSequenceCoding.code
      ((FiniteSequenceCoding.decode (x 1)).map (fun a => h.eval ![x 0, a])) := by
  simp only [listMap, ternary_eval, unary_eval, paramFold_eval, Program.eval, listReverse_eval,
    constant_eval, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, FiniteSequenceCoding.reverse,
    FiniteSequenceCoding.decode_code, mapStep_eval]
  have hf (s t : List ℕ) :
      s.foldl (fun z a => FiniteSequenceCoding.cons (h.eval ![x 0, a]) z)
        (FiniteSequenceCoding.code t) =
      FiniteSequenceCoding.code ((s.map (fun a => h.eval ![x 0, a])).reverse ++ t) := by
    induction s generalizing t with
    | nil => rfl
    | cons a s ih =>
      rw [List.foldl_cons, ← FiniteSequenceCoding.code_cons, ih]
      simp only [List.map_cons, List.reverse_cons, List.append_assoc, List.singleton_append]
  simpa only [FiniteSequenceCoding.code, Encodable.encode_list_nil, List.append_nil,
    List.map_reverse, List.reverse_reverse] using
    hf (FiniteSequenceCoding.decode (x 1)).reverse []

theorem maxSummary_eval (i : Fin 4) (x : Fin 3 → ℕ) :
    (maxSummary i).eval x = max (x 2)
      (coordinate i (CodingFormalProofs.statsAt (x 0) (x 1))) := by
  simp only [maxSummary, binary_eval, unary_eval, maximum_eval, part_eval, listEntry_eval,
    Program.eval, Matrix.cons_val_zero, Matrix.cons_val_one, CodingFormalProofs.statsAt]

theorem goodSummary_eval (i : Fin 4) (x : Fin 3 → ℕ) :
    (goodSummary i).eval x = (x 2) *
      (if coordinate i (CodingFormalProofs.statsAt (x 0) (x 1)) = 0 then 0 else 1) := by
  simp only [goodSummary, binary_eval, unary_eval, multiplication_eval, sign_eval, part_eval,
    listEntry_eval, Program.eval, Matrix.cons_val_zero, Matrix.cons_val_one,
    CodingFormalProofs.statsAt]
  rfl

theorem foldSummary_eval (h : Program 3) (z : ℕ) (x : Fin 2 → ℕ) :
    (foldSummary h z).eval x = (CodingFormalProofs.children (x 0)).foldl
      (fun v e => h.eval ![x 1, e, v]) z := by
  simp only [foldSummary, ternary_eval, unary_eval, Program.eval, children_eval,
    constant_eval, paramFold_eval, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, FiniteSequenceCoding.decode_code]

theorem foldSummary_max_eval (i : Fin 4) (z : ℕ) (x : Fin 2 → ℕ) :
    (foldSummary (maxSummary i) z).eval x =
      ((CodingFormalProofs.children (x 0)).map (CodingFormalProofs.statsAt (x 1))).foldl
        (fun v s => max v (coordinate i s)) z := by
  simp only [foldSummary_eval, maxSummary_eval, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, List.foldl_map]

theorem fold_good (f : ℕ → ℕ) (s : List ℕ) (z : ℕ) :
    s.foldl (fun v e => v * (if f e = 0 then 0 else 1)) z =
      if s.all (fun e => decide (0 < f e)) then z else 0 := by
  induction s generalizing z with
  | nil => simp
  | cons a s ih =>
    rw [List.foldl_cons, ih]
    by_cases ha : f a = 0 <;> simp [ha, Nat.pos_iff_ne_zero]

set_option backward.isDefEq.respectTransparency false in
theorem foldSummary_good_eval (i : Fin 4) (x : Fin 2 → ℕ) :
    (foldSummary (goodSummary i) 1).eval x =
      if ((CodingFormalProofs.children (x 0)).map (CodingFormalProofs.statsAt (x 1))).all
        (fun s => decide (0 < coordinate i s)) then 1 else 0 := by
  simp only [foldSummary_eval, goodSummary_eval, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, List.all_map]
  convert fold_good (fun e => coordinate i (CodingFormalProofs.statsAt (x 1) e))
      (CodingFormalProofs.children (x 0)) 1 using 1
  rfl

theorem arithmeticFunctionTest_eval (x : Fin 2 → ℕ) :
    arithmeticFunctionTest.eval x =
      if CodingFormalProofs.arithmeticSignature.functionTest (x 0) (x 1) then 1 else 0 := by
  simp only [arithmeticFunctionTest, binary_eval, disjoin_eval, multiplication_eval,
    equalTest_eval, constant_eval, Program.eval, Matrix.cons_val_zero, Matrix.cons_val_one,
    CodingFormalProofs.arithmeticSignature, CodingFormalProofs.arithFunctionTest]
  by_cases h0 : x 0 = 0 <;> by_cases h1 : x 0 = 1 <;>
    by_cases h2 : x 0 = 2 <;> by_cases h3 : x 0 = 3 <;>
    by_cases a0 : x 1 = 0 <;> by_cases a1 : x 1 = 1 <;> by_cases a2 : x 1 = 2 <;>
      simp [h0, h1, h2, h3, a0, a1, a2]

def flag (P : Prop) [Decidable P] : ℕ := if P then 1 else 0

@[simp] theorem flag_eq_zero (P : Prop) [Decidable P] : flag P = 0 ↔ ¬ P := by
  by_cases h : P <;> simp [flag, h]

@[simp] theorem flag_mul (P Q : Prop) [Decidable P] [Decidable Q] :
    flag P * flag Q = flag (P ∧ Q) := by
  by_cases hp : P <;> by_cases hq : Q <;> simp [flag, hp, hq]

theorem equalTest_eval_flag (x : Fin 2 → ℕ) : equalTest.eval x = flag (x 0 = x 1) :=
  equalTest_eval x

theorem sign_eval_flag (x : Fin 1 → ℕ) : sign.eval x = flag (x 0 ≠ 0) := by
  rw [sign_eval]
  by_cases h : x 0 = 0 <;> simp [flag, h]

theorem arithmeticFunctionTest_eval_flag (x : Fin 2 → ℕ) :
    arithmeticFunctionTest.eval x = flag
      (CodingFormalProofs.arithmeticSignature.functionTest (x 0) (x 1) = true) :=
  arithmeticFunctionTest_eval x

theorem foldSummary_good_eval_flag (i : Fin 4) (x : Fin 2 → ℕ) :
    (foldSummary (goodSummary i) 1).eval x = flag
      (((CodingFormalProofs.children (x 0)).map (CodingFormalProofs.statsAt (x 1))).all
        (fun s => decide (0 < coordinate i s)) = true) :=
  foldSummary_good_eval i x

theorem equalTest_eval_values (a b : ℕ) :
    equalTest.eval ![a, b] = flag (a = b) := equalTest_eval_flag ![a, b]

theorem sign_eval_values (a : ℕ) :
    sign.eval ![a] = flag (a ≠ 0) := sign_eval_flag ![a]

theorem select_eval_values (c a b : ℕ) :
    select.eval ![c, a, b] = if c = 0 then b else a := select_eval ![c, a, b]

theorem functionTest_eval_values (f n : ℕ) :
    arithmeticFunctionTest.eval ![f, n] = flag
      (CodingFormalProofs.arithmeticSignature.functionTest f n = true) :=
  arithmeticFunctionTest_eval_flag ![f, n]

theorem goodTerm_eval (x : Fin 2 → ℕ) :
    (foldSummary (goodSummary 0) 1).eval x = flag
      (((CodingFormalProofs.children (x 0)).map (CodingFormalProofs.statsAt (x 1))).all
        (fun s => decide (0 < s.1)) = true) := foldSummary_good_eval_flag 0 x

theorem goodForm_eval (x : Fin 2 → ℕ) :
    (foldSummary (goodSummary 1) 1).eval x = flag
      (((CodingFormalProofs.children (x 0)).map (CodingFormalProofs.statsAt (x 1))).all
        (fun s => decide (0 < s.2.1)) = true) := foldSummary_good_eval_flag 1 x

theorem encode_zero_summary :
    Encodable.encode ((0, 0, 0, 0) : CodingFormalProofs.Stats) = 0 := rfl

theorem pair_zero_zero : Nat.pair 0 0 = 0 := rfl

theorem arithmetic_relation_false (a n : ℕ) :
    CodingFormalProofs.arithmeticSignature.relationTest a n = false := rfl

theorem encode_conditional (P : Prop) [Decidable P]
    (s t : CodingFormalProofs.Stats) :
    Encodable.encode (if P then s else t) =
      if P then Encodable.encode s else Encodable.encode t := by
  by_cases h : P <;> simp only [h, ↓reduceIte]


end
end Lemmatheca.MathematicalLogic.PAComputations.ProofPrograms.SyntaxPrograms
