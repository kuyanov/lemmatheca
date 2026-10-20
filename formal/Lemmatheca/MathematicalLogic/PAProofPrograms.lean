import Lemmatheca.MathematicalLogic.PAProgramValues
import Lemmatheca.MathematicalLogic.PAInduction
import Lemmatheca.MathematicalLogic.PAComputationsPrograms
import Lemmatheca.MathematicalLogic.PAInternalDefinability

/-! Explicit primitive-recursive program DAGs for the arithmetic and syntax
constructors used by the actual proof checker. Standard evaluation identities
and internal graph identities are kept separate. -/
namespace Lemmatheca.MathematicalLogic.PAComputations.ProofPrograms
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic ArithmeticTheories ArithmeticRepresentability
open CodingFormalProofs
noncomputable section
universe u

def constant {r : ℕ} : ℕ → Program r
  | 0 => .comp .zero Fin.elim0
  | n + 1 => .comp .succ (fun _ => constant n)

def addition : Program 2 :=
  .prec (.proj 0) (.comp .succ (fun _ => .proj 2))

def multiplication : Program 2 :=
  .prec (constant 0) (.comp addition ![.proj 2, .proj 0])

def predecessor : Program 1 := .prec .zero (.proj 0)

def subtraction : Program 2 := .prec (.proj 0) (.comp predecessor ![.proj 2])

def sign : Program 1 := .prec .zero (constant 1)
def zeroTest : Program 1 := .prec (constant 1) (constant 0)

def less : Program 2 := .comp sign ![.comp subtraction ![.proj 1, .proj 0] ]

/-- Select the second input on a nonzero first input, otherwise the third. -/
def select : Program 3 :=
  .comp addition ![
    .comp multiplication ![.comp sign ![.proj 0], .proj 1],
    .comp multiplication ![.comp zeroTest ![.proj 0], .proj 2] ]

/-- The exact square pairing function used by the corpus, not Cantor's pairing. -/
def squarePair : Program 2 :=
  .comp select ![
    less,
    .comp addition ![.comp multiplication ![.proj 1, .proj 1], .proj 0],
    .comp addition ![.comp addition ![.comp multiplication ![.proj 0, .proj 0], .proj 0],
      .proj 1] ]

def listCons : Program 2 := .comp .succ (fun _ => squarePair)

def list {r : ℕ} : List (Program r) → Program r
  | [] => constant 0
  | p :: ps => .comp listCons ![p, list ps]

def syntaxNode {r : ℕ} (tag : ℕ) (args : List (Program r)) : Program r :=
  .comp listCons ![constant tag, list args]

def implication : Program 2 := syntaxNode 6 [.proj 0, .proj 1]

/-- The actual `numeralCode 0 1`, with its zero and successor symbol codes. -/
def numeral : Program 1 :=
  .prec (syntaxNode 2 [constant 0]) (syntaxNode 2 [constant 1, .proj 1])

@[simp] theorem constant_eval {r : ℕ} (n : ℕ) (x : Fin r → ℕ) :
    (constant n).eval x = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [constant, Program.eval, ih]

@[simp] theorem addition_eval (x : Fin 2 → ℕ) : addition.eval x = x 0 + x 1 := by
  change primitiveRec (fun v => v 0) (fun v => v 2 + 1)
    (fun i : Fin 1 => x i.castSucc) (x 1) = _
  generalize x 1 = n
  induction n with
  | zero => rfl
  | succ n ih => simp [primitiveRec, ih, Fin.snoc, Nat.add_assoc]

@[simp] theorem multiplication_eval (x : Fin 2 → ℕ) :
    multiplication.eval x = x 0 * x 1 := by
  change primitiveRec _ _
    (fun i : Fin 1 => x i.castSucc) (x 1) = _
  have hs : (Program.comp addition ![.proj (2 : Fin 3), .proj 0]).eval =
      fun v => v 2 + v 0 := by
    funext v
    simp [Program.eval]
  have hb : (constant 0 : Program 1).eval = fun _ => 0 := by
    funext v
    exact constant_eval 0 v
  rw [hs, hb]
  generalize x 1 = n
  induction n with
  | zero => rfl
  | succ n ih => simp [primitiveRec, ih, Nat.mul_succ, Fin.snoc]

@[simp] theorem predecessor_eval (x : Fin 1 → ℕ) :
    predecessor.eval x = x 0 - 1 := by
  change primitiveRec (fun _ => 0) (fun v => v 0)
    (fun i : Fin 0 => x i.castSucc) (x 0) = _
  generalize x 0 = n
  cases n with
  | zero => rfl
  | succ n => simp [primitiveRec, Fin.snoc]

@[simp] theorem subtraction_eval (x : Fin 2 → ℕ) :
    subtraction.eval x = x 0 - x 1 := by
  change primitiveRec _ _
    (fun i : Fin 1 => x i.castSucc) (x 1) = _
  have hs : (Program.comp predecessor ![.proj (2 : Fin 3)]).eval =
      fun v => v 2 - 1 := by
    funext v
    simp [Program.eval]
  rw [hs]
  change primitiveRec (fun v => v 0) (fun v => v 2 - 1)
    (fun i : Fin 1 => x i.castSucc) (x 1) = _
  generalize x 1 = n
  induction n with
  | zero => rfl
  | succ n ih => simp [primitiveRec, ih, Nat.sub_sub, Fin.snoc]

@[simp] theorem sign_eval (x : Fin 1 → ℕ) :
    sign.eval x = if x 0 = 0 then 0 else 1 := by
  change primitiveRec (fun _ => 0) (fun _ => 1)
    (fun i : Fin 0 => x i.castSucc) (x 0) = _
  generalize x 0 = n
  cases n <;> simp [primitiveRec]

@[simp] theorem zeroTest_eval (x : Fin 1 → ℕ) :
    zeroTest.eval x = if x 0 = 0 then 1 else 0 := by
  change primitiveRec (fun _ => 1) (fun _ => 0)
    (fun i : Fin 0 => x i.castSucc) (x 0) = _
  generalize x 0 = n
  cases n <;> simp [primitiveRec]

@[simp] theorem less_eval (x : Fin 2 → ℕ) :
    less.eval x = if x 0 < x 1 then 1 else 0 := by
  simp only [less, Program.eval, sign_eval, subtraction_eval,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  split_ifs <;> omega

@[simp] theorem select_eval (x : Fin 3 → ℕ) :
    select.eval x = if x 0 = 0 then x 2 else x 1 := by
  simp only [select, Program.eval, addition_eval, multiplication_eval, sign_eval,
    zeroTest_eval, Matrix.cons_val_zero, Matrix.cons_val_one]
  split_ifs <;> simp

@[simp] theorem squarePair_eval (x : Fin 2 → ℕ) :
    squarePair.eval x = Nat.pair (x 0) (x 1) := by
  simp only [squarePair, Program.eval, select_eval, addition_eval, multiplication_eval,
    less_eval, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.head_cons, Nat.pair]
  split_ifs <;> simp_all

@[simp] theorem listCons_eval (x : Fin 2 → ℕ) :
    listCons.eval x = FiniteSequenceCoding.cons (x 0) (x 1) := by
  simp [listCons, Program.eval, FiniteSequenceCoding.cons, Nat.add_comm]

@[simp] theorem list_eval {r : ℕ} (ps : List (Program r)) (x : Fin r → ℕ) :
    (list ps).eval x = FiniteSequenceCoding.code (ps.map (fun p => p.eval x)) := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp only [list, Program.eval, listCons_eval, Matrix.cons_val_zero,
      Matrix.cons_val_one, List.map_cons, FiniteSequenceCoding.code_cons, ih]

@[simp] theorem syntaxNode_eval {r : ℕ} (tag : ℕ) (args : List (Program r))
    (x : Fin r → ℕ) :
    (syntaxNode tag args).eval x = node tag (args.map (fun p => p.eval x)) := by
  simp [syntaxNode, Program.eval, node, FiniteSequenceCoding.cons]

@[simp] theorem implication_eval (x : Fin 2 → ℕ) :
    implication.eval x = impCode (x 0) (x 1) := by
  simp [implication, impCode, Program.eval]

@[simp] theorem numeral_eval (x : Fin 1 → ℕ) :
    numeral.eval x = numeralCode 0 1 (x 0) := by
  change primitiveRec _ _ (fun i : Fin 0 => x i.castSucc) (x 0) = _
  generalize x 0 = n
  induction n with
  | zero => simp [primitiveRec, numeralCode]
  | succ n ih => simp [primitiveRec, ih, numeralCode, Program.eval, Fin.snoc]

section Internal
variable {M : Type u} [language.Structure M] [M ⊨ PA]

omit [language.Structure M] [M ⊨ PA] in
private theorem snoc_empty (a : M) : Fin.snoc (Fin.elim0 : Fin 0 → M) a = ![a] := by
  funext i
  fin_cases i
  rfl

@[simp] theorem constant_value {r : ℕ} (n : ℕ) (x : Fin r → M) :
    (constant n).value x = numeralValue M n := by
  induction n with
  | zero => simp only [constant, Program.value_comp, Program.value_zero, numeral_value_zero]
  | succ n ih =>
    simp only [constant, Program.value_comp, Program.value_succ, ih, numeral_value_succ]

theorem addition_value (a b : M) : addition.value ![a, b] = addValue M a b := by
  have hi : ∀ b : M,
      addition.value (Fin.snoc (fun _ : Fin 1 => a) b) = addValue M a b := by
    apply definable_induction
    · change DPred (fun v : Fin 1 → M =>
        addition.value (Fin.snoc (fun _ : Fin 1 => a) (v 0)) = addValue M a (v 0))
      apply dp_eq
      · apply (addition.value_definable (M := M)).comp
        intro i
        fin_cases i
        · simpa [Fin.snoc] using (df_const (α := Fin 1) a)
        · simpa [Fin.snoc] using (df_proj (M := M) (0 : Fin 1))
      · exact df_add _ _ (df_const a) (df_proj 0)
    · rw [addition, Program.value_rec_zero, Program.value_proj, add_zero_value]
    · intro k hk
      change (Program.prec _ _).value _ = _
      rw [Program.value_rec_succ, Program.value_comp, Program.value_succ]
      simp only [Program.value_proj, Fin.snoc] at *
      exact (congrArg (succValue M) hk).trans (add_successor_value a k).symm
  have hv : (![a, b] : Fin 2 → M) = Fin.snoc (fun _ : Fin 1 => a) b := by
    funext i
    fin_cases i <;> rfl
  rw [hv]
  exact hi b

theorem multiplication_value (a b : M) :
    multiplication.value ![a, b] = mulValue M a b := by
  have hi : ∀ b : M,
      multiplication.value (Fin.snoc (fun _ : Fin 1 => a) b) = mulValue M a b := by
    apply definable_induction
    · change DPred (fun v : Fin 1 → M =>
        multiplication.value (Fin.snoc (fun _ : Fin 1 => a) (v 0)) = mulValue M a (v 0))
      apply dp_eq
      · apply (multiplication.value_definable (M := M)).comp
        intro i
        fin_cases i
        · simpa [Fin.snoc] using (df_const (α := Fin 1) a)
        · simpa [Fin.snoc] using (df_proj (M := M) (0 : Fin 1))
      · exact df_mul _ _ (df_const a) (df_proj 0)
    · rw [multiplication, Program.value_rec_zero, constant_value,
        numeral_value_zero, mul_zero_value]
    · intro k hk
      change (Program.prec _ _).value _ = _
      rw [Program.value_rec_succ, Program.value_comp]
      have htuple : (fun i : Fin 2 =>
          (![Program.proj 2, Program.proj 0] i).value
            (Fin.snoc (Fin.snoc (fun _ : Fin 1 => a) k)
              (multiplication.value (Fin.snoc (fun _ : Fin 1 => a) k)))) =
          ![multiplication.value (Fin.snoc (fun _ : Fin 1 => a) k), a] := by
        funext i
        fin_cases i <;> simp [Program.value_proj, Fin.snoc]
      change addition.value (fun i : Fin 2 =>
        (![Program.proj 2, Program.proj 0] i).value
          (Fin.snoc (Fin.snoc (fun _ : Fin 1 => a) k)
            (multiplication.value (Fin.snoc (fun _ : Fin 1 => a) k)))) = _
      rw [htuple, addition_value, hk, mul_successor_value]
  have hv : (![a, b] : Fin 2 → M) = Fin.snoc (fun _ : Fin 1 => a) b := by
    funext i
    fin_cases i <;> rfl
  rw [hv]
  exact hi b

theorem predecessor_zero : predecessor.value ![zeroValue M] = zeroValue M := by
  have h := Program.value_rec_zero Program.zero (Program.proj (0 : Fin 2))
    (Fin.elim0 : Fin 0 → M)
  have hv : Fin.snoc (Fin.elim0 : Fin 0 → M) (zeroValue M) = ![zeroValue M] := by
    funext i
    fin_cases i
    rfl
  rw [hv] at h
  simpa [predecessor, Program.value_zero] using h

theorem predecessor_successor (a : M) : predecessor.value ![succValue M a] = a := by
  have h := Program.value_rec_succ Program.zero (Program.proj (0 : Fin 2))
    (Fin.elim0 : Fin 0 → M) a
  have hv : Fin.snoc (Fin.elim0 : Fin 0 → M) (succValue M a) = ![succValue M a] := by
    funext i
    fin_cases i
    rfl
  rw [hv] at h
  simpa [predecessor, Program.value_proj, Fin.snoc] using h

theorem list_nil_value {r : ℕ} (x : Fin r → M) :
    (list []).value x = zeroValue M := by
  exact (constant_value 0 x).trans (numeral_value_zero M)

theorem list_cons_value {r : ℕ} (p : Program r) (ps : List (Program r)) (x : Fin r → M) :
    (list (p :: ps)).value x = listCons.value ![p.value x, (list ps).value x] := by
  rw [list, Program.value_comp]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem syntaxNode_value {r : ℕ} (tag : ℕ) (args : List (Program r)) (x : Fin r → M) :
    (syntaxNode tag args).value x = listCons.value ![numeralValue M tag, (list args).value x] := by
  rw [syntaxNode, Program.value_comp]
  congr 1
  funext i
  fin_cases i
  · exact constant_value tag x
  · rfl

theorem implication_value (a b : M) :
    implication.value ![a, b] = listCons.value ![numeralValue M 6,
      listCons.value ![a, listCons.value ![b, zeroValue M] ] ] := by
  simp only [implication, syntaxNode_value, list_cons_value, list_nil_value,
    Program.value_proj, Matrix.cons_val_zero, Matrix.cons_val_one]

theorem numeral_zero_value :
    numeral.value ![zeroValue M] = numeralValue M (numeralCode 0 1 0) := by
  have h := numeral.value_numerals (M := M) ![0]
  have hx : (fun i : Fin 1 => numeralValue M (![0] i)) = ![zeroValue M] := by
    funext i
    fin_cases i
    exact numeral_value_zero M
  simpa only [hx, numeral_eval, Matrix.cons_val_zero] using h

theorem numeral_successor_value (n : M) :
    numeral.value ![succValue M n] = listCons.value ![numeralValue M 2,
      listCons.value ![numeralValue M 1,
        listCons.value ![numeral.value ![n], zeroValue M] ] ] := by
  have h := Program.value_rec_succ (syntaxNode 2 [constant 0])
    (syntaxNode 2 [constant 1, Program.proj (1 : Fin 2)]) (Fin.elim0 : Fin 0 → M) n
  rw [snoc_empty, snoc_empty] at h
  simpa [numeral, syntaxNode_value, list_cons_value, list_nil_value,
    constant_value, Program.value_proj, Fin.snoc] using h

end Internal

end
end Lemmatheca.MathematicalLogic.PAComputations.ProofPrograms
