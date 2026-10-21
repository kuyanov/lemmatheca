import Lemmatheca.PaListsAndSyntax.PASyntaxEvaluation
import Lemmatheca.PaProofCheckers.ArithmeticProofPredicatesPA

open Lemmatheca.MathematicalLogic Lemmatheca.ModelTheory Lemmatheca.ComputabilityTheory

/-! The explicit native program for PA axiom certificates. Every branch,
auxiliary-name binding traversal, and closing iteration is a fixed program DAG;
no program is selected merely by its behaviour on the standard natural numbers.
The checker preservation lemmas remain valid for an arbitrary verifier. -/
namespace Lemmatheca.ProofTheory.PAComputations.ProofPrograms.CheckerPrograms
open Lemmatheca.MathematicalLogic ArithmeticTheories
open CodingFormalProofs ArithmeticProofPredicates
open SyntaxPrograms
noncomputable section

namespace AxiomPrograms

/-- Bind auxiliary names and shift the pre-existing bound slots. Inputs are
 the name bound, the current syntax code, and the earlier-value history. -/
def bindStep (single : Bool) : Program 3 :=
  let k : Program 3 := .proj 0
  let e : Program 3 := .proj 1
  let hist : Program 3 := .proj 2
  let tg := unary tag e
  let first := unary (argument 0) e
  let bound (j : Program 3) := syntaxNode 1 [j]
  let choose := ternary select
  choose e
    (choose (binary equalTest tg (constant 8))
      (if single then choose (binary equalTest first k) (bound (constant 0)) e
       else bound first)
      (choose (binary equalTest tg (constant 1))
        (bound (binary addition first (if single then constant 1 else k)))
        (binary listCons tg
          (choose (binary disjoin (binary equalTest tg (constant 2))
              (binary equalTest tg (constant 5)))
            (binary listCons first
              (binary (listMap listEntry) hist (unary listTail (unary args e))))
            (binary (listMap listEntry) hist (unary args e))))))
    (constant 0)

def bindCode (single : Bool) : Program 2 := courseValue (bindStep single)

/-- Iterate the universal-quantifier constructor; inputs are the starting
formula and the number of quantifiers. -/
def closeIteration : Program 2 := .prec (.proj 0) (allCode (.proj 2))

def closeCode : Program 2 :=
  binary closeIteration (bindCode false) (.proj 0)

def allAuxCode : Program 2 := allCode (bindCode true)

def inductionCode : Program 2 :=
  let k : Program 2 := .proj 0
  let e : Program 2 := .proj 1
  let base := .comp rewrite ![constant 1, k,
    constant ArithmeticProofPredicates.arithmeticZeroCode, e]
  let stepTerm := syntaxNode 2 [constant 1, auxCode k]
  let step := .comp rewrite ![constant 1, k, stepTerm, e]
  binary closeCode k
    (impCode (andCode base (binary allAuxCode k (impCode e step)))
      (binary allAuxCode k e))

/-- Inputs are the proposed axiom code and its finite schema certificate.
The Robinson-axiom table is literal finite data; induction certificates use
 the native syntax recognizer and the native induction-code constructor. -/
def verifier : Program 2 :=
  let n : Program 2 := .proj 0
  let s : Program 2 := .proj 1
  let len := unary listLength s
  let i := binary listEntry s (constant 0)
  let k := binary listEntry s (constant 1)
  let e := binary listEntry s (constant 2)
  ternary select (binary equalTest len (constant 1))
    (conjunction [binary less i (constant 7),
      binary equalTest n (binary listEntry
        (constant (FiniteSequenceCoding.code ArithmeticProofPredicates.robinsonCodes)) i)])
    (ternary select (conjunction [binary equalTest len (constant 3),
        binary equalTest i (constant 7)])
      (conjunction [binary namedForm (constant 0) e,
        binary leq (unary (part 3) (unary stats e)) (unary .succ k),
        binary equalTest n (binary inductionCode k e)])
      (constant 0))


private theorem bindStep_eval (single : Bool) (x : Fin 3 → ℕ) :
    (bindStep single).eval x =
      ArithmeticProofPredicates.bindStep single (x 0) (x 1) (x 2) := by
  cases single <;>
    simp only [bindStep, ternary_eval, binary_eval, unary_eval, projection_eval,
      select_eval_values, equalTest_eval_values, disjoin_eval, constant_eval,
      tag_eval, argument_eval, args_eval, tail_eval, listMap_eval, listEntry_eval,
      listCons_eval, syntaxNode_eval, addition_eval,
      Matrix.cons_val_zero, Matrix.cons_val_one,
      List.map_cons, List.map_nil, Bool.false_eq_true, ↓reduceIte,
      FiniteSequenceCoding.tail_code, FiniteSequenceCoding.decode_code,
      ArithmeticProofPredicates.bindStep, flag, CodingFormalProofs.boundName,
      CodingFormalProofs.node, CodingFormalProofs.arg] <;>
    split_ifs <;> simp_all [FiniteSequenceCoding.cons, FiniteSequenceCoding.code, Nat.add_comm]

theorem bindCode_eval (single : Bool) (x : Fin 2 → ℕ) :
    (bindCode single).eval x = ArithmeticProofPredicates.bindCode single (x 0) (x 1) := by
  let p : Fin 1 → ℕ := ![x 0]
  have hx : Fin.snoc p (x 1) = x := by ext i; fin_cases i <;> rfl
  have hs : (fun i hist => (bindStep single).eval (Fin.snoc (Fin.snoc p i) hist)) =
      ArithmeticProofPredicates.bindStep single (x 0) := by
    funext i hist
    rw [bindStep_eval]
    rfl
  have he := courseValue_eval (bindStep single) p (x 1)
  rw [hx, hs] at he
  exact he

private theorem closeIteration_eval_values (e k : ℕ) :
    closeIteration.eval ![e, k] = (CodingFormalProofs.allCode^[k]) e := by
  let : ℕ ⊨ PA := nat_models_PA
  induction k with
  | zero => rfl
  | succ k ih =>
    have h := Program.value_rec_succ (M := ℕ) (Program.proj (0 : Fin 1))
      (allCode (Program.proj (2 : Fin 3))) (![e] : Fin 1 → ℕ) k
    simp only [Program.value_nat, allCode_eval, projection_eval,
      show (2 : Fin 3) = Fin.last 2 from rfl, Fin.snoc_last] at h
    have hvec (z : ℕ) : Fin.snoc (![e] : Fin 1 → ℕ) z = ![e, z] := by
      ext i; fin_cases i <;> rfl
    rw [hvec, hvec] at h
    change closeIteration.eval ![e, k + 1] =
      CodingFormalProofs.allCode (closeIteration.eval ![e, k]) at h
    rw [h, ih]
    exact (Function.iterate_succ_apply' _ _ _).symm

theorem closeCode_eval (x : Fin 2 → ℕ) :
    closeCode.eval x = ArithmeticProofPredicates.closeCode (x 0) (x 1) := by
  simp only [closeCode, binary_eval, bindCode_eval, projection_eval,
    closeIteration_eval_values, ArithmeticProofPredicates.closeCode]

theorem allAuxCode_eval (x : Fin 2 → ℕ) :
    allAuxCode.eval x = ArithmeticProofPredicates.allAuxCode (x 0) (x 1) := by
  simp only [allAuxCode, allCode_eval, bindCode_eval, ArithmeticProofPredicates.allAuxCode]


private theorem rewrite_comp_eval {n : ℕ} (a b c d : Program n) (x : Fin n → ℕ) :
    (Program.comp rewrite ![a, b, c, d]).eval x =
      CodingFormalProofs.rewrite (a.eval x) (b.eval x) (c.eval x) (d.eval x) := by
  change rewrite.eval (fun i => (![a, b, c, d] : Fin 4 → Program n) i |>.eval x) = _
  rw [rewrite_eval]
  rfl

theorem inductionCode_eval (x : Fin 2 → ℕ) :
    inductionCode.eval x = ArithmeticProofPredicates.inductionCode (x 0) (x 1) := by
  simp only [inductionCode, binary_eval, closeCode_eval, impCode_eval, andCode_eval,
    allAuxCode_eval, rewrite_comp_eval, projection_eval, constant_eval, syntaxNode_eval,
    auxCode_eval, List.map_cons, List.map_nil,
    Matrix.cons_val_zero, Matrix.cons_val_one,
    ArithmeticProofPredicates.inductionCode, ArithmeticProofPredicates.arithmeticSuccCode,
    CodingFormalProofs.arithFunctionCode]

private theorem leq_eval_values (a b : ℕ) : leq.eval ![a, b] = flag (a ≤ b) := by
  simp only [leq, Program.eval, zeroTest_eval, subtraction_eval,
    Matrix.cons_val_zero, Matrix.cons_val_one, Nat.sub_eq_zero_iff_le]
  rfl

private theorem less_eval_values (a b : ℕ) : less.eval ![a, b] = flag (a < b) := by
  rw [less_eval]
  rfl

private theorem successor_eval_value (a : ℕ) : Program.succ.eval ![a] = a + 1 := rfl

theorem verifier_eval (x : Fin 2 → ℕ) :
    verifier.eval x = if paAxiomCertificate (x 0) (x 1) then 1 else 0 := by
  simp only [verifier, ternary_eval, binary_eval, unary_eval, projection_eval,
    constant_eval, listLength_eval, listEntry_eval, equalTest_eval_values,
    select_eval_values, conjunction_eval, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    namedForm_eval, part_eval, stats_eval, leq_eval_values,
    less_eval_values, successor_eval_value, inductionCode_eval,
    Denumerable.ofNat_encode, coordinate3,
    Matrix.cons_val_zero, Matrix.cons_val_one, Nat.mul_one,
    flag, boolNat, FiniteSequenceCoding.length,
    FiniteSequenceCoding.entry, paAxiomCertificate]
  simp only [FiniteSequenceCoding.decode]
  split_ifs <;> simp_all <;> try omega
  all_goals try (split_ifs <;> simp_all)
  all_goals
    have hz : 0 < (Denumerable.ofNat (List ℕ) (x 1)).length := by omega
    simp_all only [List.getElem?_eq_getElem hz, Option.getD_some]


end AxiomPrograms

/-- The fixed explicit PA schema-certificate algorithm. -/
def axiomVerifier : Program 2 := AxiomPrograms.verifier

theorem axiomVerifier_eval (x : Fin 2 → ℕ) :
    axiomVerifier.eval x = if paAxiomCertificate (x 0) (x 1) then 1 else 0 :=
  AxiomPrograms.verifier_eval x

end
end Lemmatheca.ProofTheory.PAComputations.ProofPrograms.CheckerPrograms
