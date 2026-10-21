import Lemmatheca.PaListsAndSyntax.PAListPrograms

open Lemmatheca.MathematicalLogic Lemmatheca.ModelTheory Lemmatheca.ComputabilityTheory

/-! Concrete course-of-values recursion over the corpus's numerical list codes.
The history is appended in increasing index order.  The programs retain the
parameters as inputs, and their equations hold in arbitrary PA models. -/
namespace Lemmatheca.ProofTheory.PAComputations.ProofPrograms
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic ArithmeticTheories ArithmeticRepresentability
noncomputable section
universe u

/-- The step sees the fixed parameters, the current index, and the prior history. -/
def historyStep {n : ℕ} (h : Program (n + 2)) : Program (n + 2) :=
  .comp listAppend ![.proj (Fin.last (n + 1)),
    .comp listCons ![h, constant 0] ]

def history {n : ℕ} (h : Program (n + 2)) : Program (n + 1) :=
  .prec (constant 0) (historyStep h)

def courseValue {n : ℕ} (h : Program (n + 2)) : Program (n + 1) :=
  .comp h (Fin.snoc (fun i : Fin (n + 1) => Program.proj i) (history h))

section Internal
variable {M : Type u} [language.Structure M] [M ⊨ PA]

theorem history_zero_value {n : ℕ} (h : Program (n + 2)) (x : Fin n → M) :
    (history h).value (Fin.snoc x (zeroValue M)) = zeroValue M := by
  rw [history, Program.value_rec_zero, constant_value, numeral_value_zero]

theorem history_successor_value {n : ℕ} (h : Program (n + 2)) (x : Fin n → M) (k : M) :
    (history h).value (Fin.snoc x (succValue M k)) =
      listAppend.value ![(history h).value (Fin.snoc x k),
        listCons.value ![h.value (Fin.snoc (Fin.snoc x k) ((history h).value (Fin.snoc x k))),
          zeroValue M] ] := by
  rw [history, Program.value_rec_succ]
  simp only [historyStep, Program.value_comp_two, Program.value_proj,
    Fin.snoc_last, constant_value, numeral_value_zero]

theorem courseValue_value {n : ℕ} (h : Program (n + 2)) (x : Fin n → M) (k : M) :
    (courseValue h).value (Fin.snoc x k) =
      h.value (Fin.snoc (Fin.snoc x k) ((history h).value (Fin.snoc x k))) := by
  rw [courseValue, Program.value_comp]
  congr 1
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Fin.snoc_last]
  · simp only [Fin.snoc_castSucc, Program.value_proj]

end Internal

local instance historyProgramsLocalInstance1 : ℕ ⊨ PA := nat_models_PA
private theorem zero_value_nat : zeroValue ℕ = 0 := rfl
private theorem succ_value_nat (n : ℕ) : succValue ℕ n = n + 1 := rfl

theorem history_eval {n : ℕ} (h : Program (n + 2)) (x : Fin n → ℕ) (k : ℕ) :
    (history h).eval (Fin.snoc x k) =
      FiniteSequenceCoding.historyCode (fun i hist => h.eval (Fin.snoc (Fin.snoc x i) hist)) k := by
  induction k with
  | zero =>
    simpa only [value_nat_eq_eval, zero_value_nat, FiniteSequenceCoding.historyCode] using history_zero_value (M := ℕ) h x
  | succ k ih =>
    have hs := history_successor_value (M := ℕ) h x k
    simp only [value_nat_eq_eval, succ_value_nat, listAppend_eval, listCons_eval,
      Matrix.cons_val_zero, Matrix.cons_val_one, zero_value_nat] at hs
    rw [hs, ih]
    rfl

theorem courseValue_eval {n : ℕ} (h : Program (n + 2)) (x : Fin n → ℕ) (k : ℕ) :
    (courseValue h).eval (Fin.snoc x k) =
      FiniteSequenceCoding.historyValue (fun i hist => h.eval (Fin.snoc (Fin.snoc x i) hist)) k := by
  have hs := courseValue_value (M := ℕ) h x k
  simp only [value_nat_eq_eval] at hs
  rw [hs, history_eval]
  rfl

end
end Lemmatheca.ProofTheory.PAComputations.ProofPrograms
