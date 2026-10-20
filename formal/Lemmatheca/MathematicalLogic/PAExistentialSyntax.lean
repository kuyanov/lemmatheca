import Lemmatheca.MathematicalLogic.PAExistentialProofPrograms
import Lemmatheca.MathematicalLogic.PAModelSyntaxCorrectness

/-! Literal finite existential prefixes, including the enumeration actually
chosen by the shared `iExs` syntax operation. -/
namespace Lemmatheca.MathematicalLogic.PAComputations.ProofPrograms.CheckerPrograms
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic ArithmeticTheories ArithmeticRepresentability
open SyntaxPrograms FixedSyntaxPrograms
noncomputable section
universe u
variable {M : Type u} [language.Structure M] [M ⊨ PA]

private theorem implication_node (a b : M) :
    implication.value ![a, b] = modelNode 6 [a, b] := by
  rw [implication_value]
  rfl

def modelExPrefix : ℕ → M → M
  | 0, a => a
  | k + 1, a => modelExPrefix k (exValue a)

theorem modelExPrefix_succ (k : ℕ) (a : M) :
    modelExPrefix (k + 1) a = exValue (modelExPrefix k a) := by
  induction k generalizing a with
  | zero => rfl
  | succ k ih => exact ih (exValue a)

private theorem modelFormulaCodeAt_ex {α : Type*} (name : α → M)
    (offset : ℕ) {k : ℕ} (A : language.BoundedFormula α (k + 1)) :
    modelFormulaCodeAt name offset A.ex = exValue (modelFormulaCodeAt name offset A) := by
  simp only [modelFormulaCodeAt,
    exValue, negValue, implication_node]

 theorem modelFormulaCodeAt_exs {α : Type*} (name : α → M)
    (offset : ℕ) {k : ℕ} (A : language.BoundedFormula α k) :
    modelFormulaCodeAt name offset A.exs = modelExPrefix k (modelFormulaCodeAt name offset A) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [BoundedFormula.exs, ih, modelFormulaCodeAt_ex]
    rfl

theorem modelFormulaCodeAt_iExs {α β : Type*} {n : ℕ}
    (e : β ≃ Fin n) (name : α → M) (offset : ℕ)
    (A : language.Formula (α ⊕ β)) :
    modelFormulaCodeAt name offset
      ((BoundedFormula.relabel (Sum.map id e) A).exs) =
      modelExPrefix n (modelFormulaCodeAt
        (Sum.elim name (fun i => modelNode 1 [numeralValue M (offset + (e i).val)]))
        (offset + n) A) := by
  rw [modelFormulaCodeAt_exs, modelFormulaCodeAt_relabel, Nat.add_zero]
  congr 2
  funext i
  cases i <;> rfl

private theorem formulaBound_ex {k : ℕ} {a : M} (ha : FormulaBound (k + 1) a) :
    FormulaBound k (exValue a) := by
  simp only [exValue, negValue, implication_node]
  exact ((ha.imp (FormulaBound.bottom (k + 1))).all).imp (FormulaBound.bottom k)

theorem modelExPrefix_bound (k l : ℕ) (a : M) (ha : FormulaBound (k + l) a) :
    FormulaBound l (modelExPrefix k a) := by
  induction k generalizing a with
  | zero => simpa only [Nat.zero_add, modelExPrefix] using ha
  | succ k ih =>
    apply ih (exValue a)
    apply formulaBound_ex
    simpa only [Nat.succ_add, Nat.add_succ] using ha

private theorem rewrite_slot_ex (i t a : M) :
    rewrite.value ![numeralValue M 2, i, t, exValue a] =
      exValue (rewrite.value ![numeralValue M 2, i, t, a]) := by
  simp only [exValue, negValue, implication_node, rewrite_slot_imp_value,
    rewrite_slot_all_value, rewrite_slot_nonleaf_value 3 (by decide) (by decide) (by decide),
    List.map_nil]
  rfl

theorem rewrite_slot_modelExPrefix (k : ℕ) (i t a : M) :
    rewrite.value ![numeralValue M 2, i, t, modelExPrefix k a] =
      modelExPrefix k (rewrite.value ![numeralValue M 2, i, t, a]) := by
  induction k generalizing a with
  | zero => rfl
  | succ k ih => rw [modelExPrefix, ih, rewrite_slot_ex]; rfl

/-- At stage j the earlier witnesses are numerals, and the remaining variables
are precisely the pending bound slots. -/
def prefixName {r n : ℕ} (x : Fin r → M) (y : Fin n → M) (j : ℕ) : Fin r ⊕ Fin n → M :=
  Sum.elim (fun i => ProofPrograms.numeral.value ![x i])
    (fun i => if i.val < j then ProofPrograms.numeral.value ![y i]
      else modelNode 1 [numeralValue M (i.val - j)])

theorem prefixName_bound {r n : ℕ} (x : Fin r → M) (y : Fin n → M)
    (j : ℕ) (hj : j ≤ n) (i : Fin r ⊕ Fin n) :
    TermBound (n - j) (prefixName x y j i) := by
  cases i with
  | inl i => exact (PureTerm.numeral _).termBound _
  | inr i =>
    simp only [prefixName, Sum.elim_inr]
    split_ifs with hi
    · exact (PureTerm.numeral _).termBound _
    · exact TermBound.bound _ ⟨i.val - j, by omega⟩

theorem prefixName_rewrite {r n : ℕ} (x : Fin r → M) (y : Fin n → M)
    (j : Fin n) (i : Fin r ⊕ Fin n) :
    rewrite.value ![numeralValue M 2, zeroValue M, ProofPrograms.numeral.value ![y j],
      prefixName x y j.val i] = prefixName x y (j.val + 1) i := by
  cases i with
  | inl i => exact rewrite_slot_numeral_value _ _ _
  | inr i =>
    simp only [prefixName, Sum.elim_inr]
    by_cases hij : i.val < j.val
    · simp only [hij, show i.val < j.val + 1 by omega, ↓reduceIte,
        rewrite_slot_numeral_value]
    · by_cases heq : i = j
      · subst i
        simp only [lt_self_iff_false, ↓reduceIte, Nat.sub_self, numeral_value_zero,
          rewrite_slot_bound_zero_value, Nat.lt_succ_self]
      · have hgt : j.val < i.val := by
          have hne : i.val ≠ j.val := fun h => heq (Fin.ext h)
          omega
        simp only [hij, show ¬ i.val < j.val + 1 by omega, ↓reduceIte]
        have hslot : numeralValue M (i.val - j.val) =
            succValue M (numeralValue M (i.val - (j.val + 1))) := by
          rw [show i.val - j.val = (i.val - (j.val + 1)) + 1 by omega, numeral_value_succ]
        rw [hslot, rewrite_slot_bound_successor_value]

end
end Lemmatheca.MathematicalLogic.PAComputations.ProofPrograms.CheckerPrograms
