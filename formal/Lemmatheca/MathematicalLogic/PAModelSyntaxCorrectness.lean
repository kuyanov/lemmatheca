import Lemmatheca.MathematicalLogic.PAModelSyntax
import Lemmatheca.MathematicalLogic.PAFixedFormulaCorrectness

/-! Named syntax bounds for scalar interpretations of the shared AST.
Auxiliary constants remain available, and offset bound slots are tracked
through nested quantifiers. -/
namespace Lemmatheca.MathematicalLogic.PAComputations.ProofPrograms.FixedSyntaxPrograms
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic ArithmeticTheories ArithmeticRepresentability
open SyntaxPrograms
noncomputable section
universe u
variable {M : Type u} [language.Structure M] [M ⊨ PA]

theorem TermBound.mono {k l : ℕ} {a : M} (ha : TermBound k a) (hkl : k ≤ l) :
    TermBound l a := by
  obtain ⟨d, hd, hdk, hs⟩ := ha
  let := PA_models_Q M
  have hkl' : leValue M (numeralValue M (k + 1)) (numeralValue M (l + 1)) :=
    (finite_bound _ (l + 1)).mpr ⟨k + 1, by omega, rfl⟩
  exact ⟨d, hd, le_trans_value hdk hkl', hs⟩

theorem modelTermCode_bound {α : Type*} {k : ℕ} (name : α → M)
    (hn : ∀ i, TermBound k (name i)) (t : language.Term α) :
    TermBound k (modelTermCode name t) := by
  induction t with
  | var i => exact hn i
  | func f ts ih =>
    rw [modelTermCode]
    cases f with
    | zero => simpa only [CodingFormalProofs.arithFunctionCode, List.ofFn_zero,
        numeral_value_zero] using (PureTerm.zero (M := M)).termBound k
    | succ => simpa only [CodingFormalProofs.arithFunctionCode, List.ofFn_succ,
        List.ofFn_zero] using (TermBound.succ (ih 0))
    | add => simpa only [CodingFormalProofs.arithFunctionCode, List.ofFn_succ,
        List.ofFn_zero, Fin.succ_zero_eq_one] using
        (TermBound.binary 2 (Or.inl rfl) (ih 0) (ih 1))
    | mul => simpa only [CodingFormalProofs.arithFunctionCode, List.ofFn_succ,
        List.ofFn_zero, Fin.succ_zero_eq_one] using
        (TermBound.binary 3 (Or.inr rfl) (ih 0) (ih 1))

theorem modelFormulaCodeAt_bound {α : Type*} (name : α → M) (offset : ℕ)
    (hn : ∀ i, TermBound offset (name i)) {k : ℕ}
    (A : language.BoundedFormula α k) :
    FormulaBound (offset + k) (modelFormulaCodeAt name offset A) := by
  have hname (k : ℕ) (i : α ⊕ Fin k) :
      TermBound (offset + k)
        (Sum.elim name (fun j => modelNode 1 [numeralValue M (offset + j.val)]) i) := by
    cases i with
    | inl i => exact (hn i).mono (by omega)
    | inr i => exact TermBound.bound (M := M) (offset + k) ⟨offset + i.val, by omega⟩
  induction A with
  | falsum => exact FormulaBound.bottom _
  | equal s t =>
    exact FormulaBound.equal (modelTermCode_bound _ (hname _) s) (modelTermCode_bound _ (hname _) t)
  | rel e _ => exact e.elim
  | imp a b iha ihb => exact FormulaBound.imp iha ihb
  | all a ih =>
    apply FormulaBound.all
    simpa only [Nat.add_assoc] using ih

theorem modelTermCode_namedBound {α : Type*} {k : ℕ} (name : α → M)
    (hn : ∀ i, NamedTermBound k (name i)) (t : language.Term α) :
    NamedTermBound k (modelTermCode name t) := by
  induction t with
  | var i => exact hn i
  | func f ts ih =>
    rw [modelTermCode]
    cases f with
    | zero => simpa only [CodingFormalProofs.arithFunctionCode, List.ofFn_zero,
        numeral_value_zero] using ((PureTerm.zero (M := M)).termBound k).named
    | succ => simpa only [CodingFormalProofs.arithFunctionCode, List.ofFn_succ,
        List.ofFn_zero] using (NamedTermBound.succ (ih 0))
    | add => simpa only [CodingFormalProofs.arithFunctionCode, List.ofFn_succ,
        List.ofFn_zero, Fin.succ_zero_eq_one] using
        (NamedTermBound.binary 2 (Or.inl rfl) (ih 0) (ih 1))
    | mul => simpa only [CodingFormalProofs.arithFunctionCode, List.ofFn_succ,
        List.ofFn_zero, Fin.succ_zero_eq_one] using
        (NamedTermBound.binary 3 (Or.inr rfl) (ih 0) (ih 1))

theorem modelFormulaCodeAt_namedBound {α : Type*} (name : α → M) (offset : ℕ)
    (hn : ∀ i, NamedTermBound offset (name i)) {k : ℕ}
    (A : language.BoundedFormula α k) :
    NamedFormulaBound (offset + k) (modelFormulaCodeAt name offset A) := by
  have hname (k : ℕ) (i : α ⊕ Fin k) :
      NamedTermBound (offset + k)
        (Sum.elim name (fun j => modelNode 1 [numeralValue M (offset + j.val)]) i) := by
    cases i with
    | inl i => exact (hn i).mono (by omega)
    | inr i => exact (TermBound.bound (M := M) (offset + k) ⟨offset + i.val, by omega⟩).named
  induction A with
  | falsum => exact NamedFormulaBound.bottom _
  | equal s t =>
    exact NamedFormulaBound.equal
      (modelTermCode_namedBound _ (hname _) s) (modelTermCode_namedBound _ (hname _) t)
  | rel e _ => exact e.elim
  | imp a b iha ihb => exact NamedFormulaBound.imp iha ihb
  | all a ih =>
    apply NamedFormulaBound.all
    simpa only [Nat.add_assoc] using ih

theorem modelFormulaCodeAt_namedForm {α : Type*} (name : α → M) (offset : ℕ)
    (hn : ∀ i, NamedTermBound offset (name i)) {k : ℕ}
    (A : language.BoundedFormula α k) :
    CheckerPrograms.namedForm.value ![numeralValue M (offset + k),
      modelFormulaCodeAt name offset A] = numeralValue M 1 :=
  (modelFormulaCodeAt_namedBound name offset hn A).namedForm

end
end Lemmatheca.MathematicalLogic.PAComputations.ProofPrograms.FixedSyntaxPrograms
