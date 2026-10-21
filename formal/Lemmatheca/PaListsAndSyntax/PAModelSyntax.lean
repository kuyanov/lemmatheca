import Lemmatheca.PaListsAndSyntax.PAFixedSyntaxCorrectness
import Lemmatheca.PaListsAndSyntax.PANumeralCodes

open Lemmatheca.MathematicalLogic Lemmatheca.ModelTheory Lemmatheca.ComputabilityTheory

/-! The shared syntax interpreted by the actual internal syntax constructors.
This is a structural map from the existing AST, not a new formula language. -/
namespace Lemmatheca.ProofTheory.PAComputations.ProofPrograms.FixedSyntaxPrograms
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic ArithmeticTheories ArithmeticRepresentability
open SyntaxPrograms
noncomputable section
universe u
variable {M : Type u} [language.Structure M] [M ⊨ PA]

def modelTermCode {α : Type*} (name : α → M) : language.Term α → M
  | .var i => name i
  | .func f ts => modelNode 2 (numeralValue M (CodingFormalProofs.arithFunctionCode f) ::
      List.ofFn (fun i => modelTermCode name (ts i)))

def modelFormulaCodeAt {α : Type*} (name : α → M) (offset : ℕ) :
    {k : ℕ} → language.BoundedFormula α k → M
  | _, .falsum => modelNode 3 []
  | _, .equal s t => modelNode 4 [
      modelTermCode (Sum.elim name (fun i => modelNode 1 [numeralValue M (offset + i.val)])) s,
      modelTermCode (Sum.elim name (fun i => modelNode 1 [numeralValue M (offset + i.val)])) t]
  | _, .rel e _ => e.elim
  | _, .imp a b => modelNode 6 [modelFormulaCodeAt name offset a, modelFormulaCodeAt name offset b]
  | _, .all a => modelNode 7 [modelFormulaCodeAt name offset a]

theorem termCode_model_value {α : Type*} {r : ℕ} (name : α → Program r)
    (t : language.Term α) (x : Fin r → M) :
    (termCode name t).value x = modelTermCode (fun a => (name a).value x) t := by
  induction t with
  | var i => rfl
  | func f ts ih =>
    rw [termCode_value]
    simp only [modelTermCode]
    congr 2
    apply congrArg List.ofFn
    funext i
    exact ih i

theorem formulaCode_model_value {α : Type*} {r k : ℕ} (name : α → Program r)
    (A : language.BoundedFormula α k) (x : Fin r → M) :
    (formulaCode name A).value x = modelFormulaCodeAt (fun a => (name a).value x) 0 A := by
  have hn (k : ℕ) :
      (fun i : α ⊕ Fin k =>
        (Sum.elim name (fun i => syntaxNode 1 [constant i.val]) i).value x) =
      Sum.elim (fun a => (name a).value x) (fun i => modelNode 1 [numeralValue M (0 + i.val)]) := by
    funext i
    cases i with
    | inl i => rfl
    | inr i => simp only [Sum.elim_inr, syntaxNode_value, list_cons_value, constant_value,
        list_nil_value, modelNode, modelList_cons, modelList_nil, Nat.zero_add]
  induction A with
  | falsum => simp only [formulaCode, syntaxNode_value, list_nil_value, modelFormulaCodeAt,
      modelNode, modelList_nil]
  | equal s t => simp only [formulaCode, syntaxNode_value, list_cons_value, list_nil_value,
      termCode_model_value, hn, modelFormulaCodeAt, modelNode, modelList_cons, modelList_nil]
  | rel e _ => exact e.elim
  | imp a b ha hb => simp only [formulaCode, syntaxNode_value, list_cons_value, list_nil_value,
      ha, hb, modelFormulaCodeAt, modelNode, modelList_cons, modelList_nil]
  | all a ha => simp only [formulaCode, syntaxNode_value, list_cons_value, list_nil_value,
      ha, modelFormulaCodeAt, modelNode, modelList_cons, modelList_nil]

theorem rewrite_slot_modelTermCode {α : Type*} (name : α → M)
    (i t : M) (a : language.Term α) :
    rewrite.value ![numeralValue M 2, i, t, modelTermCode name a] =
      modelTermCode (fun j => rewrite.value ![numeralValue M 2, i, t, name j]) a := by
  induction a with
  | var j => rfl
  | func f ts ih =>
    rw [modelTermCode, rewrite_slot_nonleaf_value 2 (by decide) (by decide) (by decide)]
    simp only [true_or, ↓reduceIte, List.headD_cons, List.tail_cons,
      List.map_ofFn, Function.comp_def, modelTermCode]
    congr 2
    apply congrArg List.ofFn
    funext j
    exact ih j

theorem rewrite_slot_modelFormulaCodeAt {α : Type*} (name : α → M)
    (i t : M) (offset : ℕ) {k : ℕ} (A : language.BoundedFormula α k) :
    rewrite.value ![numeralValue M 2, i, t, modelFormulaCodeAt name (offset + 1) A] =
      modelFormulaCodeAt
        (fun a => rewrite.value ![numeralValue M 2, i, t, name a]) offset A := by
  have hn (k : ℕ) :
      (fun j : α ⊕ Fin k => rewrite.value ![numeralValue M 2, i, t,
        Sum.elim name (fun j => modelNode 1 [numeralValue M (offset + 1 + j.val)]) j]) =
      Sum.elim (fun a => rewrite.value ![numeralValue M 2, i, t, name a])
        (fun j => modelNode 1 [numeralValue M (offset + j.val)]) := by
    funext j
    cases j with
    | inl j => rfl
    | inr j =>
      simp only [Sum.elim_inr]
      have hj : numeralValue M (offset + 1 + j.val) =
          succValue M (numeralValue M (offset + j.val)) := by
        rw [show offset + 1 + j.val = (offset + j.val) + 1 by omega, numeral_value_succ]
      rw [hj, rewrite_slot_bound_successor_value]
  induction A with
  | falsum =>
    rw [modelFormulaCodeAt, rewrite_slot_nonleaf_value 3 (by decide) (by decide) (by decide)]
    rfl
  | equal a b =>
    rw [modelFormulaCodeAt, rewrite_slot_equal_value, rewrite_slot_modelTermCode,
      rewrite_slot_modelTermCode, hn]
    rfl
  | rel e _ => exact e.elim
  | imp a b ha hb => rw [modelFormulaCodeAt, rewrite_slot_imp_value, ha, hb]; rfl
  | all a ha => rw [modelFormulaCodeAt, rewrite_slot_all_value, ha]; rfl

theorem modelTermCode_relabel {α β : Type*} (name : β → M) (f : α → β)
    (t : language.Term α) :
    modelTermCode name (t.relabel f) = modelTermCode (name ∘ f) t := by
  induction t with
  | var i => rfl
  | func g ts ih =>
    simp only [Term.relabel, modelTermCode]
    congr 2
    apply congrArg List.ofFn
    funext i
    exact ih i

theorem modelTermCode_subst {α β : Type*} (name : β → M) (s : α → language.Term β)
    (t : language.Term α) :
    modelTermCode name (t.subst s) =
      modelTermCode (fun a => modelTermCode name (s a)) t := by
  induction t with
  | var i => rfl
  | func g ts ih =>
    simp only [Term.subst, modelTermCode]
    congr 2
    apply congrArg List.ofFn
    funext i
    exact ih i

theorem modelFormulaCodeAt_subst {α β : Type*} (name : β → M)
    (offset : ℕ) (s : α → language.Term β) {k : ℕ} (A : language.BoundedFormula α k) :
    modelFormulaCodeAt name offset (A.subst s) =
      modelFormulaCodeAt (fun a => modelTermCode name (s a)) offset A := by
  have hn (k : ℕ) :
      (fun j : α ⊕ Fin k => modelTermCode
        (Sum.elim name (fun j => modelNode 1 [numeralValue M (offset + j.val)]))
        (Sum.elim (Term.relabel Sum.inl ∘ s) (Term.var ∘ Sum.inr) j)) =
      Sum.elim (fun a => modelTermCode name (s a))
        (fun j => modelNode 1 [numeralValue M (offset + j.val)]) := by
    funext j
    cases j with
    | inl j => simp only [Sum.elim_inl, Function.comp_apply, modelTermCode_relabel,
        Sum.elim_comp_inl]
    | inr j => rfl
  induction A with
  | falsum => rfl
  | equal a b => simp only [BoundedFormula.subst, BoundedFormula.mapTermRel,
      modelFormulaCodeAt, modelTermCode_subst, hn]
  | rel e _ => exact e.elim
  | imp a b ha hb =>
    change modelNode 6 [modelFormulaCodeAt name offset (a.subst s),
      modelFormulaCodeAt name offset (b.subst s)] = _
    rw [ha, hb]
    rfl
  | all a ha =>
    change modelNode 7 [modelFormulaCodeAt name offset (a.subst s)] = _
    rw [ha]
    rfl

theorem modelTermCode_numerals {α : Type*} (name : α → ℕ) (t : language.Term α) :
    modelTermCode (fun a => numeralValue M (name a)) t =
      numeralValue M (CodingFormalProofs.termCode CodingFormalProofs.arithmeticSignature name t) := by
  induction t with
  | var i => rfl
  | func f ts ih =>
    rw [modelTermCode, CodingFormalProofs.termCode]
    have he : (numeralValue M (CodingFormalProofs.arithFunctionCode f) ::
        List.ofFn (fun i => modelTermCode (fun a => numeralValue M (name a)) (ts i))) =
        (CodingFormalProofs.arithFunctionCode f :: List.ofFn
          (fun i => CodingFormalProofs.termCode CodingFormalProofs.arithmeticSignature name (ts i))).map
          (numeralValue M) := by
      simp only [List.map_cons, List.map_ofFn, Function.comp_def]
      congr 1
      apply congrArg List.ofFn
      funext i
      exact ih i
    rw [he, CheckerPrograms.modelNode_numerals]
    rfl

theorem modelFormulaCodeAt_numerals {α : Type*} (name : α → ℕ)
    (offset : ℕ) {k : ℕ} (A : language.BoundedFormula α k) :
    modelFormulaCodeAt (fun a => numeralValue M (name a)) offset A =
      numeralValue M (CodingFormalProofs.codeAt CodingFormalProofs.arithmeticSignature name offset A) := by
  have hn (k : ℕ) :
      Sum.elim (fun a => numeralValue M (name a))
        (fun j : Fin k => modelNode 1 [numeralValue M (offset + j.val)]) =
      (fun j : α ⊕ Fin k => numeralValue M
        (Sum.elim name (fun j => CodingFormalProofs.boundName (offset + j.val)) j)) := by
    funext j
    cases j with
    | inl j => rfl
    | inr j =>
      simpa only [Sum.elim_inr, List.map_cons, List.map_nil, CodingFormalProofs.boundName]
        using CheckerPrograms.modelNode_numerals (M := M) 1 [offset + j.val]
  have hn0 : modelNode (M := M) 3 [] = numeralValue M (CodingFormalProofs.node 3 []) :=
    CheckerPrograms.modelNode_numerals 3 []
  have hn1 (j : ℕ) (a : ℕ) : modelNode j [numeralValue M a] =
      numeralValue M (CodingFormalProofs.node j [a]) :=
    CheckerPrograms.modelNode_numerals j [a]
  have hn2 (j : ℕ) (a b : ℕ) : modelNode j [numeralValue M a, numeralValue M b] =
      numeralValue M (CodingFormalProofs.node j [a, b]) :=
    CheckerPrograms.modelNode_numerals j [a, b]
  induction A with
  | falsum => exact hn0
  | equal s t =>
    simp only [modelFormulaCodeAt, hn, modelTermCode_numerals, hn2,
      CodingFormalProofs.codeAt, CodingFormalProofs.equalCode]
  | rel e _ => exact e.elim
  | imp a b ha hb => simp only [modelFormulaCodeAt, ha, hb, hn2,
      CodingFormalProofs.codeAt, CodingFormalProofs.impCode]
  | all a ha => simp only [modelFormulaCodeAt, ha, hn1,
      CodingFormalProofs.codeAt, CodingFormalProofs.allCode]

theorem modelFormulaCodeAt_zero_numerals {α : Type*} (name : α → ℕ)
    {k : ℕ} (A : language.BoundedFormula α k) :
    modelFormulaCodeAt (fun a => numeralValue M (name a)) 0 A =
      numeralValue M (CodingFormalProofs.formulaCode CodingFormalProofs.arithmeticSignature name A) := by
  rw [modelFormulaCodeAt_numerals, CodingFormalProofs.codeAt_zero]

theorem modelFormulaCodeAt_cast {α : Type*} (name : α → M) (offset : ℕ)
    {m n : ℕ} (h : m ≤ n) (A : language.BoundedFormula α m) :
    modelFormulaCodeAt name offset (A.castLE h) = modelFormulaCodeAt name offset A := by
  have hn (m n : ℕ) (h : m ≤ n) :
      (Sum.elim name (fun i : Fin n => modelNode 1 [numeralValue M (offset + i.val)])) ∘
        Sum.map id (Fin.castLE h) =
      Sum.elim name (fun i : Fin m => modelNode 1 [numeralValue M (offset + i.val)]) := by
    funext i
    cases i <;> rfl
  induction A generalizing n with
  | falsum => rfl
  | equal s t => simp only [BoundedFormula.castLE, modelFormulaCodeAt,
      modelTermCode_relabel, hn]
  | rel e _ => exact e.elim
  | imp a b ha hb =>
    simpa only [BoundedFormula.castLE, modelFormulaCodeAt] using
      congrArg (fun xs => modelNode 6 xs) (congrArg₂ (fun a b => [a, b]) (ha h) (hb h))
  | all a ha =>
    simpa only [BoundedFormula.castLE, modelFormulaCodeAt] using
      congrArg (fun a => modelNode 7 [a]) (ha (Nat.succ_le_succ h))

theorem modelFormulaCodeAt_relabel {α β : Type*} (name : β → M) (offset : ℕ)
    {m n : ℕ} (f : α → β ⊕ Fin m) (A : language.BoundedFormula α n) :
    modelFormulaCodeAt name offset (A.relabel f) =
      modelFormulaCodeAt
        (fun a => Sum.elim name (fun i => modelNode 1 [numeralValue M (offset + i.val)]) (f a))
        (offset + m) A := by
  have hn (k : ℕ) :
      (Sum.elim name (fun i : Fin (m + k) => modelNode 1 [numeralValue M (offset + i.val)])) ∘
        BoundedFormula.relabelAux f k =
      Sum.elim
        (fun a => Sum.elim name (fun i => modelNode 1 [numeralValue M (offset + i.val)]) (f a))
        (fun i : Fin k => modelNode 1 [numeralValue M (offset + m + i.val)]) := by
    funext i
    cases i with
    | inl a => cases h : f a <;> simp [BoundedFormula.relabelAux, h]
    | inr i => simp [BoundedFormula.relabelAux, Nat.add_assoc]
  induction A with
  | falsum => rfl
  | equal s t => simp only [BoundedFormula.relabel, BoundedFormula.mapTermRel,
      modelFormulaCodeAt, modelTermCode_relabel, hn]
  | rel e _ => exact e.elim
  | imp a b ha hb => simp only [BoundedFormula.relabel_imp, modelFormulaCodeAt, ha, hb]
  | all a ha =>
    simp only [BoundedFormula.relabel, BoundedFormula.mapTermRel, modelFormulaCodeAt,
      modelFormulaCodeAt_cast]
    exact congrArg (fun a => modelNode 7 [a]) ha

theorem modelFormulaCodeAt_iAlls_unit {α : Type*} (name : α → M) (offset : ℕ)
    (A : language.Formula (α ⊕ Unit)) :
    modelFormulaCodeAt name offset (A.iAlls Unit) = modelNode 7
      [modelFormulaCodeAt (Sum.elim name (fun _ => modelNode 1 [numeralValue M offset]))
        (offset + 1) A] := by
  have aux (n : ℕ) (e : Unit ≃ Fin n) :
      modelFormulaCodeAt name offset ((BoundedFormula.relabel (Sum.map id e) A).alls) = modelNode 7
        [modelFormulaCodeAt (Sum.elim name (fun _ => modelNode 1 [numeralValue M offset]))
          (offset + 1) A] := by
    have hn : n = 1 := by simpa only [Fintype.card_fin, Fintype.card_unique] using
      (Fintype.card_congr e).symm
    subst n
    change modelNode 7 [modelFormulaCodeAt name offset (BoundedFormula.relabel (Sum.map id e) A)] = _
    rw [modelFormulaCodeAt_relabel]
    apply congrArg (fun name => modelNode 7 [modelFormulaCodeAt name (offset + 1) A])
    funext a
    cases a with
    | inl a => rfl
    | inr a => simp only [Sum.map_inr, Sum.elim_inr, Fin.val_eq_zero (e a), Nat.add_zero]
  exact aux _ _

theorem modelFormulaCodeAt_iExs_unit {α : Type*} (name : α → M) (offset : ℕ)
    (A : language.Formula (α ⊕ Unit)) :
    modelFormulaCodeAt name offset (A.iExs Unit) = modelNode 6 [modelNode 7
      [modelNode 6 [modelFormulaCodeAt
        (Sum.elim name (fun _ => modelNode 1 [numeralValue M offset])) (offset + 1) A,
        modelNode 3 [] ] ], modelNode 3 [] ] := by
  have aux (n : ℕ) (e : Unit ≃ Fin n) :
      modelFormulaCodeAt name offset ((BoundedFormula.relabel (Sum.map id e) A).exs) =
        modelNode 6 [modelNode 7 [modelNode 6
          [modelFormulaCodeAt (Sum.elim name (fun _ => modelNode 1 [numeralValue M offset]))
            (offset + 1) A, modelNode 3 [] ] ], modelNode 3 [] ] := by
    have hn : n = 1 := by simpa only [Fintype.card_fin, Fintype.card_unique] using
      (Fintype.card_congr e).symm
    subst n
    change modelNode 6 [modelNode 7 [modelNode 6
      [modelFormulaCodeAt name offset (BoundedFormula.relabel (Sum.map id e) A),
        modelNode 3 [] ] ], modelNode 3 [] ] = _
    rw [modelFormulaCodeAt_relabel]
    apply congrArg (fun name => modelNode 6 [modelNode 7 [modelNode 6
      [modelFormulaCodeAt name (offset + 1) A, modelNode 3 [] ] ], modelNode 3 [] ])
    funext a
    cases a with
    | inl a => rfl
    | inr a => simp only [Sum.map_inr, Sum.elim_inr, Fin.val_eq_zero (e a), Nat.add_zero]
  exact aux _ _

end
end Lemmatheca.ProofTheory.PAComputations.ProofPrograms.FixedSyntaxPrograms
