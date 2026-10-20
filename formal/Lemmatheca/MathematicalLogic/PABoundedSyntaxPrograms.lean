import Lemmatheca.MathematicalLogic.PAOrderAtomProofs
import Lemmatheca.MathematicalLogic.PABoundedUniversalCorrectness
import Lemmatheca.MathematicalLogic.PANativeNoAux
import Lemmatheca.MathematicalLogic.PABoundTermTransport

/-! Exact shared-syntax formula families for signed bounded proof construction. -/
namespace Lemmatheca.MathematicalLogic.PAComputations.ProofPrograms.CheckerPrograms.BoundedSyntaxPrograms
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic ArithmeticTheories ArithmeticRepresentability
open SyntaxPrograms FixedSyntaxPrograms NumericalProofs InitialSegmentPrograms
noncomputable section

def namedFormula {α : Type} {r : ℕ} (name : α → Program r) (D : language.Formula α) : Program r :=
  formulaCode (fun a => num (name a)) D

def slotFormula {α : Type} {r : ℕ} (offset : ℕ) (name : α → Program r)
    (D : language.Formula (α ⊕ Unit)) : Program r :=
  formulaCodeAt (Sum.elim (fun a => num (name a))
    (fun _ => syntaxNode 1 [constant offset])) (offset + 1) D

section Internal
variable {M : Type} [language.Structure M] [M ⊨ PA]

theorem namedFormula_value {α : Type} {r : ℕ} (name : α → Program r)
    (D : language.Formula α) (x : Fin r → M) :
    (namedFormula name D).value x =
      modelFormulaCodeAt (fun a => numeralSyntax ((name a).value x)) 0 D := by
  rw [namedFormula, formulaCode_model_value]
  congr 1
  funext a
  exact num_model_value _ _

theorem namedFormula_pure {α : Type} {r : ℕ} (name : α → Program r)
    (D : language.Formula α) (x : Fin r → M) : PureFormula ((namedFormula name D).value x) :=
  formulaCode_pure _ (fun _ _ => num_pure _ _) D x

theorem slotFormula_value {α : Type} {r : ℕ} (offset : ℕ) (name : α → Program r)
    (D : language.Formula (α ⊕ Unit)) (x : Fin r → M) :
    (slotFormula offset name D).value x =
      modelFormulaCodeAt (Sum.elim (fun a => numeralSyntax ((name a).value x))
        (fun _ : Unit => boundSyntax offset)) (offset + 1) D := by
  rw [slotFormula, formulaCodeAt_model_value]
  congr 1
  funext a
  cases a with
  | inl a => exact num_model_value _ _
  | inr a =>
    simp only [Sum.elim_inr, syntaxNode_value, list_cons_value, list_nil_value,
      constant_value, boundSyntax, modelNode, modelList_cons, modelList_nil]

theorem slotFormula_bound {α : Type} {r : ℕ} (offset : ℕ) (name : α → Program r)
    (D : language.Formula (α ⊕ Unit)) (x : Fin r → M) :
    FormulaBound (offset + 1) ((slotFormula offset name D).value x) := by
  rw [slotFormula_value]
  have hn (a : α ⊕ Unit) : TermBound (offset + 1)
      (Sum.elim (fun a => numeralSyntax ((name a).value x)) (fun _ : Unit => boundSyntax offset) a) := by
    cases a with
    | inl a => exact (PureTerm.numeral _).termBound _
    | inr a => exact TermBound.bound (offset + 1) (Fin.last offset)
  simpa only [Nat.add_zero] using modelFormulaCodeAt_bound _ (offset + 1) hn D

theorem noAux_of_formulaBound {k : ℕ} {e : M} (he : FormulaBound k e) (j : M) :
    occursAux.value ![j, e] = zeroValue M := by
  obtain ⟨d, hd, _, hs⟩ := he
  have hne : d ≠ zeroValue M := by
    intro hz
    rw [hz, numeral_value_succ, numeral_value_zero] at hd
    exact ((successor_le_iff_lt _ _).mp hd).2 (le_refl_value _)
  apply (recognized_noAux j e).2
  · simpa only [formDepth, hs, modelSummary_part_value, Matrix.cons_val_one,
      Matrix.cons_val_zero] using hne
  · simp only [statsPart, hs, modelSummary_part_value, Matrix.cons_val_three,
      Matrix.head_cons, Matrix.tail_cons]

theorem slotFormula_fresh {α : Type} {r : ℕ} (offset : ℕ) (name : α → Program r)
    (D : language.Formula (α ⊕ Unit)) (x : Fin r → M) (j : M) :
    occursAux.value ![j, (slotFormula offset name D).value x] = zeroValue M :=
  noAux_of_formulaBound (slotFormula_bound offset name D x) j

theorem slotFormula_instantiate {α : Type} {r : ℕ} (name : α → Program r)
    (D : language.Formula (α ⊕ Unit)) (x : Fin r → M) (t : M)
    (ht : namedTerm.value ![t] = numeralValue M 1) :
    instantiate.value ![(slotFormula 0 name D).value x, t] =
      modelFormulaCodeAt (Sum.elim (fun a => numeralSyntax ((name a).value x))
        (fun _ : Unit => t)) 0 D := by
  rw [instantiate_value_of_tests _ _ (slotFormula_bound 0 name D x).namedForm ht,
    slotFormula_value, rewrite_slot_modelFormulaCodeAt _ _ _ 0 D]
  congr 1
  funext a
  cases a with
  | inl a => exact (PureTerm.numeral _).2 _ _
  | inr a =>
    simp only [Sum.elim_inr, boundSyntax, numeral_value_zero]
    exact rewrite_slot_bound_zero_value _ _

theorem slotFormula_aux_named {α : Type} {r : ℕ} (name : α → Program r)
    (D : language.Formula (α ⊕ Unit)) (x : Fin r → M) (j : M) :
    NamedFormulaBound 0 (instantiate.value
      ![(slotFormula 0 name D).value x, modelNode 8 [j] ]) := by
  have ht : namedTerm.value ![modelNode 8 [j] ] = numeralValue M 1 := by
    apply namedTerm_of_stats _ _
    exact stats_aux_modelNode_value j
  rw [slotFormula_instantiate name D x _ ht]
  have hn (a : α ⊕ Unit) : NamedTermBound 0
      (Sum.elim (fun a => numeralSyntax ((name a).value x)) (fun _ : Unit => modelNode 8 [j]) a) := by
    cases a with
    | inl a => exact ((PureTerm.numeral _).termBound 0).named
    | inr a => exact NamedTermBound.aux 0 j
  simpa only [Nat.add_zero] using modelFormulaCodeAt_namedBound _ 0 hn D

theorem slotFormula_instantiate_numeral {α : Type} {r : ℕ} (name : α → Program r)
    (D : language.Formula (α ⊕ Unit)) (x : Fin r → M) (i : M) :
    instantiate.value ![(slotFormula 0 name D).value x, numeralSyntax i] =
      (namedFormula (BoundedTruthPrograms.extendName name) D).value (Fin.snoc x i) := by
  have ht : namedTerm.value ![numeralSyntax i] = numeralValue M 1 := (PureTerm.numeral i).namedTerm
  rw [slotFormula_instantiate name D x (numeralSyntax i) ht,
    namedFormula_value]
  congr 1
  funext a
  cases a with
  | inl a =>
    simp only [Sum.elim_inl, BoundedTruthPrograms.extendName, BoundedTruthPrograms.lift_value]
  | inr a =>
    simp only [Sum.elim_inr, BoundedTruthPrograms.extendName, Program.value_proj, Fin.snoc_last]

theorem slotFormula_shift_rewrite {α : Type} {r : ℕ} (name : α → Program r)
    (D : language.Formula (α ⊕ Unit)) (x : Fin r → M) (t : M) :
    rewrite.value ![numeralValue M 2, zeroValue M, t, (slotFormula 1 name D).value x] =
      (slotFormula 0 name D).value x := by
  rw [slotFormula_value, rewrite_slot_modelFormulaCodeAt _ _ _ 1 D, slotFormula_value]
  congr 1
  funext a
  cases a with
  | inl a => exact (PureTerm.numeral _).2 _ _
  | inr a =>
    change rewrite.value ![numeralValue M 2, zeroValue M, t, boundSyntax 1] = boundSyntax 0
    have hnum : numeralValue M 1 = succValue M (zeroValue M) := by
      rw [numeral_value_succ, numeral_value_zero]
    rw [boundSyntax, hnum, rewrite_slot_bound_successor_value, boundSyntax_zero]

theorem namedFormula_bot {α : Type} {r : ℕ} (name : α → Program r) (x : Fin r → M) :
    (namedFormula name (⊥ : language.Formula α)).value x = modelNode 3 [] := by
  rw [namedFormula_value]
  rfl

theorem namedFormula_equal {α : Type} {r : ℕ} (name : α → Program r)
    (s t : language.Term α) (x : Fin r → M) :
    (namedFormula name (s.equal t)).value x =
      modelNode 4 [(namedTermCode name s).value x, (namedTermCode name t).value x] := by
  rw [namedFormula_value, modelFormulaCodeAt_equal, namedTermCode_value, namedTermCode_value]

theorem namedFormula_le {α : Type} {r : ℕ} (name : α → Program r)
    (s t : language.Term α) (x : Fin r → M) :
    (namedFormula name (leFormula s t)).value x =
      orderValue ((namedTermCode name s).value x) ((namedTermCode name t).value x) := by
  rw [namedFormula_value, modelFormulaCodeAt_le, namedTermCode_value, namedTermCode_value]

theorem namedFormula_imp {α : Type} {r : ℕ} (name : α → Program r)
    (D F : language.Formula α) (x : Fin r → M) :
    (namedFormula name (D.imp F)).value x =
      implication.value ![(namedFormula name D).value x, (namedFormula name F).value x] := by
  rw [namedFormula_value, namedFormula_value, namedFormula_value, LogicalProofs.implication_node]
  rfl

theorem namedFormula_not {α : Type} {r : ℕ} (name : α → Program r)
    (D : language.Formula α) (x : Fin r → M) :
    (namedFormula name D.not).value x = negValue ((namedFormula name D).value x) := by
  change (namedFormula name (D.imp ⊥)).value x = _
  rw [namedFormula_imp, namedFormula_bot]
  rfl

theorem modelFormulaCodeAt_order_offset {α : Type} (name : α → M) (offset : ℕ)
    (s t : language.Term α) :
    modelFormulaCodeAt name offset (leFormula s t) =
      BoundTermTransport.orderTermValue offset (modelTermCode name s) (modelTermCode name t) := by
  rw [leFormula, modelFormulaCodeAt_iExs_unit]
  simp only [modelFormulaCodeAt_equal, modelTermCode_relabel, Function.comp_def,
    Sum.elim_inl, Sum.elim_inr, modelTermCode, addTerm, CodingFormalProofs.arithFunctionCode,
    List.ofFn_succ, List.ofFn_zero, Fin.succ_zero_eq_one,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  simp only [BoundTermTransport.orderTermValue, exValue, negValue, LogicalProofs.implication_node]

theorem modelFormulaCodeAt_and {α : Type} (name : α → M) (offset : ℕ)
    (A B : language.Formula α) :
    modelFormulaCodeAt name offset (A ⊓ B) =
      andValue (modelFormulaCodeAt name offset A) (modelFormulaCodeAt name offset B) := by
  change modelNode 6 [modelNode 6 [modelFormulaCodeAt name offset A,
    modelNode 6 [modelFormulaCodeAt name offset B, modelNode 3 [] ] ], modelNode 3 [] ] = _
  simp only [andValue, negValue, LogicalProofs.implication_node]

theorem namedFormula_boundedAll {α : Type} {r : ℕ} (name : α → Program r)
    (t : language.Term α) (D : language.Formula (α ⊕ Unit)) (x : Fin r → M) :
    (namedFormula name (boundedAll t D)).value x =
      BoundTermTransport.quantifiedValue true false ((slotFormula 0 name D).value x)
        ((namedTermCode name t).value x) := by
  rw [namedFormula_value, boundedAll, modelFormulaCodeAt_iAlls_unit]
  change modelNode 7 [modelNode 6 [modelFormulaCodeAt
    (Sum.elim (fun a => numeralSyntax ((name a).value x))
      (fun _ : Unit => modelNode 1 [numeralValue M 0])) 1
    (leFormula (.var (.inr ())) (t.relabel Sum.inl)),
    modelFormulaCodeAt (Sum.elim (fun a => numeralSyntax ((name a).value x))
      (fun _ : Unit => modelNode 1 [numeralValue M 0])) 1 D] ] = _
  rw [modelFormulaCodeAt_order_offset, slotFormula_value, namedTermCode_value]
  simp only [modelTermCode, modelTermCode_relabel, Function.comp_def, Sum.elim_inl,
    Sum.elim_inr, numeral_value_zero, boundSyntax_zero,
    BoundTermTransport.quantifiedValue, BoundTermTransport.signedValue,
    Bool.false_eq_true, ↓reduceIte, LogicalProofs.implication_node]

theorem namedFormula_boundedEx {α : Type} {r : ℕ} (name : α → Program r)
    (t : language.Term α) (D : language.Formula (α ⊕ Unit)) (x : Fin r → M) :
    (namedFormula name (boundedEx t D)).value x =
      BoundTermTransport.quantifiedValue false false ((slotFormula 0 name D).value x)
        ((namedTermCode name t).value x) := by
  rw [namedFormula_value, boundedEx, modelFormulaCodeAt_iExs_unit,
    modelFormulaCodeAt_and, modelFormulaCodeAt_order_offset,
    slotFormula_value, namedTermCode_value]
  simp only [modelTermCode, modelTermCode_relabel, Function.comp_def, Sum.elim_inl,
    Sum.elim_inr, numeral_value_zero, boundSyntax_zero,
    BoundTermTransport.quantifiedValue, BoundTermTransport.signedValue,
    Bool.false_eq_true, ↓reduceIte, exValue, negValue, LogicalProofs.implication_node]

end Internal
end
end Lemmatheca.MathematicalLogic.PAComputations.ProofPrograms.CheckerPrograms.BoundedSyntaxPrograms
