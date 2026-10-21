import Lemmatheca.BoundedArithmeticProofs.PABoundedUniversalCorrectness

open Lemmatheca.MathematicalLogic Lemmatheca.ModelTheory Lemmatheca.ComputabilityTheory

/-! One-slot shared-checker formula contexts for transporting a bounded
quantifier from a numerical value back to its original closed bound term. -/
namespace Lemmatheca.ProofTheory.PAComputations.ProofPrograms.CheckerPrograms.BoundTermTransport
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic ArithmeticTheories ArithmeticRepresentability
open SyntaxPrograms FixedSyntaxPrograms InitialSegmentPrograms BoundedUniversalPrograms
noncomputable section
universe u

def orderTermCode {r : ℕ} (offset : ℕ) (s t : Program r) : Program r :=
  exCode (equalCode (syntaxNode 2 [constant 2, syntaxNode 1 [constant offset], s]) t)

def signedCode {r : ℕ} (negative : Bool) (a : Program r) : Program r :=
  if negative then negCode a else a

def boundedTermCode (universal negative : Bool) : Program 2 :=
  let body : Program 2 := .proj 0
  let bound : Program 2 := .proj 1
  let order := orderTermCode 1 (syntaxNode 1 [constant 0]) bound
  signedCode negative (if universal then allCode (impCode order body) else exCode (andCode order body))

def quantifiedBoundHole (universal negative : Bool) : Program 1 :=
  let body : Program 1 := .proj 0
  let order := orderTermCode 2 (syntaxNode 1 [constant 1]) (syntaxNode 1 [constant 0])
  signedCode negative (if universal then allCode (impCode order body) else exCode (andCode order body))

section Internal
variable {M : Type u} [language.Structure M] [M ⊨ PA]

def orderTermValue (offset : ℕ) (s t : M) : M :=
  exValue (modelNode 4 [modelNode 2 [numeralValue M 2, modelNode 1 [numeralValue M offset], s], t])

def signedValue (negative : Bool) (a : M) : M := if negative then negValue a else a

def quantifiedValue (universal negative : Bool) (body bound : M) : M :=
  let order := orderTermValue 1 (modelNode 1 [zeroValue M]) bound
  signedValue negative (if universal then modelNode 7 [implication.value ![order, body] ]
    else exValue (andValue order body))

def holeValue (universal negative : Bool) (body : M) : M :=
  let order := orderTermValue 2 (modelNode 1 [numeralValue M 1]) (modelNode 1 [zeroValue M])
  signedValue negative (if universal then modelNode 7 [implication.value ![order, body] ]
    else exValue (andValue order body))

theorem orderTermCode_model_value {r : ℕ} (offset : ℕ) (s t : Program r) (x : Fin r → M) :
    (orderTermCode offset s t).value x = orderTermValue offset (s.value x) (t.value x) := by
  simp only [orderTermCode, exCode_value, equalCode_value, syntaxNode_model_value,
    List.map_cons, List.map_nil, constant_value, orderTermValue]

theorem signedCode_model_value {r : ℕ} (negative : Bool) (a : Program r) (x : Fin r → M) :
    (signedCode negative a).value x = signedValue negative (a.value x) := by
  cases negative <;> simp only [signedCode, Bool.false_eq_true, ↓reduceIte,
    negCode_value, signedValue]

theorem boundedTermCode_model_value (universal negative : Bool) (body bound : M) :
    (boundedTermCode universal negative).value ![body, bound] =
      quantifiedValue universal negative body bound := by
  cases universal <;>
    simp only [boundedTermCode, signedCode_model_value, Bool.false_eq_true, ↓reduceIte,
      allCode_value, exCode_value, andCode_value, impCode, binary_value, orderTermCode_model_value,
      syntaxNode_model_value, List.map_cons, List.map_nil, constant_value, numeral_value_zero,
      Program.value_proj, Matrix.cons_val_zero, Matrix.cons_val_one, quantifiedValue]

theorem quantifiedBoundHole_model_value (universal negative : Bool) (body : M) :
    (quantifiedBoundHole universal negative).value ![body] = holeValue universal negative body := by
  cases universal <;>
    simp only [quantifiedBoundHole, signedCode_model_value, Bool.false_eq_true, ↓reduceIte,
      allCode_value, exCode_value, andCode_value, impCode, binary_value, orderTermCode_model_value,
      syntaxNode_model_value, List.map_cons, List.map_nil, constant_value, numeral_value_zero,
      Program.value_proj, Matrix.cons_val_zero, holeValue]

theorem formulaBound_neg {k : ℕ} {a : M} (ha : FormulaBound k a) : FormulaBound k (negValue a) := by
  rw [negValue, implication_node_value]
  exact ha.imp (FormulaBound.bottom k)

theorem formulaBound_and {k : ℕ} {a b : M} (ha : FormulaBound k a) (hb : FormulaBound k b) :
    FormulaBound k (andValue a b) := by
  rw [andValue]
  apply formulaBound_neg
  rw [implication_node_value]
  exact ha.imp (formulaBound_neg hb)

theorem formulaBound_ex {k : ℕ} {a : M} (ha : FormulaBound (k + 1) a) : FormulaBound k (exValue a) :=
  formulaBound_neg (FormulaBound.all (formulaBound_neg ha))

theorem formulaBound_signed {k : ℕ} (negative : Bool) {a : M} (ha : FormulaBound k a) :
    FormulaBound k (signedValue negative a) := by
  cases negative
  · exact ha
  · exact formulaBound_neg ha

theorem orderTermValue_bound (offset : ℕ) (s t : M)
    (hs : TermBound offset s) (ht : TermBound offset t) : FormulaBound offset (orderTermValue offset s t) := by
  apply formulaBound_ex
  apply FormulaBound.equal
  · exact TermBound.binary 2 (Or.inl rfl)
      (TermBound.bound (offset + 1) ⟨offset, by omega⟩) (hs.mono (by omega))
  · exact ht.mono (by omega)

theorem quantifiedBoundHole_bound (universal negative : Bool) (body : M) (hb : FormulaBound 2 body) :
    FormulaBound 1 ((quantifiedBoundHole universal negative).value ![body]) := by
  rw [quantifiedBoundHole_model_value]
  apply formulaBound_signed
  have horder : FormulaBound 2
      (orderTermValue 2 (modelNode 1 [numeralValue M 1]) (modelNode 1 [zeroValue M])) := by
    apply orderTermValue_bound
    · exact TermBound.bound 2 (1 : Fin 2)
    · simpa only [Fin.val_zero, numeral_value_zero] using TermBound.bound (M := M) 2 (0 : Fin 2)
  cases universal
  · exact formulaBound_ex (formulaBound_and horder hb)
  · apply FormulaBound.all
    rw [implication_node_value]
    exact horder.imp hb

theorem rewrite_slot_and_value (i t a b : M) :
    rewrite.value ![numeralValue M 2, i, t, andValue a b] =
      andValue (rewrite.value ![numeralValue M 2, i, t, a])
        (rewrite.value ![numeralValue M 2, i, t, b]) := by
  simp only [andValue, negValue, implication_node_value, rewrite_slot_imp_value]
  rw [rewrite_slot_nonleaf_value 3 (by decide) (by decide) (by decide)]
  rfl

theorem rewrite_slot_ex_value (i t a : M) :
    rewrite.value ![numeralValue M 2, i, t, exValue a] =
      exValue (rewrite.value ![numeralValue M 2, i, t, a]) := by
  rw [exValue, rewrite_slot_neg_value, rewrite_slot_all_value, rewrite_slot_neg_value]
  rfl

theorem rewrite_slot_signed_value (negative : Bool) (i t a : M) :
    rewrite.value ![numeralValue M 2, i, t, signedValue negative a] =
      signedValue negative (rewrite.value ![numeralValue M 2, i, t, a]) := by
  cases negative
  · rfl
  · exact rewrite_slot_neg_value i t a

theorem orderTermValue_rewrite (offset : ℕ) (i t s u : M) :
    rewrite.value ![numeralValue M 2, i, t, orderTermValue (offset + 1) s u] =
      orderTermValue offset (rewrite.value ![numeralValue M 2, i, t, s])
        (rewrite.value ![numeralValue M 2, i, t, u]) := by
  rw [orderTermValue, rewrite_slot_ex_value, rewrite_slot_equal_value,
    rewrite_slot_nonleaf_value 2 (by decide) (by decide) (by decide)]
  change exValue (modelNode 4 [modelNode 2 [numeralValue M 2,
    rewrite.value ![numeralValue M 2, i, t, modelNode 1 [numeralValue M (offset + 1)] ],
    rewrite.value ![numeralValue M 2, i, t, s] ],
    rewrite.value ![numeralValue M 2, i, t, u] ]) = _
  rw [numeral_value_succ M offset, rewrite_slot_bound_successor_value]
  rfl

theorem quantifiedBoundHole_instantiate (universal negative : Bool) (shifted normal t : M)
    (hb : FormulaBound 2 shifted) (ht : PureTerm t)
    (hr : rewrite.value ![numeralValue M 2, zeroValue M, t, shifted] = normal) :
    instantiate.value ![(quantifiedBoundHole universal negative).value ![shifted], t] =
      quantifiedValue universal negative normal t := by
  rw [instantiate_value_of_tests _ _ (quantifiedBoundHole_bound universal negative shifted hb).namedForm ht.namedTerm,
    quantifiedBoundHole_model_value]
  unfold holeValue quantifiedValue
  rw [rewrite_slot_signed_value]
  cases universal
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [rewrite_slot_ex_value, rewrite_slot_and_value, orderTermValue_rewrite 1,
      numeral_value_succ M 0, numeral_value_zero, rewrite_slot_bound_successor_value,
      rewrite_slot_bound_zero_value, hr]
  · simp only [↓reduceIte]
    rw [rewrite_slot_all_value]
    simp only [implication_node_value]
    rw [rewrite_slot_imp_value, orderTermValue_rewrite 1,
      numeral_value_succ M 0, numeral_value_zero, rewrite_slot_bound_successor_value,
      rewrite_slot_bound_zero_value, hr]

theorem upperValue_orderTermValue (offset : ℕ) (z n : M) :
    upperValue offset z n = orderTermValue offset z (ProofPrograms.numeral.value ![n]) := by
  unfold upperValue upperFormula leFormula
  rw [modelFormulaCodeAt_iExs_unit]
  simp only [Term.equal, Term.bdEqual, modelFormulaCodeAt, modelTermCode_relabel, addTerm, modelTermCode,
    CodingFormalProofs.arithFunctionCode, List.ofFn_succ, List.ofFn_zero,
    Function.comp_def, Sum.elim_inl, Sum.elim_inr, Fin.succ_zero_eq_one,
    Matrix.cons_val_zero, Matrix.cons_val_one,
    orderTermValue, exValue, negValue, implication_node_value]

theorem quantifiedValue_universal_numeral (body n : M) :
    quantifiedValue true false body (ProofPrograms.numeral.value ![n]) =
      modelNode 7 [matrixValue body n] := by
  simp only [quantifiedValue, signedValue, Bool.false_eq_true, ↓reduceIte, matrixValue,
    upperValue_orderTermValue]

theorem quantifiedValue_existential_numeral (body n : M) :
    quantifiedValue false false body (ProofPrograms.numeral.value ![n]) =
      exValue (andValue (upperValue 1 (modelNode 1 [zeroValue M]) n) body) := by
  simp only [quantifiedValue, signedValue, Bool.false_eq_true, ↓reduceIte,
    upperValue_orderTermValue]

theorem quantifiedValue_pure (universal negative : Bool) (body t : M)
    (hb : FormulaBound 1 body) (ht : PureTerm t) :
    PureFormula (quantifiedValue universal negative body t) := by
  apply FormulaBound.pure
  apply formulaBound_signed
  have horder : FormulaBound 1 (orderTermValue 1 (modelNode 1 [zeroValue M]) t) :=
    orderTermValue_bound 1 _ t bound_zero_termBound (ht.termBound 1)
  cases universal
  · exact formulaBound_ex (formulaBound_and horder hb)
  · apply FormulaBound.all
    rw [implication_node_value]
    exact horder.imp hb

end Internal
end
end Lemmatheca.ProofTheory.PAComputations.ProofPrograms.CheckerPrograms.BoundTermTransport
