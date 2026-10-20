import Lemmatheca.MathematicalLogic.PANumericalOrder

/-! Actual native equality substitution into positive and negative order
formulas. The outer substitution slot and the inner difference slot are distinct. -/
namespace Lemmatheca.MathematicalLogic.PAComputations.ProofPrograms.CheckerPrograms.NumericalProofs
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic ArithmeticTheories ArithmeticRepresentability
open SyntaxPrograms FixedSyntaxPrograms LogicalProofs
noncomputable section
universe u

def orderTransport (left negative : Bool) : Program 5 :=
  let body := if left then orderAtOneCode boundZero (.proj 4)
    else orderAtOneCode (.proj 2) boundZero
  .comp equalitySubstitutionCertificate ![.proj 0, .proj 1,
    if negative then negCode body else body,
    if left then .proj 2 else .proj 3, if left then .proj 3 else .proj 4]

section Internal
variable {M : Type u} [language.Structure M] [M ⊨ PA]

def signedOrder (negative : Bool) (a b : M) : M :=
  if negative then negValue (orderValue a b) else orderValue a b

def orderHole (left negative : Bool) (a c : M) : M :=
  let body := if left then orderAtOneValue (modelNode 1 [zeroValue M]) c
    else orderAtOneValue a (modelNode 1 [zeroValue M])
  if negative then negValue body else body

theorem orderAtOneRightHole_bound {a : M} (ha : PureTerm a) :
    FormulaBound 1 (orderAtOneValue a (modelNode 1 [zeroValue M])) := by
  have hleft : TermBound 2 (modelNode 1 [numeralValue M 1]) := TermBound.bound 2 (1 : Fin 2)
  have hright : TermBound 2 (modelNode 1 [zeroValue M]) := by
    simpa only [Fin.val_zero, numeral_value_zero] using TermBound.bound (M := M) 2 (0 : Fin 2)
  have heq := FormulaBound.equal (TermBound.binary 2 (Or.inl rfl) hleft (ha.termBound 2)) hright
  exact negation_bound (negation_bound heq).all

theorem rewrite_orderAtOneRightHole {a t : M} (ha : PureTerm a) :
    rewrite.value ![numeralValue M 2, zeroValue M, t,
      orderAtOneValue a (modelNode 1 [zeroValue M])] = orderValue a t := by
  have hbot : rewrite.value ![numeralValue M 2, zeroValue M, t, modelNode 3 [] ] =
      modelNode 3 ([] : List M) := by
    rw [rewrite_slot_nonleaf_value 3 (by decide) (by decide) (by decide)]
    rfl
  have hbound : rewrite.value ![numeralValue M 2, zeroValue M, t,
      modelNode 1 [numeralValue M 1] ] = modelNode 1 [zeroValue M] := by
    have hn : numeralValue M 1 = succValue M (zeroValue M) := by
      rw [numeral_value_succ, numeral_value_zero]
    rw [hn, rewrite_slot_bound_successor_value]
  simp only [orderAtOneValue, exValue, negValue, implication_node]
  rw [rewrite_slot_imp_value, rewrite_slot_all_value, rewrite_slot_imp_value,
    rewrite_slot_equal_value,
    rewrite_slot_nonleaf_value 2 (by decide) (by decide) (by decide)]
  change modelNode 6 [modelNode 7 [modelNode 6 [modelNode 4
    [modelNode 2 [numeralValue M 2,
      rewrite.value ![numeralValue M 2, zeroValue M, t, modelNode 1 [numeralValue M 1] ],
      rewrite.value ![numeralValue M 2, zeroValue M, t, a] ],
      rewrite.value ![numeralValue M 2, zeroValue M, t, modelNode 1 [zeroValue M] ] ],
      rewrite.value ![numeralValue M 2, zeroValue M, t, modelNode 3 [] ] ] ],
      rewrite.value ![numeralValue M 2, zeroValue M, t, modelNode 3 [] ] ] = _
  rw [hbound, rewrite_slot_bound_zero_value, ha.2, hbot]
  simp only [orderValue, orderBodyValue, exValue, negValue, implication_node]

theorem orderHole_bound (left negative : Bool) {a c : M} (ha : PureTerm a) (hc : PureTerm c) :
    FormulaBound 1 (orderHole left negative a c) := by
  cases left <;> cases negative
  · exact orderAtOneRightHole_bound ha
  · exact negation_bound (orderAtOneRightHole_bound ha)
  · exact orderAtOneHole_bound hc
  · exact negation_bound (orderAtOneHole_bound hc)

theorem rewrite_orderHole (left negative : Bool) {a c t : M} (ha : PureTerm a) (hc : PureTerm c) :
    rewrite.value ![numeralValue M 2, zeroValue M, t, orderHole left negative a c] =
      signedOrder negative (if left then t else a) (if left then c else t) := by
  have hbot : rewrite.value ![numeralValue M 2, zeroValue M, t, modelNode 3 [] ] =
      modelNode 3 ([] : List M) := by
    rw [rewrite_slot_nonleaf_value 3 (by decide) (by decide) (by decide)]
    rfl
  cases left <;> cases negative
  · exact rewrite_orderAtOneRightHole ha
  · change rewrite.value ![numeralValue M 2, zeroValue M, t,
      negValue (orderAtOneValue a (modelNode 1 [zeroValue M]))] = negValue (orderValue a t)
    simp only [negValue, implication_node]
    rw [rewrite_slot_imp_value, rewrite_orderAtOneRightHole ha, hbot]
  · exact rewrite_orderAtOneHole hc
  · change rewrite.value ![numeralValue M 2, zeroValue M, t,
      negValue (orderAtOneValue (modelNode 1 [zeroValue M]) c)] = negValue (orderValue t c)
    simp only [negValue, implication_node]
    rw [rewrite_slot_imp_value, rewrite_orderAtOneHole hc, hbot]

theorem instantiate_orderHole (left negative : Bool) {a c t : M}
    (ha : PureTerm a) (hc : PureTerm c) (ht : PureTerm t) :
    instantiate.value ![orderHole left negative a c, t] =
      signedOrder negative (if left then t else a) (if left then c else t) := by
  rw [instantiate_value_of_tests _ _ (orderHole_bound left negative ha hc).namedForm ht.namedTerm,
    rewrite_orderHole left negative ha hc]

theorem signedOrder_pure (negative : Bool) {a b : M} (ha : PureTerm a) (hb : PureTerm b) :
    PureFormula (signedOrder negative a b) := by
  cases negative
  · exact orderValue_pure ha hb
  · exact pure_negation (orderValue_pure ha hb)

theorem orderTransport_value (left negative : Bool) (p q a b c : M) :
    (orderTransport left negative).value ![p, q, a, b, c] =
      equalitySubstitutionCertificate.value ![p, q, orderHole left negative a c,
        if left then a else b, if left then b else c] := by
  rw [orderTransport, Program.value_comp]
  congr 1
  funext i
  cases left <;> cases negative <;> fin_cases i <;>
    simp [Program.value_proj, negCode_value, orderAtOneCode_value, boundZero,
      syntaxNode_value, list_cons_value, list_nil_value, constant_value, numeral_value_zero,
      orderHole, modelNode, modelList_cons, modelList_nil]

theorem certified_orderTransport (E : Program 2) (left negative : Bool) (p q a b c : M)
    (hp : Certified E p (modelNode 4 [if left then a else b, if left then b else c]))
    (hq : Certified E q (signedOrder negative a (if left then c else b)))
    (ha : PureTerm a) (hb : PureTerm b) (hc : PureTerm c) :
    Certified E ((orderTransport left negative).value ![p, q, a, b, c])
      (signedOrder negative (if left then b else a) c) := by
  have hs : PureTerm (if left then a else b) := by cases left <;> assumption
  have ht : PureTerm (if left then b else c) := by cases left <;> assumption
  have hsrc := instantiate_orderHole left negative ha hc hs
  have htgt := instantiate_orderHole left negative ha hc ht
  have hq' : Certified E q (instantiate.value
      ![orderHole left negative a c, if left then a else b]) := by
    rw [hsrc]
    cases left <;> exact hq
  have hout : isSentence.value ![instantiate.value
      ![orderHole left negative a c, if left then b else c] ] = numeralValue M 1 := by
    rw [htgt]
    apply PureFormula.sentence
    cases left
    · exact signedOrder_pure negative ha hc
    · exact signedOrder_pure negative hb hc
  rw [orderTransport_value]
  have h := certified_equalitySubstitution E p q (orderHole left negative a c)
    (if left then a else b) (if left then b else c) hp hq'
    (orderHole_bound left negative ha hc).namedForm hs.namedTerm ht.namedTerm hout
  rw [htgt] at h
  cases left <;> exact h

end Internal
end
end Lemmatheca.MathematicalLogic.PAComputations.ProofPrograms.CheckerPrograms.NumericalProofs
