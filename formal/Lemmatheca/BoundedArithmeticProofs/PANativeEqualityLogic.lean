import Lemmatheca.BoundedArithmeticProofs.PANativeLogicalProofs
import Lemmatheca.BoundedArithmeticProofs.PANumericalProofCorrectness

open Lemmatheca.MathematicalLogic Lemmatheca.ModelTheory Lemmatheca.ComputabilityTheory

/-! Native equality and disequality transports for numerical normalization. -/
namespace Lemmatheca.ProofTheory.PAComputations.ProofPrograms.CheckerPrograms.NumericalProofs
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic ArithmeticTheories ArithmeticRepresentability
open SyntaxPrograms FixedSyntaxPrograms LogicalProofs
noncomputable section
universe u

def symmetry : Program 3 :=
  .comp equalitySubstitutionCertificate ![.proj 0,
    unary equalityReflexivityCertificate (.proj 1),
    equalCode boundZero (.proj 1), .proj 1, .proj 2]

/-- Inputs p,q,a,b,c: p proves b=c, q proves a≠b. -/
def notEqualRightTransport : Program 5 :=
  .comp equalitySubstitutionCertificate ![.proj 0, .proj 1,
    negCode (equalCode (.proj 2) boundZero), .proj 3, .proj 4]

/-- Inputs p,q,a,b,c: p proves a=b, q proves a≠c. -/
def notEqualLeftTransport : Program 5 :=
  .comp equalitySubstitutionCertificate ![.proj 0, .proj 1,
    negCode (equalCode boundZero (.proj 4)), .proj 2, .proj 3]

section Internal
variable {M : Type u} [language.Structure M] [M ⊨ PA]

theorem equalityHole_left_bound (a : M) (ha : PureTerm a) :
    FormulaBound 1 (modelNode 4 [modelNode 1 [zeroValue M], a]) := by
  apply FormulaBound.equal
  · simpa only [Fin.val_zero, numeral_value_zero] using TermBound.bound (M := M) 1 (0 : Fin 1)
  · exact ha.termBound 1

theorem equalityHole_right_bound (a : M) (ha : PureTerm a) :
    FormulaBound 1 (modelNode 4 [a, modelNode 1 [zeroValue M] ]) := by
  apply FormulaBound.equal (ha.termBound 1)
  simpa only [Fin.val_zero, numeral_value_zero] using TermBound.bound (M := M) 1 (0 : Fin 1)

theorem negation_bound {k : ℕ} {a : M} (ha : FormulaBound k a) : FormulaBound k (negValue a) := by
  rw [negValue, implication_node]
  exact ha.imp (FormulaBound.bottom k)

theorem instantiate_equality_left {a t : M} (ha : PureTerm a) (ht : PureTerm t) :
    instantiate.value ![modelNode 4 [modelNode 1 [zeroValue M], a], t] = modelNode 4 [t, a] := by
  rw [instantiate_value_of_tests _ _ (equalityHole_left_bound a ha).namedForm ht.namedTerm,
    rewrite_slot_equal_value, rewrite_slot_bound_zero_value, ha.2]

theorem instantiate_negated_equality_left {a t : M} (ha : PureTerm a) (ht : PureTerm t) :
    instantiate.value ![negValue (modelNode 4 [modelNode 1 [zeroValue M], a]), t] =
      negValue (modelNode 4 [t, a]) := by
  have hbody := (negation_bound (equalityHole_left_bound a ha)).namedForm
  rw [instantiate_value_of_tests _ _ hbody ht.namedTerm]
  simp only [negValue, implication_node]
  rw [rewrite_slot_imp_value, rewrite_slot_equal_value,
    rewrite_slot_bound_zero_value, ha.2,
    rewrite_slot_nonleaf_value 3 (by decide) (by decide) (by decide)]
  rfl

theorem instantiate_negated_equality_right {a t : M} (ha : PureTerm a) (ht : PureTerm t) :
    instantiate.value ![negValue (modelNode 4 [a, modelNode 1 [zeroValue M] ]), t] =
      negValue (modelNode 4 [a, t]) := by
  have hbody := (negation_bound (equalityHole_right_bound a ha)).namedForm
  rw [instantiate_value_of_tests _ _ hbody ht.namedTerm]
  simp only [negValue, implication_node]
  rw [rewrite_slot_imp_value, rewrite_slot_equal_value, ha.2,
    rewrite_slot_bound_zero_value,
    rewrite_slot_nonleaf_value 3 (by decide) (by decide) (by decide)]
  rfl

theorem symmetry_value (p a b : M) :
    symmetry.value ![p, a, b] = equalitySubstitutionCertificate.value
      ![p, equalityReflexivityCertificate.value ![a],
        modelNode 4 [modelNode 1 [zeroValue M], a], a, b] := by
  rw [symmetry, Program.value_comp]
  congr 1
  funext i
  fin_cases i <;>
    simp [unary_value, Program.value_proj, equalCode_value, boundZero,
      syntaxNode_value, list_cons_value, list_nil_value, constant_value, numeral_value_zero,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
      modelNode, modelList_cons, modelList_nil]

theorem certified_symmetry (E : Program 2) (p a b : M)
    (hp : Certified E p (modelNode 4 [a, b])) (ha : PureTerm a) (hb : PureTerm b) :
    Certified E (symmetry.value ![p, a, b]) (modelNode 4 [b, a]) := by
  have hia := instantiate_equality_left ha ha
  have hib := instantiate_equality_left ha hb
  have href := certified_equalityReflexivity E a ha.namedTerm (ha.equal_sentence ha)
  have href' : Certified E (equalityReflexivityCertificate.value ![a])
      (instantiate.value ![modelNode 4 [modelNode 1 [zeroValue M], a], a]) := hia.symm ▸ href
  rw [symmetry_value]
  have hout : isSentence.value ![instantiate.value
      ![modelNode 4 [modelNode 1 [zeroValue M], a], b] ] = numeralValue M 1 := by
    rw [hib]
    exact hb.equal_sentence ha
  have h := certified_equalitySubstitution E p (equalityReflexivityCertificate.value ![a])
    _ a b hp href' (equalityHole_left_bound a ha).namedForm ha.namedTerm hb.namedTerm hout
  simpa only [hib] using h

theorem notEqualRightTransport_value (p q a b c : M) :
    notEqualRightTransport.value ![p, q, a, b, c] = equalitySubstitutionCertificate.value
      ![p, q, negValue (modelNode 4 [a, modelNode 1 [zeroValue M] ]), b, c] := by
  rw [notEqualRightTransport, Program.value_comp]
  congr 1
  funext i
  fin_cases i <;>
    simp [Program.value_proj, negCode_value, equalCode_value, boundZero,
      syntaxNode_value, list_cons_value, list_nil_value, constant_value, numeral_value_zero,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
      modelNode, modelList_cons, modelList_nil]

theorem certified_notEqualRightTransport (E : Program 2) (p q a b c : M)
    (hp : Certified E p (modelNode 4 [b, c]))
    (hq : Certified E q (negValue (modelNode 4 [a, b])))
    (ha : PureTerm a) (hb : PureTerm b) (hc : PureTerm c) :
    Certified E (notEqualRightTransport.value ![p, q, a, b, c])
      (negValue (modelNode 4 [a, c])) := by
  have hib := instantiate_negated_equality_right ha hb
  have hic := instantiate_negated_equality_right ha hc
  have hq' : Certified E q (instantiate.value
      ![negValue (modelNode 4 [a, modelNode 1 [zeroValue M] ]), b]) := hib.symm ▸ hq
  have hout : isSentence.value ![instantiate.value
      ![negValue (modelNode 4 [a, modelNode 1 [zeroValue M] ]), c] ] = numeralValue M 1 := by
    rw [hic]
    exact (pure_negation (PureFormula.equal ha hc)).sentence
  rw [notEqualRightTransport_value]
  have h := certified_equalitySubstitution E p q _ b c hp hq'
    (negation_bound (equalityHole_right_bound a ha)).namedForm hb.namedTerm hc.namedTerm hout
  simpa only [hic] using h

theorem notEqualLeftTransport_value (p q a b c : M) :
    notEqualLeftTransport.value ![p, q, a, b, c] = equalitySubstitutionCertificate.value
      ![p, q, negValue (modelNode 4 [modelNode 1 [zeroValue M], c]), a, b] := by
  rw [notEqualLeftTransport, Program.value_comp]
  congr 1
  funext i
  fin_cases i <;>
    simp [Program.value_proj, negCode_value, equalCode_value, boundZero,
      syntaxNode_value, list_cons_value, list_nil_value, constant_value, numeral_value_zero,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
      modelNode, modelList_cons, modelList_nil]

theorem certified_notEqualLeftTransport (E : Program 2) (p q a b c : M)
    (hp : Certified E p (modelNode 4 [a, b]))
    (hq : Certified E q (negValue (modelNode 4 [a, c])))
    (ha : PureTerm a) (hb : PureTerm b) (hc : PureTerm c) :
    Certified E (notEqualLeftTransport.value ![p, q, a, b, c])
      (negValue (modelNode 4 [b, c])) := by
  have hia := instantiate_negated_equality_left hc ha
  have hib := instantiate_negated_equality_left hc hb
  have hq' : Certified E q (instantiate.value
      ![negValue (modelNode 4 [modelNode 1 [zeroValue M], c]), a]) := hia.symm ▸ hq
  have hout : isSentence.value ![instantiate.value
      ![negValue (modelNode 4 [modelNode 1 [zeroValue M], c]), b] ] = numeralValue M 1 := by
    rw [hib]
    exact (pure_negation (PureFormula.equal hb hc)).sentence
  rw [notEqualLeftTransport_value]
  have h := certified_equalitySubstitution E p q _ a b hp hq'
    (negation_bound (equalityHole_left_bound c hc)).namedForm ha.namedTerm hb.namedTerm hout
  simpa only [hib] using h

end Internal
end
end Lemmatheca.ProofTheory.PAComputations.ProofPrograms.CheckerPrograms.NumericalProofs
