import Lemmatheca.BoundedArithmeticProofs.PASignedProofBasics
import Lemmatheca.BoundedArithmeticProofs.PASignedBoundTransport
import Lemmatheca.BoundedArithmeticProofs.PATrueBoundedExistential
import Lemmatheca.BoundedArithmeticProofs.PANegativeBoundedExistential

open Lemmatheca.MathematicalLogic Lemmatheca.ModelTheory Lemmatheca.ComputabilityTheory

/-! The existential step of the signed bounded-formula compiler. -/
namespace Lemmatheca.ProofTheory.PAComputations.ProofPrograms.CheckerPrograms.SignedProofs
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic ArithmeticTheories ArithmeticRepresentability
open SyntaxPrograms FixedSyntaxPrograms NumericalProofs BoundedSyntaxPrograms BoundedTruthPrograms
open InitialSegmentPrograms BoundedUniversalPrograms BoundedCounterexamplePrograms
open BoundTermTransport SignedBoundTransport BoundedExistentialNegation
noncomputable section

def existentialWitness {α : Type} [Fintype α] {r : ℕ} {D : language.Formula (α ⊕ Unit)}
    (t : language.Term α) (hD : DeltaZero D) (name : α → Program r) : Program r :=
  atLast (boundedWitness (test hD (extendName name))) (namedTermValue name t)

def existentialPositiveNumeral {α : Type} [Fintype α] {r : ℕ} {D : language.Formula (α ⊕ Unit)}
    (t : language.Term α) (hD : DeltaZero D) (name : α → Program r)
    (child : SignedPrograms D (extendName name)) : Program r :=
  let i := existentialWitness t hD name
  let n := namedTermValue name t
  .comp existentialInstanceCertificate ![binary numeralLeBuilder i n,
    atLast child.positive i, slotFormula 0 name D, i, n]

def existentialNegativeNumeral {α : Type} [Fintype α] {r : ℕ} {D : language.Formula (α ⊕ Unit)}
    (t : language.Term α) (_hD : DeltaZero D) (name : α → Program r)
    (child : SignedPrograms D (extendName name)) : Program r :=
  let body := slotFormula 0 name D
  let n := namedTermValue name t
  let allNeg := atLast (forallBoundedBuilder (negCode body) child.negative) n
  .comp universalNegativeToNegativeExistential ![allNeg,
    upperAt 1 (syntaxNode 1 [constant 0]) n, body]

section Internal
variable {M : Type} [language.Structure M] [M ⊨ PA]

theorem existentialWitness_spec {α : Type} [Fintype α] {r : ℕ} {D : language.Formula (α ⊕ Unit)}
    (t : language.Term α) (hD : DeltaZero D) (name : α → Program r) (x : Fin r → M)
    (hex : (boundedEx t D).Realize (fun a => (name a).value x)) :
    (test hD (extendName name)).value (Fin.snoc x ((existentialWitness t hD name).value x)) =
      numeralValue M 1 ∧
      leValue M ((existentialWitness t hD name).value x) ((namedTermValue name t).value x) := by
  have hbool (i : M) : BooleanValue ((test hD (extendName name)).value (Fin.snoc x i)) := by
    rw [child_truth]
    exact truthValue_boolean _
  obtain ⟨i, hi, hDi⟩ := (realize_boundedEx _ _ _).mp hex
  have hex' : ∃ i : M, leValue M i ((namedTermValue name t).value x) ∧
      (test hD (extendName name)).value (Fin.snoc x i) = numeralValue M 1 := by
    refine ⟨i, ?_, ?_⟩
    · simpa only [namedTermValue_value] using hi
    · rw [child_truth, truthValue_eq_one_iff]
      exact hDi
  have hw := boundedWitness_spec (test hD (extendName name)) x hbool
    ((namedTermValue name t).value x) hex'
  simpa only [existentialWitness, atLast_value] using hw

theorem existentialPositiveNumeral_correct {α : Type} [Fintype α] {r : ℕ}
    {D : language.Formula (α ⊕ Unit)} (t : language.Term α) (hD : DeltaZero D)
    (name : α → Program r) (child : SignedPrograms D (extendName name)) (x : Fin r → M)
    (hex : (boundedEx t D).Realize (fun a => (name a).value x)) :
    Certified axiomVerifier ((existentialPositiveNumeral t hD name child).value x)
      (quantifiedValue false false ((slotFormula 0 name D).value x)
        (numeralSyntax ((namedTermValue name t).value x))) := by
  obtain ⟨hchosen, hbound⟩ := existentialWitness_spec t hD name x hex
  let i := (existentialWitness t hD name).value x
  let n := (namedTermValue name t).value x
  have hp := certified_numeralUpper i n hbound
  have hq := child_positive_instance hD name child x i hchosen
  have hc := certified_existentialInstanceCertificate axiomVerifier
    (numeralLeBuilder.value ![i, n]) (child.positive.value (Fin.snoc x i))
    ((slotFormula 0 name D).value x) i n hp hq
    (slotFormula_bound 0 name D x) (child_instance_pure name D x i)
  change Certified axiomVerifier ((existentialPositiveNumeral t hD name child).value x)
    (quantifiedValue false false ((slotFormula 0 name D).value x) (ProofPrograms.numeral.value ![n]))
  rw [quantifiedValue_existential_numeral]
  simpa only [existentialPositiveNumeral, compFive_model_value, binary_value,
    atLast_value, existentialMatrixValue, i, n] using hc

theorem upper_aux_instance_named (n : M) :
    NamedFormulaBound 0 (instantiate.value
      ![upperValue 1 (modelNode 1 [zeroValue M]) n, modelNode 8 [zeroValue M] ]) := by
  rw [instantiate_value_of_tests _ _ (upperValue_bound 1 _ n bound_zero_termBound).namedForm
    aux_zero_namedTerm, upperValue_rewrite 0, rewrite_slot_bound_zero_value]
  exact upperValue_namedBound 0 _ n (NamedTermBound.aux 0 _)

theorem existentialNegativeNumeral_correct {α : Type} [Fintype α] {r : ℕ}
    {D : language.Formula (α ⊕ Unit)} (t : language.Term α) (hD : DeltaZero D)
    (name : α → Program r) (child : SignedPrograms D (extendName name)) (x : Fin r → M)
    (hnot : ¬(boundedEx t D).Realize (fun a => (name a).value x)) :
    Certified axiomVerifier ((existentialNegativeNumeral t hD name child).value x)
      (quantifiedValue false true ((slotFormula 0 name D).value x)
        (numeralSyntax ((namedTermValue name t).value x))) := by
  let body := slotFormula 0 name D
  let n := (namedTermValue name t).value x
  let qtest := booleanNot (test hD (extendName name))
  have hb := slotFormula_bound 0 name D x
  have hneg : FormulaBound 1 ((negCode body).value x) := by
    rw [negCode_value]
    exact negation_bound hb
  have hinst : NamedFormulaBound 0
      (instantiate.value ![(negCode body).value x, modelNode 8 [zeroValue M] ]) := by
    rw [negCode_value, instantiate_negation hb aux_zero_namedTerm]
    exact named_negation (slotFormula_aux_named name D x _)
  have hfresh : occursAux.value ![zeroValue M, (negCode body).value x] = zeroValue M := by
    rw [negCode_value]
    exact occurs_negation_zero _ _ (slotFormula_fresh 0 name D x _)
  have hpositive (i : M) (hi : qtest.value (Fin.snoc x i) = numeralValue M 1) :
      Certified axiomVerifier (child.negative.value (Fin.snoc x i))
        (instantiate.value ![(negCode body).value x, ProofPrograms.numeral.value ![i] ]) := by
    rw [negCode_value, instantiate_negation hb (PureTerm.numeral i).namedTerm]
    exact child_negative_instance hD name child x i hi
  have hall (i : M) (hi : leValue M i n) : qtest.value (Fin.snoc x i) = numeralValue M 1 := by
    rw [show qtest = booleanNot (test hD (extendName name)) from rfl,
      child_negative_truth, truthValue_eq_one_iff]
    intro hDi
    apply hnot
    apply (realize_boundedEx _ _ _).mpr
    refine ⟨i, ?_, hDi⟩
    simpa only [n, namedTermValue_value] using hi
  have hp := forallBoundedBuilder_certified (negCode body) qtest child.negative x
    hneg hinst hfresh hpositive n hall
  rw [boundedCode_model_value, negCode_value] at hp
  have ha := upperValue_bound 1 (modelNode 1 [zeroValue M]) n bound_zero_termBound
  have hc := certified_universalNegativeToNegativeExistential axiomVerifier
    ((forallBoundedBuilder (negCode body) child.negative).value (Fin.snoc x n))
    (upperValue 1 (modelNode 1 [zeroValue M]) n) (body.value x)
    hp ha hb (upper_aux_instance_named n) (slotFormula_aux_named name D x _)
    (noAux_of_formulaBound ha _) (slotFormula_fresh 0 name D x _)
  have hv : quantifiedValue false true (body.value x) (numeralSyntax n) =
      negValue (exValue (andValue (upperValue 1 (modelNode 1 [zeroValue M]) n) (body.value x))) := by
    simp only [quantifiedValue, signedValue, Bool.false_eq_true, ↓reduceIte,
      ← upperValue_orderTermValue, numeralSyntax]
  rw [hv]
  simpa only [existentialNegativeNumeral, Program.value_comp_three, atLast_value,
    upperAt_model_value, syntaxNode_model_value, List.map_cons, List.map_nil,
    constant_value, numeral_value_zero, body, n, matrixValue] using hc

end Internal

def existentialPrograms {α : Type} [Fintype α] {r : ℕ} {D : language.Formula (α ⊕ Unit)}
    (t : language.Term α) (hD : DeltaZero D) (name : α → Program r)
    (child : SignedPrograms D (extendName name)) : SignedPrograms (boundedEx t D) name where
  positive := transportBound false false name t D (existentialPositiveNumeral t hD name child)
  negative := transportBound false true name t D (existentialNegativeNumeral t hD name child)
  positive_correct := by
    intro M _ _ x hex
    rw [namedFormula_boundedEx]
    exact certified_transportBound false false name t D _ x
      (existentialPositiveNumeral_correct t hD name child x hex)
  negative_correct := by
    intro M _ _ x hnot
    rw [namedFormula_boundedEx]
    exact certified_transportBound false true name t D _ x
      (existentialNegativeNumeral_correct t hD name child x hnot)

end
end Lemmatheca.ProofTheory.PAComputations.ProofPrograms.CheckerPrograms.SignedProofs
