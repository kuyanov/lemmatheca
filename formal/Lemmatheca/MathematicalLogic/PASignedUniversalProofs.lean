import Lemmatheca.MathematicalLogic.PASignedProofBasics
import Lemmatheca.MathematicalLogic.PASignedBoundTransport
import Lemmatheca.MathematicalLogic.PAFalseBoundedUniversal

namespace Lemmatheca.MathematicalLogic.PAComputations.ProofPrograms.CheckerPrograms.SignedProofs
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic ArithmeticTheories ArithmeticRepresentability
open SyntaxPrograms FixedSyntaxPrograms NumericalProofs BoundedSyntaxPrograms BoundedTruthPrograms
open BoundedUniversalPrograms BoundedCounterexamplePrograms BoundTermTransport SignedBoundTransport
noncomputable section

def universalPositiveNormalized {α : Type} [Fintype α] {r : ℕ} (name : α → Program r)
    (t : language.Term α) (D : language.Formula (α ⊕ Unit))
    (child : SignedPrograms D (extendName name)) : Program r :=
  atLast (forallBoundedBuilder (slotFormula 0 name D) child.positive) (namedTermValue name t)

def universalWitness {α : Type} [Fintype α] {r : ℕ} (name : α → Program r)
    (t : language.Term α) {D : language.Formula (α ⊕ Unit)} (hD : DeltaZero D) : Program r :=
  atLast (boundedWitness (booleanNot (test hD (extendName name)))) (namedTermValue name t)

def universalNegativeNormalized {α : Type} [Fintype α] {r : ℕ} (name : α → Program r)
    (t : language.Term α) (D : language.Formula (α ⊕ Unit)) (hD : DeltaZero D)
    (child : SignedPrograms D (extendName name)) : Program r :=
  let witness := universalWitness name t hD
  let bound := namedTermValue name t
  .comp counterexampleCertificate ![binary numeralLeBuilder witness bound,
    atLast child.negative witness, slotFormula 0 name D, witness, bound]

section Internal
variable {M : Type} [language.Structure M] [M ⊨ PA]

theorem universalPositiveNormalized_correct {α : Type} [Fintype α] {r : ℕ}
    (name : α → Program r) (t : language.Term α) (D : language.Formula (α ⊕ Unit))
    (hD : DeltaZero D) (child : SignedPrograms D (extendName name)) (x : Fin r → M)
    (hall : (boundedAll t D).Realize (fun a => (name a).value x)) :
    Certified axiomVerifier ((universalPositiveNormalized name t D child).value x)
      (quantifiedValue true false ((slotFormula 0 name D).value x)
        (numeralSyntax ((namedTermValue name t).value x))) := by
  have hbody := slotFormula_bound 0 name D x
  have hinst := slotFormula_aux_named name D x (zeroValue M)
  have hfresh := slotFormula_fresh 0 name D x (zeroValue M)
  have hpositive := child_positive_instance hD name child x
  have htest : ∀ i : M, leValue M i ((namedTermValue name t).value x) →
      (test hD (extendName name)).value (Fin.snoc x i) = numeralValue M 1 := by
    rw [realize_boundedAll] at hall
    intro i hi
    rw [child_truth, truthValue_eq_one_iff]
    apply hall i
    simpa only [namedTermValue_value] using hi
  have h := forallBoundedBuilder_certified (slotFormula 0 name D)
    (test hD (extendName name)) child.positive x hbody hinst hfresh hpositive
    ((namedTermValue name t).value x) htest
  rw [boundedCode_model_value] at h
  rw [universalPositiveNormalized, atLast_value]
  simpa only [numeralSyntax, quantifiedValue_universal_numeral] using h

theorem upperValue_zero_orderValue (i n : M) :
    InitialSegmentPrograms.upperValue 0 (numeralSyntax i) n =
      orderValue (numeralSyntax i) (numeralSyntax n) := by
  rw [upperValue_orderTermValue]
  simp only [orderTermValue, orderValue, orderBodyValue, numeral_value_zero, numeralSyntax]

theorem universalNegativeNormalized_correct {α : Type} [Fintype α] {r : ℕ}
    (name : α → Program r) (t : language.Term α) (D : language.Formula (α ⊕ Unit))
    (hD : DeltaZero D) (child : SignedPrograms D (extendName name)) (x : Fin r → M)
    (hnot : ¬(boundedAll t D).Realize (fun a => (name a).value x)) :
    Certified axiomVerifier ((universalNegativeNormalized name t D hD child).value x)
      (quantifiedValue true true ((slotFormula 0 name D).value x)
        (numeralSyntax ((namedTermValue name t).value x))) := by
  classical
  let q := booleanNot (test hD (extendName name))
  let n := (namedTermValue name t).value x
  let witness := universalWitness name t hD
  let i := witness.value x
  have hbool (j : M) : BooleanValue (q.value (Fin.snoc x j)) := by
    rw [child_negative_truth]
    exact truthValue_boolean _
  have hex : ∃ j : M, leValue M j n ∧ q.value (Fin.snoc x j) = numeralValue M 1 := by
    rw [realize_boundedAll] at hnot
    push Not at hnot
    obtain ⟨j, hj, hfalse⟩ := hnot
    refine ⟨j, ?_, ?_⟩
    · simpa only [n, namedTermValue_value] using hj
    · rw [child_negative_truth, truthValue_eq_one_iff]
      exact hfalse
  have hchoice := boundedWitness_spec q x hbool n hex
  have hindex : (boundedWitness q).value (Fin.snoc x n) = i := by
    rw [show i = (universalWitness name t hD).value x from rfl,
      universalWitness, atLast_value]
  rw [hindex] at hchoice
  have hupper := certified_numeralLeBuilder i n hchoice.2
  have hupper' : Certified axiomVerifier (numeralLeBuilder.value ![i, n])
      (InitialSegmentPrograms.upperValue 0 (numeralSyntax i) n) := by
    rw [upperValue_zero_orderValue]
    exact hupper
  have hnegative := child_negative_instance hD name child x i hchoice.1
  have h := certified_counterexampleCertificate axiomVerifier
    (numeralLeBuilder.value ![i, n]) (child.negative.value (Fin.snoc x i))
    ((slotFormula 0 name D).value x) i n hupper' hnegative
    (slotFormula_bound 0 name D x) (child_instance_pure name D x i)
  have hquant : quantifiedValue true true ((slotFormula 0 name D).value x) (numeralSyntax n) =
      negValue (modelNode 7 [matrixValue ((slotFormula 0 name D).value x) n]) := by
    change negValue (quantifiedValue true false ((slotFormula 0 name D).value x) (numeralSyntax n)) = _
    simp only [numeralSyntax, quantifiedValue_universal_numeral]
  rw [hquant]
  simpa only [universalNegativeNormalized, compFive_model_value, binary_value, atLast_value,
    witness, i, n] using h

end Internal

def universalPrograms {α : Type} [Fintype α] {r : ℕ}
    {D : language.Formula (α ⊕ Unit)} (t : language.Term α) (hD : DeltaZero D) (name : α → Program r)
    (child : SignedPrograms D (extendName name)) : SignedPrograms (boundedAll t D) name where
  positive := transportBound true false name t D (universalPositiveNormalized name t D child)
  negative := transportBound true true name t D (universalNegativeNormalized name t D hD child)
  positive_correct := by
    intro M _ _ x h
    rw [namedFormula_boundedAll]
    exact certified_transportBound true false name t D _ x
      (universalPositiveNormalized_correct name t D hD child x h)
  negative_correct := by
    intro M _ _ x h
    rw [namedFormula_boundedAll]
    exact certified_transportBound true true name t D _ x
      (universalNegativeNormalized_correct name t D hD child x h)

end
end Lemmatheca.MathematicalLogic.PAComputations.ProofPrograms.CheckerPrograms.SignedProofs
