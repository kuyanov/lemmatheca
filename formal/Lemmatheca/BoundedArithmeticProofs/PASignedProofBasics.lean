import Lemmatheca.BoundedArithmeticProofs.PABoundedSyntaxPrograms
import Lemmatheca.BoundedArithmeticProofs.PABoundedWitnessPrograms

open Lemmatheca.MathematicalLogic Lemmatheca.ModelTheory Lemmatheca.ComputabilityTheory

/-! The common exact contract for signed native proof compilers. -/
namespace Lemmatheca.ProofTheory.PAComputations.ProofPrograms.CheckerPrograms.SignedProofs
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic ArithmeticTheories ArithmeticRepresentability
open SyntaxPrograms FixedSyntaxPrograms NumericalProofs BoundedSyntaxPrograms BoundedTruthPrograms
noncomputable section

structure SignedPrograms {α : Type} {r : ℕ} (D : language.Formula α) (name : α → Program r) where
  positive : Program r
  negative : Program r
  positive_correct : ∀ {M : Type} [language.Structure M] [M ⊨ PA] (x : Fin r → M),
    D.Realize (fun a => (name a).value x) →
      Certified axiomVerifier (positive.value x) ((namedFormula name D).value x)
  negative_correct : ∀ {M : Type} [language.Structure M] [M ⊨ PA] (x : Fin r → M),
    ¬D.Realize (fun a => (name a).value x) →
      Certified axiomVerifier (negative.value x) (negValue ((namedFormula name D).value x))

def atLast {r : ℕ} (p : Program (r + 1)) (a : Program r) : Program r :=
  .comp p (Fin.snoc (fun i => .proj i) a)

section Internal
variable {M : Type} [language.Structure M] [M ⊨ PA]

theorem atLast_value {r : ℕ} (p : Program (r + 1)) (a : Program r) (x : Fin r → M) :
    (atLast p a).value x = p.value (Fin.snoc x (a.value x)) := by
  rw [atLast, Program.value_comp]
  congr 1
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Fin.snoc_last]
  · simp only [Fin.snoc_castSucc, Program.value_proj]

theorem child_truth {α : Type} [Fintype α] {r : ℕ} {D : language.Formula (α ⊕ Unit)}
    (hD : DeltaZero D) (name : α → Program r) (x : Fin r → M) (i : M) :
    (test hD (extendName name)).value (Fin.snoc x i) =
      truthValue (M := M) (D.Realize (extend (fun a => (name a).value x) i)) := by
  rw [test_value, extendName_value]
  rfl

theorem child_negative_truth {α : Type} [Fintype α] {r : ℕ} {D : language.Formula (α ⊕ Unit)}
    (hD : DeltaZero D) (name : α → Program r) (x : Fin r → M) (i : M) :
    (booleanNot (test hD (extendName name))).value (Fin.snoc x i) =
      truthValue (M := M) (¬D.Realize (extend (fun a => (name a).value x) i)) :=
  booleanNot_truthValue _ _ _ (child_truth hD name x i)

theorem child_positive_instance {α : Type} [Fintype α] {r : ℕ} {D : language.Formula (α ⊕ Unit)}
    (hD : DeltaZero D) (name : α → Program r) (child : SignedPrograms D (extendName name))
    (x : Fin r → M) (i : M)
    (htest : (test hD (extendName name)).value (Fin.snoc x i) = numeralValue M 1) :
    Certified axiomVerifier (child.positive.value (Fin.snoc x i))
      (instantiate.value ![(slotFormula 0 name D).value x, numeralSyntax i]) := by
  rw [slotFormula_instantiate_numeral]
  apply child.positive_correct
  rw [child_truth, truthValue_eq_one_iff] at htest
  rw [extendName_value]
  exact htest

theorem child_negative_instance {α : Type} [Fintype α] {r : ℕ} {D : language.Formula (α ⊕ Unit)}
    (hD : DeltaZero D) (name : α → Program r) (child : SignedPrograms D (extendName name))
    (x : Fin r → M) (i : M)
    (htest : (booleanNot (test hD (extendName name))).value (Fin.snoc x i) = numeralValue M 1) :
    Certified axiomVerifier (child.negative.value (Fin.snoc x i))
      (negValue (instantiate.value ![(slotFormula 0 name D).value x, numeralSyntax i])) := by
  rw [slotFormula_instantiate_numeral]
  apply child.negative_correct
  rw [child_negative_truth, truthValue_eq_one_iff] at htest
  rw [extendName_value]
  exact htest

theorem child_instance_pure {α : Type} {r : ℕ} (name : α → Program r)
    (D : language.Formula (α ⊕ Unit)) (x : Fin r → M) (i : M) :
    PureFormula (instantiate.value ![(slotFormula 0 name D).value x, numeralSyntax i]) := by
  rw [slotFormula_instantiate_numeral]
  exact namedFormula_pure _ _ _

theorem certified_numeralUpper (i n : M) (hi : leValue M i n) :
    Certified axiomVerifier (numeralLeBuilder.value ![i, n])
      (InitialSegmentPrograms.upperValue 0 (numeralSyntax i) n) := by
  rw [BoundTermTransport.upperValue_orderTermValue]
  have hp := certified_numeralLeBuilder i n hi
  simpa only [BoundTermTransport.orderTermValue, orderValue, orderBodyValue,
    numeral_value_zero, numeralSyntax] using hp

end Internal
end
end Lemmatheca.ProofTheory.PAComputations.ProofPrograms.CheckerPrograms.SignedProofs
