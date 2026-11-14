import Lemmatheca.HeytingArithmeticMultiplication.Instances
import Lemmatheca.IntuitionisticFirstOrderDeduction.Soundness

namespace Lemmatheca.Entry.HeytingArithmeticMultiplication
open _root_.FirstOrder _root_.FirstOrder.Language
open Lemmatheca.ProofTheory.HeytingArithmetic
open Lemmatheca.ProofTheory.HeytingArithmetic.Multiplication
universe u
variable {α : Type u}
noncomputable section
local instance haMultiplicationExamplesEq {β : Type*} : DecidableEq (Formula β) := Classical.decEq _

def doubling {Γ : Context α} (t : LA.Term α) : Certificate false Γ
    (termEqual (mulTerm ((numeral 2).relabel Empty.elim) t) (addTerm t t)) := by
  have h := TheoryCertificate.equalTransitivity (successorLeft (Γ := Γ) (succTerm zeroTerm) t)
    (TheoryCertificate.addEquality (oneLeft t) (TheoryCertificate.equalIntro t))
  simpa only [Lemmatheca.ModelTheory.ArithmeticTheories.numeral, succ_relabel, zero_relabel] using h

/-- Expand the supplied equation first, then rewrite precisely its unit factor. -/
def workedRewrite {Γ : Context α} (x y z : LA.Term α)
    (p : Certificate false Γ (termEqual (mulTerm (addTerm x (succTerm zeroTerm)) y) z)) :
    Certificate false Γ (termEqual (addTerm (mulTerm x y) y) z) :=
  TheoryCertificate.equalTransitivity
    (TheoryCertificate.addEquality (TheoryCertificate.equalIntro (mulTerm x y))
      (TheoryCertificate.equalSymmetry (oneLeft y)))
    (expandLeftSum x (succTerm zeroTerm) y z p)

/-- The exact four original closed recursion clauses, with no further arithmetic assumptions. -/
def recursionTheory : Set Sentence := {qAddZero, qAddSucc, qMulZero, qMulSucc}

@[instance_reducible]
def projectionStructure : LA.Structure Bool where
  funMap := fun f ts => match f with
    | .zero => false
    | .succ => ts 0
    | .add => ts 0
    | .mul => ts 1
  RelMap := fun r => r.elim

theorem projection_recursion_axioms :
    letI : LA.Structure Bool := projectionStructure
    ∀ θ ∈ recursionTheory,
      Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Holds (M := Bool) θ Empty.elim := by
  intro θ hθ
  simp only [recursionTheory, Set.mem_insert_iff, Set.mem_singleton_iff] at hθ
  rcases hθ with h | h | h | h <;> subst θ
  · change ∀ a : Bool, a = a
    intro a
    rfl
  · change ∀ a b : Bool, a = a
    intro a b
    rfl
  · change ∀ a : Bool, (false : Bool) = false
    intro a
    rfl
  · change ∀ a b : Bool, b = b
    intro a b
    rfl

theorem projection_not_zeroLeft :
    letI : LA.Structure Bool := projectionStructure
    ¬ Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Holds (M := Bool)
      zeroLeftSentence Empty.elim := by
  change ¬ (∀ z : Bool, z = false)
  decide

theorem projection_not_separation :
    letI : LA.Structure Bool := projectionStructure
    ¬ Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Holds (M := Bool)
      qSuccNeZero Empty.elim := by
  change ¬ (∀ x : Bool, x ≠ false)
  decide

theorem zeroLeft_not_from_recursion :
    ¬ Nonempty (TheoryCertificate false recursionTheory (∅ : Context Empty) zeroLeftSentence) := by
  let : LA.Structure Bool := projectionStructure
  rintro ⟨p⟩
  apply projection_not_zeroLeft
  apply Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.TheoryProof.sound p Empty.elim
  intro B hB
  rcases hB with hT | hΓ
  · obtain ⟨θ, hθ, rfl⟩ := hT
    have hf : (Empty.elim : Empty → Empty) = id := Subsingleton.elim _ _
    simpa only [hf, Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.rename_id] using
      projection_recursion_axioms θ hθ
  · simp at hΓ

end
end Lemmatheca.Entry.HeytingArithmeticMultiplication
