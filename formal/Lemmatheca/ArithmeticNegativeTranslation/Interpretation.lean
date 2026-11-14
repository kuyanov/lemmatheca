import Lemmatheca.ArithmeticNegativeTranslation.Axioms
import Lemmatheca.HeytingArithmetic.Correspondence
import Lemmatheca.FirstOrderNegativeTranslation.Public

namespace Lemmatheca.ProofTheory.HeytingArithmetic.NegativeTranslation
open _root_.FirstOrder _root_.FirstOrder.Language
open Lemmatheca.ProofTheory.FirstOrder.NegativeTranslation (negative context)
universe u v
variable {α : Type u}
noncomputable section
local instance arithmeticNegativeInterpretationFormulaEq {β : Type*} : DecidableEq (Formula β) := Classical.decEq _

variable {Γ : Context α} {A : Formula α}

private def logicalInterpret (p : Certificate true Γ A) :
    Certificate false (context Γ) (negative A) := by
  let q := Lemmatheca.ProofTheory.FirstOrder.NegativeTranslation.translateTheory p
  apply q.replace
  intro B hB
  let C := Classical.choose hB
  have hC : C ∈ assumptions theory Γ := (Classical.choose_spec hB).1
  have hCB : negative C = B := (Classical.choose_spec hB).2
  rw [← hCB]
  by_cases hΓ : C ∈ Γ
  · exact TheoryCertificate.assumption (Finset.mem_image.mpr ⟨C, hΓ, rfl⟩)
  · have hT : C ∈ liftTheory theory α := hC.resolve_right hΓ
    let θ := Classical.choose hT
    have hθ : θ ∈ theory := (Classical.choose_spec hT).1
    have hθC : θ.rename (Empty.elim : Empty → α) = C := (Classical.choose_spec hT).2
    rw [← hθC]
    exact (translatedAxiomOverNames θ hθ α).weaken (Finset.empty_subset _)

/-- Transform the supplied finite raw tree and its actual arithmetic support. -/
def interpretRaw (p : RawCertificate true theory Γ A) :
    RawCertificate false theory (context Γ) (negative A) := by
  exact TheoryCertificate.toRaw (logicalInterpret (TheoryCertificate.ofRaw p))

/-- Transform supplied public arithmetic certificate data, not mere provability. -/
def interpret (p : Certificate true Γ A) :
    Certificate false (context Γ) (negative A) := by
  exact TheoryCertificate.ofRaw (interpretRaw (TheoryCertificate.toRaw p))

def reflect (p : Certificate false (context Γ) (negative A)) :
    Certificate true Γ A := by
  let q := p.classicalize
  let r : Certificate true Γ (negative A) := q.replace (by
    intro B hB
    by_cases hΓ : B ∈ context Γ
    · have hex := Finset.mem_image.mp hΓ
      let C := Classical.choose hex
      have hC : C ∈ Γ := (Classical.choose_spec hex).1
      have hCB : negative C = B := (Classical.choose_spec hex).2
      rw [← hCB]
      exact TheoryCertificate.ofRaw ⟨Γ, fun _ h => Or.inr h,
        Lemmatheca.ProofTheory.FirstOrder.NegativeTranslation.classicalTo C
          (.assumption hC)⟩
    · have hT : B ∈ liftTheory theory α := hB.resolve_right hΓ
      let θ := Classical.choose hT
      have hθ : θ ∈ theory := (Classical.choose_spec hT).1
      have hθB : θ.rename (Empty.elim : Empty → α) = B := (Classical.choose_spec hT).2
      rw [← hθB]
      exact TheoryCertificate.fromAxiom θ hθ)
  let rr := TheoryCertificate.toRaw r
  exact TheoryCertificate.ofRaw ⟨rr.support, rr.allowed,
    Lemmatheca.ProofTheory.FirstOrder.NegativeTranslation.classicalFrom A rr.derivation⟩

theorem provable_iff (Γ : Context α) (A : Formula α) :
    Provable true Γ A ↔ Provable false (context Γ) (negative A) := by
  constructor
  · rintro ⟨p⟩
    exact ⟨interpret p⟩
  · rintro ⟨p⟩
    exact ⟨reflect p⟩

/-- The actual earlier PA relation is Prop-valued; both endpoints are consequence assertions. -/
theorem pa_iff (A : Sentence) :
    Lemmatheca.MathematicalLogic.FirstOrderProofs.Derives
        Lemmatheca.ModelTheory.ArithmeticTheories.PA A.toClassical ↔
      Provable false (∅ : Context Empty) (negative A) := by
  exact (classical_iff_PA A).symm.trans (by
    simpa only [context, Finset.image_empty] using provable_iff (∅ : Context Empty) A)

theorem pa_small_iff (D : LA.Sentence) :
    Lemmatheca.MathematicalLogic.FirstOrderProofs.Derives
        Lemmatheca.ModelTheory.ArithmeticTheories.PA D ↔
      Provable false (∅ : Context Empty)
        (negative (Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.ofClassical D)) := by
  simpa only [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.toClassical_ofClassical]
    using pa_iff (Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.ofClassical D)

/-- External consistency of the two actual native deduction modes. -/
def Consistent (c : Bool) : Prop :=
  ¬ Provable c (∅ : Context Empty) (.falsum : Sentence)

theorem native_consistency_iff : Consistent false ↔ Consistent true := by
  constructor
  · intro h p
    apply h
    rcases p with ⟨p⟩
    exact ⟨by simpa only [context, Finset.image_empty, negative] using interpret p⟩
  · intro h p
    rcases p with ⟨p⟩
    exact h ⟨p.classicalize⟩

theorem pa_consistency_iff :
    Consistent false ↔
      Lemmatheca.MathematicalLogic.FirstOrderProofs.Consistent
        Lemmatheca.ModelTheory.ArithmeticTheories.PA := by
  apply native_consistency_iff.trans
  change (¬ Provable true (∅ : Context Empty) (.falsum : Sentence)) ↔
    ¬ Lemmatheca.MathematicalLogic.FirstOrderProofs.Derives
      Lemmatheca.ModelTheory.ArithmeticTheories.PA _
  exact not_congr (classical_iff_PA (.falsum : Sentence))

end
end Lemmatheca.ProofTheory.HeytingArithmetic.NegativeTranslation
