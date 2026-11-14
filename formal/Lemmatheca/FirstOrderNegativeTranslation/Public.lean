import Lemmatheca.FirstOrderNegativeTranslation.Classical
import Lemmatheca.ClassicalFirstOrderDeductionTranslations.Public

namespace Lemmatheca.ProofTheory.FirstOrder.NegativeTranslation
open _root_.FirstOrder _root_.FirstOrder.Language
universe u v a b
variable {L : Language.{u,v}} {α : Type a} {e : Bool}
noncomputable section
local instance negativePublicFormulaEq {β : Type*} : DecidableEq (Formula L β) := Classical.decEq _

variable {Γ : NaturalDeduction.Context L α} {A : Formula L α}

def translatePublic (p : NaturalDeduction.Proof true e L Γ A) :
    NaturalDeduction.Proof false e L (context Γ) (negative A) := by
  unfold NaturalDeduction.Proof at p ⊢
  have hp := translate p
  simpa only [context_rename, negative_rename] using hp

def reflectPublic (p : NaturalDeduction.Proof false e L (context Γ) (negative A)) :
    NaturalDeduction.Proof true e L Γ A := by
  unfold NaturalDeduction.Proof at p ⊢
  apply reflect (Γ := Γ.image (fun B => B.rename (Sum.inl : α → α ⊕ ℕ)))
    (A := A.rename Sum.inl)
  simpa only [context_rename, negative_rename] using p

theorem public_iff (Γ : NaturalDeduction.Context L α) (A : Formula L α) :
    NaturalDeduction.Derives true e L Γ A ↔
      NaturalDeduction.Derives false e L (context Γ) (negative A) := by
  constructor
  · rintro ⟨p⟩
    exact ⟨translatePublic p⟩
  · rintro ⟨p⟩
    exact ⟨reflectPublic p⟩

def translateTheory {T : Set (Formula L α)}
    (p : NaturalDeduction.TheoryProof true e L T A) :
    NaturalDeduction.TheoryProof false e L (theory T) (negative A) := by
  refine ⟨context p.assumptions, ?_, translatePublic p.derivation⟩
  intro B hB
  rcases Finset.mem_image.mp hB with ⟨C, hC, rfl⟩
  exact Set.mem_image_of_mem _ (p.allowed C hC)

def reflectTheory {T : Set (Formula L α)}
    (p : NaturalDeduction.TheoryProof false e L (theory T) (negative A)) :
    NaturalDeduction.TheoryProof true e L T A := by
  have preimages : ∀ B : {B // B ∈ p.assumptions}, ∃ C, C ∈ T ∧ negative C = B.val := by
    intro B
    exact p.allowed B.val B.property
  choose pick hpickT hpick using preimages
  let Γ : NaturalDeduction.Context L α := p.assumptions.attach.image pick
  have hΓ : ∀ B ∈ Γ, B ∈ T := by
    intro B hB
    rcases Finset.mem_image.mp hB with ⟨C, _, rfl⟩
    exact hpickT C
  have hsub : p.assumptions ⊆ context Γ := by
    intro B hB
    refine Finset.mem_image.mpr ⟨pick ⟨B, hB⟩, ?_, hpick ⟨B, hB⟩⟩
    exact Finset.mem_image.mpr ⟨⟨B, hB⟩, Finset.mem_attach _ _, rfl⟩
  exact ⟨Γ, hΓ, reflectPublic (p.derivation.weaken hsub)⟩

theorem theory_iff (T : Set (Formula L α)) (A : Formula L α) :
    NaturalDeduction.TheoryDerives true e L T A ↔
      NaturalDeduction.TheoryDerives false e L (theory T) (negative A) := by
  constructor
  · rintro ⟨p⟩
    exact ⟨translateTheory p⟩
  · rintro ⟨p⟩
    exact ⟨reflectTheory p⟩

theorem small_public_iff (Δ : Finset (L.Formula α)) (D : L.Formula α) :
    Lemmatheca.MathematicalLogic.FirstOrderProofs.Proof L Δ D ↔
      NaturalDeduction.Derives false true L
        (context (ClassicalPresentation.includeContext Δ))
        (negative (Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.ofClassical D)) := by
  exact (ClassicalPresentation.public_small_iff Δ D).trans (public_iff (e := true) _ _)

theorem full_small_theory (T : Set (Formula L α)) (A : Formula L α) :
    (NaturalDeduction.TheoryDerives true true L T A ↔
      Lemmatheca.MathematicalLogic.FirstOrderProofs.Derives
        (Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.toClassical '' T) A.toClassical) ∧
    (Lemmatheca.MathematicalLogic.FirstOrderProofs.Derives
        (Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.toClassical '' T) A.toClassical ↔
      NaturalDeduction.TheoryDerives false true L (theory T) (negative A)) := by
  exact ⟨ClassicalPresentation.theory_full_iff T A,
    (ClassicalPresentation.theory_full_iff T A).symm.trans (theory_iff (e := true) T A)⟩

end
end Lemmatheca.ProofTheory.FirstOrder.NegativeTranslation
