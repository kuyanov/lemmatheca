import Lemmatheca.ClassicalFirstOrderDeductionTranslations.Translations

/-! Exact public reserve and arbitrary-theory correspondences. -/
namespace Lemmatheca.ProofTheory.FirstOrder.ClassicalPresentation
open _root_.FirstOrder _root_.FirstOrder.Language
universe u v w
variable {L : Language.{u,v}} {α : Type w} {c e : Bool}
noncomputable section
local instance publicFullFormulaEq {K : Language.{u,v}} {δ : Type*} :
    DecidableEq (Formula K δ) := Classical.decEq _
local instance publicSmallFormulaEq {K : Language.{u,v}} {δ : Type*} :
    DecidableEq (K.Formula δ) := Classical.decEq _

private theorem public_toClassical_rename {β : Type w} (A : Formula L α) (f : α → β) :
    (A.rename f).toClassical = _root_.FirstOrder.Language.Formula.relabel f A.toClassical := by
  simp only [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.rename, Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.toClassical_subst,
    Lemmatheca.MathematicalLogic.FirstOrderProofs.formula_subst_vars]

private theorem public_expand_rename {β : Type w} (Γ : Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Context L α) (f : α → β) :
    expandContext (Γ.image (fun A => A.rename f)) =
      (expandContext Γ).image (fun D => _root_.FirstOrder.Language.Formula.relabel f D) := by
  simp only [expandContext, Finset.image_image, Function.comp_def, public_toClassical_rename]

private theorem public_include_rename {β : Type w} (Γ : Finset (L.Formula α)) (f : α → β) :
    includeContext (Γ.image (fun D => _root_.FirstOrder.Language.Formula.relabel f D)) =
      (includeContext Γ).image (fun A => A.rename f) := by
  simp only [includeContext, Finset.image_image, Function.comp_def, ofClassical_rename]

private theorem public_expanded_rename {β : Type w} (A : Formula L α) (f : α → β) :
    expanded (A.rename f) = (expanded A).rename f := by
  exact expanded_map A _

/-- Expand a supplied public native certificate, preserving its original end names. -/
theorem public_toSmall {Γ : Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Context L α} {A : Formula L α}
    (p : Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Proof c e L Γ A) : Lemmatheca.MathematicalLogic.FirstOrderProofs.Proof L (expandContext Γ) A.toClassical := by
  change Lemmatheca.MathematicalLogic.FirstOrderProofs.CoreProof L
    ((expandContext Γ).image (fun D => _root_.FirstOrder.Language.Formula.relabel (Sum.inl : α → α ⊕ ℕ) D))
    (_root_.FirstOrder.Language.Formula.relabel (Sum.inl : α → α ⊕ ℕ) A.toClassical)
  rw [← public_expand_rename, ← public_toClassical_rename]
  exact raw_toSmall p

/-- Include a public small proof without choosing an actual tree from a Prop proof. -/
theorem public_ofSmall {Γ : Finset (L.Formula α)} {D : L.Formula α}
    (h : Lemmatheca.MathematicalLogic.FirstOrderProofs.Proof L Γ D) :
    Nonempty (Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Proof true true L (includeContext Γ) (Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.ofClassical D)) := by
  change Nonempty (Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Derivation true true L
    ((includeContext Γ).image (fun A => A.rename (Sum.inl : α → α ⊕ ℕ)))
    ((Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.ofClassical D).rename Sum.inl))
  rw [← public_include_rename, ← ofClassical_rename]
  exact raw_ofSmall h

/-- The raw round-trip construction on the actual underlying reserve proof. -/
def Public.toExpanded {Γ : Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Context L α} {A : Formula L α}
    (p : Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Proof true e L Γ A) : Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Proof true e L Γ (expanded A) := by
  unfold Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Proof at p ⊢
  simpa only [public_expanded_rename] using Raw.toExpanded p

def Public.fromExpanded {Γ : Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Context L α} (A : Formula L α)
    (p : Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Proof true e L Γ (expanded A)) : Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Proof true e L Γ A := by
  unfold Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Proof at p ⊢
  exact Raw.fromExpanded (A.rename (Sum.inl : α → α ⊕ ℕ))
    (by simpa only [public_expanded_rename] using p)

theorem public_small_iff (Γ : Finset (L.Formula α)) (D : L.Formula α) :
    Lemmatheca.MathematicalLogic.FirstOrderProofs.Proof L Γ D ↔ Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Derives true true L (includeContext Γ) (Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.ofClassical D) := by
  constructor
  · exact public_ofSmall
  · rintro ⟨p⟩
    have hp := public_toSmall p
    simpa only [expandContext, includeContext, Finset.image_image, Function.comp_def,
      Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.toClassical_ofClassical, Finset.image_id'] using hp

theorem public_full_iff (Γ : Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Context L α) (A : Formula L α) :
    Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Derives true true L Γ A ↔ Lemmatheca.MathematicalLogic.FirstOrderProofs.Proof L (expandContext Γ) A.toClassical := by
  change Nonempty (Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Derivation true true L
    (Γ.image (fun B => B.rename (Sum.inl : α → α ⊕ ℕ))) (A.rename Sum.inl)) ↔
    Lemmatheca.MathematicalLogic.FirstOrderProofs.CoreProof L
      ((expandContext Γ).image (fun D => _root_.FirstOrder.Language.Formula.relabel (Sum.inl : α → α ⊕ ℕ) D))
      (_root_.FirstOrder.Language.Formula.relabel (Sum.inl : α → α ⊕ ℕ) A.toClassical)
  rw [← public_expand_rename, ← public_toClassical_rename]
  exact raw_full_iff _ _

theorem theory_full_iff (T : Set (Formula L α)) (A : Formula L α) :
    Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.TheoryDerives true true L T A ↔ Lemmatheca.MathematicalLogic.FirstOrderProofs.Derives (Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.toClassical '' T) A.toClassical := by
  classical
  constructor
  · rintro ⟨p⟩
    refine ⟨expandContext p.assumptions, ?_, (public_full_iff _ _).mp ⟨p.derivation⟩⟩
    intro D hD
    rcases Finset.mem_image.mp hD with ⟨B, hB, rfl⟩
    exact Set.mem_image_of_mem _ (p.allowed B hB)
  · rintro ⟨Δ, hΔ, p⟩
    have preimages : ∀ D : {D // D ∈ Δ}, ∃ B, B ∈ T ∧ B.toClassical = D.val := by
      intro D
      exact hΔ D.property
    choose pick hpickT hpick using preimages
    let Γ : Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Context L α := Δ.attach.image pick
    have hΓ : ∀ B ∈ Γ, B ∈ T := by
      intro B hB
      rcases Finset.mem_image.mp hB with ⟨D, _, rfl⟩
      exact hpickT D
    have hsub : Δ ⊆ expandContext Γ := by
      intro D hD
      refine Finset.mem_image.mpr ⟨pick ⟨D, hD⟩, ?_, hpick ⟨D,hD⟩⟩
      exact Finset.mem_image.mpr ⟨⟨D,hD⟩, Finset.mem_attach _ _, rfl⟩
    have hw := Lemmatheca.MathematicalLogic.FirstOrderProofs.Proof.weakening p hsub
    rcases (public_full_iff Γ A).mpr hw with ⟨q⟩
    exact ⟨⟨Γ, hΓ, q⟩⟩

end
end Lemmatheca.ProofTheory.FirstOrder.ClassicalPresentation
