import Lemmatheca.EqualityFreeIntuitionisticFirstOrderKripkeCompleteness.Names

namespace Lemmatheca.ProofTheory.FirstOrder.KripkeCompleteness
open _root_.FirstOrder _root_.FirstOrder.Language
universe u v
noncomputable section
variable {L : Language.{u,v}} {α : Type} [Countable L.Symbols] [Countable α]

/-- The semantic quantifier includes the actual canonical frame and actual term domains. -/
theorem strong_completeness (Γ : Set (Formula L α)) (A : Formula L α)
    (hΓ : ∀ B ∈ Γ, B.EqualityFree) (hA : A.EqualityFree) :
    Kripke.Entails.{u,v,max u v,u} Γ A ↔ NaturalDeduction.TheoryDerives false false L Γ A := by
  constructor
  · intro h
    by_contra hN
    let w := originalWorld Γ A hΓ hA hN
    have hc := original_countermodel Γ A hΓ hA hN
    exact hc.2 (h (World L) canonicalModel w (originalAssignment w) hc.1)
  · exact Kripke.theory_entails

/-- Satisfiability uses all actual diagrams of the same universe sizes as consequence. -/
def Satisfiable (Γ : Set (Formula L α)) : Prop :=
  ∃ (X : Type (max u v)) (p : Preorder X)
    (K : @Kripke.Model.{u,v,max u v,u} L X p) (x : X) (s : α → K.Domain x),
    Kripke.ForcesContext K x Γ s

theorem consequence_compactness (Γ : Set (Formula L α)) (A : Formula L α)
    (hΓ : ∀ B ∈ Γ, B.EqualityFree) (hA : A.EqualityFree)
    (h : Kripke.Entails.{u,v,max u v,u} Γ A) :
    ∃ Δ : Finset (Formula L α), (↑Δ : Set (Formula L α)) ⊆ Γ ∧
      Kripke.Entails.{u,v,max u v,u} (↑Δ : Set (Formula L α)) A := by
  obtain ⟨p⟩ := (strong_completeness Γ A hΓ hA).mp h
  refine ⟨p.assumptions,p.allowed,?_⟩
  exact Kripke.theory_entails ⟨⟨p.assumptions,fun _ hB => hB,p.derivation⟩⟩

theorem satisfiable_iff_consistent (Γ : Set (Formula L α)) (hΓ : ∀ B ∈ Γ, B.EqualityFree) :
    Satisfiable Γ ↔ ¬NaturalDeduction.TheoryDerives false false L Γ .falsum := by
  constructor
  · rintro ⟨X,p,K,x,s,hT⟩ ⟨q⟩
    exact Kripke.theoryProof_sound K q x s hT
  · intro hN
    let w := originalWorld Γ .falsum hΓ trivial hN
    have hc := original_countermodel Γ .falsum hΓ trivial hN
    exact ⟨World L,inferInstance,canonicalModel,w,originalAssignment w,hc.1⟩

end
end Lemmatheca.ProofTheory.FirstOrder.KripkeCompleteness
