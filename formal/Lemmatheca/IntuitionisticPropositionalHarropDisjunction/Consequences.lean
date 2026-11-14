import Lemmatheca.IntuitionisticPropositionalHarropDisjunction.Extraction

/-! Older Prop-valued derivability gives existence, rather than specified input data. -/
namespace Lemmatheca.ProofTheory.Intuitionistic.Harrop
open Lemmatheca.MathematicalLogic.Propositional
open PropFormula
universe u
variable {α : Type u} [DecidableEq α]

theorem finite_factor_iff (Γ : Finset (PropFormula α)) (hΓ : ContextHarrop Γ)
    (A B : PropFormula α) :
    Derives (Γ : Set (PropFormula α)) (.disj A B) ↔
      Derives (Γ : Set (PropFormula α)) A ∨ Derives (Γ : Set (PropFormula α)) B := by
  constructor
  · intro h
    rcases CutFree.from_natural h with ⟨p⟩
    rcases extract hΓ p with q | q
    · exact Or.inl q.to_natural
    · exact Or.inr q.to_natural
  · rintro (hA | hB)
    · exact .disjIntroLeft hA
    · exact .disjIntroRight hB

theorem set_factor_iff (T : Set (PropFormula α)) (hT : ∀ D ∈ T, IsHarrop D)
    (A B : PropFormula α) : Derives T (.disj A B) ↔ Derives T A ∨ Derives T B := by
  constructor
  · intro h
    rcases finite_support.mp h with ⟨Δ, hfinite, hΔ, hderive⟩
    have hΓ : ContextHarrop hfinite.toFinset := by
      intro D hD
      exact hT D (hΔ (hfinite.mem_toFinset.mp hD))
    have hd : Derives (hfinite.toFinset : Set (PropFormula α)) (.disj A B) := by
      simpa only [Set.Finite.coe_toFinset] using hderive
    rcases (finite_factor_iff hfinite.toFinset hΓ A B).mp hd with hA | hB
    · exact Or.inl (hA.weaken (by simpa only [Set.Finite.coe_toFinset] using hΔ))
    · exact Or.inr (hB.weaken (by simpa only [Set.Finite.coe_toFinset] using hΔ))
  · rintro (hA | hB)
    · exact .disjIntroLeft hA
    · exact .disjIntroRight hB

theorem implication_factor (Γ : Finset (PropFormula α)) (hΓ : ContextHarrop Γ)
    (H A B : PropFormula α) (hH : IsHarrop H)
    (h : Derives (Γ : Set (PropFormula α)) (.impl H (.disj A B))) :
    Derives (Γ : Set (PropFormula α)) (.impl H A) ∨
      Derives (Γ : Set (PropFormula α)) (.impl H B) := by
  rcases CutFree.from_natural h with ⟨p⟩
  rcases implicationChoice hΓ hH p with q | q
  · exact Or.inl q.to_natural
  · exact Or.inr q.to_natural

end Lemmatheca.ProofTheory.Intuitionistic.Harrop
