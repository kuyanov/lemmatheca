import Lemmatheca.IntuitionisticPropositionalKripkeMorphisms.Morphisms

/-! Added axioms remain finitely many assumptions of the original IPC calculus. -/
namespace Lemmatheca.ProofTheory.Intuitionistic.Extensions
open Lemmatheca.MathematicalLogic.Propositional
universe u v

/-- The supplied axiom set is fixed; the additional support is an actual finite set. -/
def SchemaConsequence {α : Type u} (S Γ : Set (PropFormula α)) (A : PropFormula α) : Prop :=
  ∃ E : Finset (PropFormula α), (↑E : Set (PropFormula α)) ⊆ S ∧
    Derives (Γ ∪ (↑E : Set (PropFormula α))) A

theorem schemaConsequence_iff_union {α : Type u} (S Γ : Set (PropFormula α))
    (A : PropFormula α) : SchemaConsequence S Γ A ↔ Derives (Γ ∪ S) A := by
  classical
  constructor
  · rintro ⟨E, hES, h⟩
    exact h.weaken (Set.union_subset_union_right Γ hES)
  · intro h
    obtain ⟨F, hF, hsub, hder⟩ := finite_support.mp h
    let E := hF.toFinset.filter (fun B => B ∈ S)
    refine ⟨E, ?_, hder.weaken ?_⟩
    · intro B hB
      exact (Finset.mem_filter.mp hB).2
    · intro B hB
      rcases hsub hB with hΓ | hS
      · exact Or.inl hΓ
      · exact Or.inr (Finset.mem_filter.mpr ⟨by simpa using hB, hS⟩)

theorem schemaConsequence_sound {α : Type u} {W : Type v} [Preorder W] [Nonempty W]
    (S Γ : Set (PropFormula α)) (A : PropFormula α)
    (hS : ∀ B ∈ S, Kripke.FrameValid W B) (h : SchemaConsequence S Γ A)
    (M : Kripke.Model α W) (w : W) (hΓ : Kripke.ForcesContext M w Γ) :
    Kripke.Forces M w A := by
  obtain ⟨E, hES, hd⟩ := h
  apply Kripke.sound hd M w
  intro B hB
  rcases hB with hB | hB
  · exact hΓ B hB
  · exact hS B (hES hB) M w

end Lemmatheca.ProofTheory.Intuitionistic.Extensions

namespace Lemmatheca.ProofTheory.Intuitionistic.WeakExcludedMiddle
open Lemmatheca.MathematicalLogic.Propositional
universe u v

def wem {α : Type u} (A : PropFormula α) : PropFormula α := .disj (.neg A) (.neg (.neg A))

def axioms {α : Type u} : Set (PropFormula α) := Set.range (wem (α := α))

def deMorgan {α : Type u} (A B : PropFormula α) : PropFormula α :=
  .impl (.neg (.conj A B)) (.disj (.neg A) (.neg B))

def deMorganAxioms {α : Type u} : Set (PropFormula α) :=
  Set.range (fun ab : PropFormula α × PropFormula α => deMorgan ab.1 ab.2)

theorem wem_substitute {α : Type u} {β : Type v} (σ : α → PropFormula β)
    (A : PropFormula α) : subst σ (wem A) = wem (subst σ A) := by
  rfl

end Lemmatheca.ProofTheory.Intuitionistic.WeakExcludedMiddle
