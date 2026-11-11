import Lemmatheca.PropositionalHornClauses.Definability

namespace Lemmatheca.Entry.PropositionalHornClausesDefinability
open Lemmatheca.MathematicalLogic.HornClauses
universe u

theorem empty_family_closed {α : Type u} :
    IntersectionClosed (∅ : Set (Set α)) := by
  intro X hX
  exact False.elim hX

theorem false_constraint {α : Type u} [DecidableEq α] (X : Set α) :
    ¬ models ({⟨∅, none⟩} : Finset (Rule α)) X := by
  simp [models, TheoryModels, Holds]

theorem empty_atom_families :
    (∀ X : Set Empty, models (∅ : Finset (Rule Empty)) X ↔ X = ∅) ∧
    (∀ X : Set Empty, ¬ models ({⟨∅, none⟩} : Finset (Rule Empty)) X) := by
  constructor
  · intro X
    have hx : X = ∅ := by ext a; exact Empty.elim a
    simp [models, TheoryModels, hx]
  · exact false_constraint

end Lemmatheca.Entry.PropositionalHornClausesDefinability
