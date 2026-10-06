import Lemmatheca.SetTheory.Relations

/-! Particular examples and counterexamples for the human entry. -/

set_option autoImplicit false
universe u v
namespace Lemmatheca.Entry.RelationExtensions
open Lemmatheca.SetTheory.Relations

/-- Closure computations for the two-edge path on three points. -/
theorem three_point_closures :
    let R := fun a b : Fin 3 => (a=0 ∧ b=1) ∨ (a=1 ∧ b=2)
    (∀ a b, Relation.TransGen R a b ↔ a < b) ∧
    (∀ a b, Relation.ReflTransGen R a b ↔ a ≤ b) ∧
    (∀ a b, Relation.EqvGen R a b) := by
  dsimp only
  let R := fun a b : Fin 3 => (a=0 ∧ b=1) ∨ (a=1 ∧ b=2)
  have he : ∀ a b, R a b → a < b := by
    intro a b h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  have h01 : R 0 1 := Or.inl ⟨rfl, rfl⟩
  have h12 : R 1 2 := Or.inr ⟨rfl, rfl⟩
  have htrans : ∀ a b, Relation.TransGen R a b ↔ a < b := by
    intro a b
    constructor
    · intro h
      induction h with
      | single h => exact he _ _ h
      | tail _ h ih => exact ih.trans (he _ _ h)
    · intro h
      fin_cases a <;> fin_cases b <;>
        first | (solve | simp at h) |
          exact Relation.TransGen.single h01 |
          exact Relation.TransGen.single h12 |
          exact (Relation.TransGen.single h01).tail h12
  refine ⟨htrans, ?_, ?_⟩
  · intro a b
    constructor
    · intro h
      induction h with
      | refl => exact le_rfl
      | tail _ h ih => exact ih.trans (he _ _ h).le
    · intro h
      rcases h.eq_or_lt with rfl | h
      · exact .refl
      · exact ((htrans _ _).mpr h).to_reflTransGen
  · intro a b
    have h02 : Relation.EqvGen R 0 2 := .trans 0 1 2 (.rel 0 1 h01) (.rel 1 2 h12)
    fin_cases a <;> fin_cases b <;>
      first | exact .refl _ | exact .rel 0 1 h01 | exact .rel 1 2 h12 |
        exact h02 | exact .symm _ _ (.rel 0 1 h01) |
        exact .symm _ _ (.rel 1 2 h12) | exact .symm _ _ h02

end Lemmatheca.Entry.RelationExtensions
