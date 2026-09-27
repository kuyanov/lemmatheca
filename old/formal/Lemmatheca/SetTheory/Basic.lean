import Mathlib.Basic.IsEmpty.Defs
import Mathlib.Data.Set.Prod
import Mathlib.Tactic.Choose

/-!
# Sets, relations, and maps

Reusable definitions and theorems for arbitrary ambient types. Subsets serve as
specified domains and codomains through their subtypes. Standard set and map laws
are bound directly to mathlib; concrete examples live in `Lemmatheca.Entry.SetsAndMaps`.
-/

namespace Lemmatheca.SetTheory

universe u v

variable {α : Type u} {β : Type v}

/-- A relation between specified sets, with its containment recorded in the type. -/
def RelationBetween (A : Set α) (B : Set β) := {R : Set (α × β) // R ⊆ A ×ˢ B}

/-- Domain and codomain are both part of a map's type. -/
abbrev Map (A : Type u) (B : Type v) := A → B

/-- The totality and uniqueness condition on a relation between two types. -/
def isFunctionGraph (R : Set (α × β)) : Prop := ∀ x, ∃! y, (x, y) ∈ R

theorem graph_has_unique_outputs (f : α → β) :
    isFunctionGraph (Set.graphOn f Set.univ) := by
  intro x
  refine ⟨f x, by simp, ?_⟩
  intro y hy
  exact (Set.mem_graphOn.mp hy).2.symm

theorem function_graph_characterization (R : Set (α × β)) :
    isFunctionGraph R ↔ ∃ f : α → β, R = Set.graphOn f Set.univ := by
  classical
  constructor
  · intro h
    unfold isFunctionGraph at h
    choose f hf hunique using h
    refine ⟨f, ?_⟩
    ext ⟨x, y⟩
    simp only [Set.mem_graphOn, Set.mem_univ, true_and]
    exact ⟨fun hxy => (hunique x y hxy).symm, fun hxy => hxy ▸ hf x⟩
  · rintro ⟨f, rfl⟩
    exact graph_has_unique_outputs f

/-- The fiber over y is the preimage of its singleton. -/
def fiber (f : α → β) (y : β) : Set α := f ⁻¹' {y}

theorem injective_iff_fibers_subsingleton (f : α → β) :
    Function.Injective f ↔ ∀ y, (fiber f y).Subsingleton := by
  constructor
  · intro hf y a ha b hb
    change f a = y at ha
    change f b = y at hb
    exact hf (ha.trans hb.symm)
  · intro h a b hab
    exact h (f a) rfl hab.symm

theorem surjective_iff_fibers_nonempty (f : α → β) :
    Function.Surjective f ↔ ∀ y, (fiber f y).Nonempty := by
  rfl

theorem empty_domain_graph [IsEmpty α] (f : α → β) :
    Set.graphOn f Set.univ = ∅ := by
  ext ⟨x, y⟩
  exact isEmptyElim x

end Lemmatheca.SetTheory
