import Mathlib.Combinatorics.Compactness
import Mathlib.Combinatorics.Hall.Basic

/-! Finite-valued local assignments and restriction-stable selection constraints. -/

namespace Lemmatheca.SetTheory.RadoHall

universe u v

variable {ι : Type u} {α : Type v}

/-- An assignment on a finite domain, with a value in the available set at each index. -/
def LocalAssignment (A : ι → Set α) (s : Finset ι) :=
  (i : s) → {x : α // x ∈ A i}

/-- All finite domains containing a specified finite set of indices. -/
def FiniteCone (s : Finset ι) : Set (Finset ι) := {t | s ⊆ t}

theorem finite_cones_intersection [DecidableEq ι] (B : Finset (Finset ι)) :
    (⋂ s ∈ B, FiniteCone s) = FiniteCone (B.biUnion id) := by
  ext t
  simp [FiniteCone]

theorem finite_cone_nonempty (s : Finset ι) : (FiniteCone s).Nonempty := by
  exact ⟨s, Finset.Subset.refl s⟩

/-- A solution of every restriction-stable finite constraint family exists globally. -/
theorem finite_constraint_solution {β : ι → Type v} [∀ i, Finite (β i)]
    (S : (s : Finset ι) → Set ((i : s) → β i))
    (hS : ∀ s, (S s).Nonempty)
    (hrestrict : ∀ (s t : Finset ι) (hst : s ⊆ t) (g : (i : t) → β i),
      g ∈ S t → (fun i : s => g (Set.inclusion hst i)) ∈ S s) :
    ∃ f : (i : ι) → β i, ∀ s : Finset ι, (fun i : s => f i) ∈ S s := by
  classical
  choose g hg using hS
  obtain ⟨f, hf⟩ := Finset.rado_selection_subtype g
  refine ⟨f, fun s => ?_⟩
  obtain ⟨t, hst, hagree⟩ := hf s
  have hs := hrestrict s t hst (g t) (hg t)
  convert hs using 1
  funext i
  exact hagree i

/-- An injective choice map for an indexed family of sets. -/
def IsDistinctRepresentative (A : ι → Set α) (f : ι → α) : Prop :=
  Function.Injective f ∧ ∀ i, f i ∈ A i

/-- Every finite set of indices has at least as many available values as indices. -/
def HallCondition [DecidableEq α] (A : ι → Finset α) : Prop :=
  ∀ s : Finset ι, s.card ≤ (s.biUnion A).card

end Lemmatheca.SetTheory.RadoHall
