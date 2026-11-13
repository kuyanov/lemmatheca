import Lemmatheca.IntuitionisticPropositionalKripkeCompleteness.CanonicalModel
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card

namespace Lemmatheca.ProofTheory.Intuitionistic.FiniteModels

open Lemmatheca.MathematicalLogic.Propositional
open PropFormula

abbrev Formula := Canonical.Formula

/-- All actual native subformulas, including the formula itself. -/
def subformulas : Formula → Finset Formula
  | .atom p => {atom p}
  | .falsum => {falsum}
  | .neg A => insert (neg A) (subformulas A)
  | .conj A B => insert (conj A B) (subformulas A ∪ subformulas B)
  | .disj A B => insert (disj A B) (subformulas A ∪ subformulas B)
  | .impl A B => insert (impl A B) (subformulas A ∪ subformulas B)

def SubformulaClosed (Δ : Finset Formula) : Prop :=
  ∀ A ∈ Δ, subformulas A ⊆ Δ

def problemSubformulas (Γ : Finset Formula) (A : Formula) : Finset Formula :=
  subformulas A ∪ Γ.biUnion subformulas

def problemAtoms (Γ : Finset Formula) (A : Formula) : Finset ℕ :=
  atoms A ∪ Γ.biUnion atoms

def worldBound (Γ : Finset Formula) (A : Formula) : ℕ :=
  2 ^ (problemSubformulas Γ A).card

theorem self_mem_subformulas (A : Formula) : A ∈ subformulas A := by
  cases A <;> simp [subformulas]

theorem subformulas_trans {A B : Formula} (h : B ∈ subformulas A) :
    subformulas B ⊆ subformulas A := by
  induction A generalizing B with
  | atom p =>
      have hB := Finset.mem_singleton.mp h
      subst B
      exact Finset.Subset.rfl
  | falsum =>
      have hB := Finset.mem_singleton.mp h
      subst B
      exact Finset.Subset.rfl
  | neg A ih =>
      rcases Finset.mem_insert.mp h with rfl | h
      · exact Finset.Subset.rfl
      · exact (ih h).trans (Finset.subset_insert _ _)
  | conj A C ihA ihC =>
      rcases Finset.mem_insert.mp h with rfl | h
      · exact Finset.Subset.rfl
      · rcases Finset.mem_union.mp h with hA | hC
        · intro D hD
          exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (ihA hA hD))
        · intro D hD
          exact Finset.mem_insert_of_mem (Finset.mem_union_right _ (ihC hC hD))
  | disj A C ihA ihC =>
      rcases Finset.mem_insert.mp h with rfl | h
      · exact Finset.Subset.rfl
      · rcases Finset.mem_union.mp h with hA | hC
        · intro D hD
          exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (ihA hA hD))
        · intro D hD
          exact Finset.mem_insert_of_mem (Finset.mem_union_right _ (ihC hC hD))
  | impl A C ihA ihC =>
      rcases Finset.mem_insert.mp h with rfl | h
      · exact Finset.Subset.rfl
      · rcases Finset.mem_union.mp h with hA | hC
        · intro D hD
          exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (ihA hA hD))
        · intro D hD
          exact Finset.mem_insert_of_mem (Finset.mem_union_right _ (ihC hC hD))

theorem subformulas_closed (A : Formula) : SubformulaClosed (subformulas A) := by
  intro B hB
  exact subformulas_trans hB

theorem atom_mem_subformulas (p : ℕ) (A : Formula) :
    atom p ∈ subformulas A ↔ p ∈ atoms A := by
  induction A <;> simp_all [subformulas, atoms]

theorem problem_closed (Γ : Finset Formula) (A : Formula) :
    SubformulaClosed (problemSubformulas Γ A) := by
  intro B hB D hD
  rcases Finset.mem_union.mp hB with hB | hB
  · exact Finset.mem_union_left _ (subformulas_trans hB hD)
  · obtain ⟨C, hC, hBC⟩ := Finset.mem_biUnion.mp hB
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨C, hC, subformulas_trans hBC hD⟩)

theorem problem_contains (Γ : Finset Formula) (A : Formula) :
    A ∈ problemSubformulas Γ A ∧ Γ ⊆ problemSubformulas Γ A := by
  constructor
  · exact Finset.mem_union_left _ (self_mem_subformulas A)
  · intro B hB
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨B, hB, self_mem_subformulas B⟩)

theorem atom_mem_problem (Γ : Finset Formula) (A : Formula) (p : ℕ) :
    atom p ∈ problemSubformulas Γ A ↔ p ∈ problemAtoms Γ A := by
  simp [problemSubformulas, problemAtoms, atom_mem_subformulas]

theorem problem_support (Γ : Finset Formula) (A : Formula) :
    atoms A ⊆ problemAtoms Γ A ∧ ∀ B ∈ Γ, atoms B ⊆ problemAtoms Γ A := by
  constructor
  · exact Finset.subset_union_left
  · intro B hB p hp
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨B, hB, hp⟩)

end Lemmatheca.ProofTheory.Intuitionistic.FiniteModels
