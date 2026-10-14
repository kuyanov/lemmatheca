import Lemmatheca.MathematicalLogic.PropositionalCompactness

/-! Illustrative infinite theories and the semantic infinitary-conjunction boundary.
The infinitary requirement type is deliberately distinct from finite PropFormula. -/

namespace Lemmatheca.Entry.PropositionalCompactness

open Lemmatheca.MathematicalLogic
open Lemmatheca.MathematicalLogic.PropositionalCompactness

def positiveTheory : Theory ℕ := Set.range PropFormula.atom

theorem all_true_models_positive :
    ModelsTheory (fun _ => true) positiveTheory := by
  rintro A ⟨n, rfl⟩
  rfl

theorem no_finite_equivalent_positive (Δ : Finset (PropFormula ℕ))
    (hΔ : (↑Δ : Set (PropFormula ℕ)) ⊆ positiveTheory) :
    ∃ v : Valuation ℕ, SatisfiesContext v Δ ∧ ¬ ModelsTheory v positiveTheory := by
  obtain ⟨k, hk⟩ := Finset.exists_notMem (contextAtoms Δ)
  let v : Valuation ℕ := fun n => if n = k then false else true
  refine ⟨v, ?_, ?_⟩
  · intro A hA
    obtain ⟨n, rfl⟩ := hΔ hA
    have hn : n ∈ contextAtoms Δ :=
      Finset.mem_biUnion.mpr ⟨.atom n, hA, Finset.mem_singleton_self n⟩
    have hnk : n ≠ k := fun he => hk (he ▸ hn)
    simp [Satisfies, eval, v, hnk]
  · intro hv
    have h := hv (.atom k) ⟨k, rfl⟩
    simp [Satisfies, eval, v] at h

theorem singleton_positive_entails (n : ℕ) :
    Entails {PropFormula.atom n} (PropFormula.atom n) := by
  intro v hv
  exact hv (.atom n) (Finset.mem_singleton_self _)

/-- Positive single-atom requirements, together with the negation of their infinite conjunction. -/
inductive InfiniteRequirement
  | positive : ℕ → InfiniteRequirement
  | notAll : InfiniteRequirement
  deriving DecidableEq

def SatisfiesInfinite (v : Valuation ℕ) : InfiniteRequirement → Prop
  | .positive n => v n = true
  | .notAll => ¬ ∀ n, v n = true

/-- Set one unrequired atom false and every other atom true. -/
def missingAtomValuation (k : ℕ) : Valuation ℕ :=
  fun n => if n = k then false else true

theorem finite_infinite_requirement_witness (Δ : Finset InfiniteRequirement) :
    ∃ k : ℕ, InfiniteRequirement.positive k ∉ Δ ∧
      ∀ A ∈ Δ, SatisfiesInfinite (missingAtomValuation k) A := by
  let indices : Finset ℕ := Δ.biUnion (fun A => match A with
    | .positive n => {n}
    | .notAll => ∅)
  obtain ⟨k, hk⟩ := Finset.exists_notMem indices
  have hpos : InfiniteRequirement.positive k ∉ Δ := by
    intro h
    apply hk
    exact Finset.mem_biUnion.mpr ⟨.positive k, h, Finset.mem_singleton_self k⟩
  refine ⟨k, hpos, fun A hA => ?_⟩
  cases A with
  | positive n =>
    have hn : n ∈ indices :=
      Finset.mem_biUnion.mpr ⟨.positive n, hA, Finset.mem_singleton_self n⟩
    have hnk : n ≠ k := fun he => hk (he ▸ hn)
    simp [SatisfiesInfinite, missingAtomValuation, hnk]
  | notAll =>
    intro hall
    have h := hall k
    simp [missingAtomValuation] at h

theorem infinite_requirements_unsatisfiable :
    ¬ ∃ v : Valuation ℕ, ∀ A : InfiniteRequirement, SatisfiesInfinite v A := by
  rintro ⟨v, hv⟩
  exact hv .notAll (fun n => hv (.positive n))

end Lemmatheca.Entry.PropositionalCompactness
