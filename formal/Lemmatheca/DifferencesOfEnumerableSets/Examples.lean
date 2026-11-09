import Lemmatheca.DifferencesOfEnumerableSets.Basic
import Lemmatheca.ProductiveAndCreativeSets.Examples

/-! A tagged difference recognizable on neither side, and the absence of a deadline. -/
namespace Lemmatheca.Entry.DifferencesOfEnumerableSets

open Lemmatheca.ComputabilityTheory
open DifferenceEnumerable UniversalComputation LimitComputability
open ProductiveAndCreativeSets

def taggedProposal : Set ℕ :=
  {z | (∃ x, z = 2 * x ∧ x ∈ haltingDiagonal) ∨ ∃ x, z = 2 * x + 1}

def taggedCancellation : Set ℕ := {z | ∃ x, z = 2 * x + 1 ∧ x ∈ haltingDiagonal}

private theorem enumerable_tag (A : Set ℕ) (hA : REPred A) (g : ℕ → ℕ)
    (hg : Computable g) : REPred (fun z => ∃ x, z = g x ∧ x ∈ A) := by
  apply (enumerable_image hA hg).of_eq
  intro z
  constructor
  · rintro ⟨x, hx, hz⟩
    exact ⟨x, hz.symm, hx⟩
  · rintro ⟨x, hz, hx⟩
    exact ⟨x, hx, hz.symm⟩

theorem tagged_difference :
    REPred taggedProposal ∧ REPred taggedCancellation ∧
      hardNonenumerable = taggedProposal \ taggedCancellation ∧
      IsDifferenceEnumerable hardNonenumerable := by
  have hEven := enumerable_tag haltingDiagonal haltingDiagonal_enumerable _ hard_embeddings.1
  have hAll : REPred (Set.univ : Set ℕ) :=
    (show ComputablePred (Set.univ : Set ℕ) from
      ⟨fun _ => isTrue trivial, Computable.const true⟩).to_re
  have hOdd : REPred (fun z => ∃ x : ℕ, z = 2 * x + 1) :=
    (enumerable_tag Set.univ hAll _ hard_embeddings.2.1).of_eq fun z => by simp
  have hProposal : REPred taggedProposal := enumerable_union hEven hOdd
  have hCancellation : REPred taggedCancellation :=
    enumerable_tag haltingDiagonal haltingDiagonal_enumerable _ hard_embeddings.2.1
  have hDifference : hardNonenumerable = taggedProposal \ taggedCancellation := by
    ext z
    simp only [hardNonenumerable, taggedProposal, taggedCancellation, Set.mem_sdiff,
      Set.mem_ofPred_eq]
    constructor
    · rintro (⟨x, hx, hz⟩ | ⟨x, hx, hz⟩)
      · refine ⟨Or.inl ⟨x, hz.symm, hx⟩, ?_⟩
        rintro ⟨y, hy, _⟩
        omega
      · refine ⟨Or.inr ⟨x, hz.symm⟩, ?_⟩
        rintro ⟨y, hy, hyK⟩
        have hxy : x = y := by omega
        exact hx (hxy.symm ▸ hyK)
    · rintro ⟨(⟨x, hz, hx⟩ | ⟨x, hz⟩), hn⟩
      · exact Or.inl ⟨x, hx, hz.symm⟩
      · exact Or.inr ⟨x, fun hx => hn ⟨x, hz, hx⟩, hz.symm⟩
  exact ⟨hProposal, hCancellation, hDifference,
    taggedProposal, taggedCancellation, hProposal, hCancellation, hDifference⟩

theorem tagged_neither_enumerable :
    ¬ REPred hardNonenumerable ∧ ¬ REPred hardNonenumerableᶜ := by
  refine ⟨hard_not_enumerable, ?_⟩
  intro hD
  apply haltingDiagonal_complement_not_enumerable
  exact (enumerable_preimage hD hard_embeddings.1).of_eq fun x =>
    not_congr (hard_embeddings.2.2.1 x)

end Lemmatheca.Entry.DifferencesOfEnumerableSets
