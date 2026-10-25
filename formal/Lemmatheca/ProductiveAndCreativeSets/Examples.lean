import Lemmatheca.ProductiveAndCreativeSets.Iteration

/-! The invalid-input example and a hard set that is not enumerable. -/
namespace Lemmatheca.Entry.ProductiveAndCreativeSets

open Lemmatheca.ComputabilityTheory
open UniversalComputation EffectiveEnumerations ProductiveAndCreativeSets

theorem constant_zero_invalid_input (q : ℕ) (hq : ∀ x, phi q x = Part.some 0) :
    indexSet q = Set.univ ∧ q ∈ haltingDiagonal ∧ ¬ indexSet q ⊆ haltingDiagonalᶜ := by
  have hall : ∀ x, (phi q x).Dom := fun x => by rw [hq x]; trivial
  have hK : q ∈ haltingDiagonal := hall q
  exact ⟨Set.eq_univ_of_forall hall, hK, fun hsub => hsub (hall q) hK⟩

def hardNonenumerable : Set ℕ :=
  {m | (∃ n ∈ haltingDiagonal, 2 * n = m) ∨
    (∃ n, n ∉ haltingDiagonal ∧ 2 * n + 1 = m)}

theorem hard_embeddings :
    Computable (fun n : ℕ => 2 * n) ∧ Computable (fun n : ℕ => 2 * n + 1) ∧
      (∀ n, 2 * n ∈ hardNonenumerable ↔ n ∈ haltingDiagonal) ∧
        ∀ n, 2 * n + 1 ∈ hardNonenumerable ↔ n ∉ haltingDiagonal := by
  have heven : Computable (fun n : ℕ => 2 * n) :=
    Primrec.nat_mul.to_comp.comp (Computable.const 2) Computable.id
  refine ⟨heven, Computable.succ.comp heven, ?_, ?_⟩
  · intro n
    constructor
    · rintro (⟨m, hm, heq⟩ | ⟨m, hm, heq⟩)
      · have hmn : m = n := by omega
        exact hmn ▸ hm
      · omega
    · intro hn
      exact Or.inl ⟨n, hn, rfl⟩
  · intro n
    constructor
    · rintro (⟨m, hm, heq⟩ | ⟨m, hm, heq⟩)
      · omega
      · have hmn : m = n := by omega
        exact hmn ▸ hm
    · intro hn
      exact Or.inr ⟨n, hn, rfl⟩

theorem hard_receives_enumerable {A : ℕ → Prop} (hA : REPred A) :
    A ≤₀ hardNonenumerable := by
  exact (diagonal_complete hA).trans
    ⟨fun n => 2 * n, hard_embeddings.1, fun n => (hard_embeddings.2.2.1 n).symm⟩

theorem hard_not_enumerable : ¬ REPred hardNonenumerable := by
  intro hD
  apply haltingDiagonal_complement_not_enumerable
  exact (enumerable_preimage hD hard_embeddings.2.1).of_eq
    (fun n => hard_embeddings.2.2.2 n)

theorem hard_not_creative : ¬ Creative hardNonenumerable := by
  exact fun h => hard_not_enumerable h.1

end Lemmatheca.Entry.ProductiveAndCreativeSets
