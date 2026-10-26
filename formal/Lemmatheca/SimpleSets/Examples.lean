import Lemmatheca.SimpleSets.Construction

/-! The least-certificate and reserved-even-number questions. -/
namespace Lemmatheca.Entry.SimpleSets

open Lemmatheca.ComputabilityTheory
open UniversalComputation EffectiveEnumerations SimpleSets

theorem total_index_selection (q : ℕ) (hq : ∀ x, (phi q x).Dom) :
    indexSet q = Set.univ ∧ (selector q).Dom ∧
      ∀ x ∈ selector q, 2 * q < x ∧ x ≠ 0 := by
  refine ⟨Set.eq_univ_of_forall hq, ?_, ?_⟩
  · exact (selector_domain q).mpr ⟨2 * q + 1, by omega, hq _⟩
  · intro x hx
    have hs := (selector_sound hx).1
    exact ⟨hs, by omega⟩

def evenNumbers : Set ℕ := Set.range (fun n : ℕ => 2 * n)

theorem even_numbers_properties :
    ComputablePred evenNumbers ∧ REPred evenNumbers ∧ evenNumbers.Infinite := by
  have htest : PrimrecPred (fun x : ℕ => x % 2 = 0) :=
    Primrec.eq.comp (Primrec.nat_mod.comp Primrec.id (Primrec.const 2)) (Primrec.const 0)
  have hdec : ComputablePred evenNumbers := htest.computablePred.of_eq (fun x => by
    change x % 2 = 0 ↔ ∃ n, 2 * n = x
    constructor
    · intro hx
      exact ⟨x / 2, by omega⟩
    · rintro ⟨n, rfl⟩
      omega)
  exact ⟨hdec, hdec.to_re,
    Set.infinite_range_of_injective (fun a b h => by omega)⟩

end Lemmatheca.Entry.SimpleSets
