import Lemmatheca.CreativeSetsAndComputableIsomorphism.Classification
import Lemmatheca.ProductiveAndCreativeSets.Examples

namespace Lemmatheca.Entry.CreativeSetsAndComputableIsomorphism

open Lemmatheca.ComputabilityTheory
open UniversalComputation ProductiveAndCreativeSets CreativeIsomorphism

/-- A concrete partial function sharing divergence at zero with bottom. -/
def onlyAtOne (z : ℕ) : Part ℕ := if z = 1 then Part.some 0 else Part.none

theorem zero_answer_not_function :
    Partrec onlyAtOne ∧ onlyAtOne 0 = Part.none ∧ onlyAtOne 1 = Part.some 0 ∧
      onlyAtOne ≠ (fun _ : ℕ => Part.none) := by
  have ht : Computable (fun z : ℕ => decide (z = 1)) :=
    Primrec.eq.decide.to_comp.comp Computable.id (Computable.const 1)
  have hp : Partrec onlyAtOne :=
    (Partrec.cond ht (Partrec.const' (Part.some 0)) Partrec.none).of_eq
      (fun z => by simp [onlyAtOne])
  refine ⟨hp, by simp [onlyAtOne], by simp [onlyAtOne], ?_⟩
  intro h
  have hh := congrFun h 1
  simp [onlyAtOne] at hh

theorem parity_injective_reduction :
    Computable (fun n : ℕ => 2 * n) ∧ Function.Injective (fun n : ℕ => 2 * n) ∧
      ∀ n, n ∈ haltingDiagonal ↔ 2 * n ∈ ProductiveAndCreativeSets.hardNonenumerable := by
  refine ⟨Lemmatheca.Entry.ProductiveAndCreativeSets.hard_embeddings.1, ?_, ?_⟩
  · intro n m h
    change 2 * n = 2 * m at h
    omega
  · intro n
    exact (Lemmatheca.Entry.ProductiveAndCreativeSets.hard_embeddings.2.2.1 n).symm

theorem parity_not_isomorphic :
    ¬ Myhill.ComputablyIsomorphic ProductiveAndCreativeSets.hardNonenumerable haltingDiagonal := by
  intro hi
  have hr := (Myhill.myhill ProductiveAndCreativeSets.hardNonenumerable haltingDiagonal).mpr hi
  exact Lemmatheca.Entry.ProductiveAndCreativeSets.hard_not_enumerable
    (ComputableReductions.enumerable_preimage hr.1.to_many_one haltingDiagonal_enumerable)

end Lemmatheca.Entry.CreativeSetsAndComputableIsomorphism
