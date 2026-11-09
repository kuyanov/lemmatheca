import Lemmatheca.MyhillsIsomorphismTheorem.Isomorphism
import Lemmatheca.UniversalComputation.UniversalComputation

namespace Lemmatheca.Entry.MyhillsIsomorphismTheorem

open Lemmatheca.ComputabilityTheory
open Myhill

theorem halting_identity_isomorphism :
    ComputablePermutation (id : ℕ → ℕ) ∧
      (∀ x, x ∈ UniversalComputation.haltingDiagonal ↔
        id x ∈ UniversalComputation.haltingDiagonal) := by
  exact ⟨⟨Computable.id, Function.bijective_id⟩, fun _ => Iff.rfl⟩

theorem two_point_not_isomorphic :
    ¬ ComputablyIsomorphic ({0, 1} : Set ℕ) ({0} : Set ℕ) := by
  rintro ⟨h, ⟨_, hb⟩, hm⟩
  have hzero : h 0 = 0 := by simpa using (hm 0).mp (by simp)
  have hone : h 1 = 0 := by simpa using (hm 1).mp (by simp)
  have hbad := hb.1 (hzero.trans hone.symm)
  norm_num at hbad

end Lemmatheca.Entry.MyhillsIsomorphismTheorem
