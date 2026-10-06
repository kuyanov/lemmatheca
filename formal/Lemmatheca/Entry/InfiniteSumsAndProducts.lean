import Lemmatheca.SetTheory.InfiniteSumsAndProducts

/-! Particular examples and counterexamples for the human entry. -/

namespace Lemmatheca.Entry.InfiniteSumsAndProducts
open Lemmatheca.SetTheory.InfiniteSumsAndProducts
open Ordinal Order Set Function
open scoped Ordinal
universe u

/-- This is a statement about the strength of the bound, not about the value
of the continuum. For example, aleph indexed by omega_1 is singular and has
cofinality aleph_1. No independence assertion is encoded here. -/
theorem uncountable_cofinality_not_regularity :
    ∃ k : Cardinal.{u}, Cardinal.aleph0 < k.ord.cof ∧ k.IsSingular := by
  let k : Cardinal.{u} := Cardinal.aleph (Ordinal.omega 1)
  have hl : IsSuccLimit (Ordinal.omega (1 : Ordinal.{u})) :=
    Cardinal.isSuccLimit_omega 1
  have hc : k.ord.cof = Cardinal.aleph 1 := by
    rw [Cardinal.ord_aleph, Ordinal.cof_omega hl]
    exact Cardinal.cof_omega_one
  refine ⟨k, ?_, ?_⟩
  · rw [hc]
    simpa only [← Cardinal.aleph_zero] using (Cardinal.aleph_lt_aleph.mpr (show (0 : Ordinal.{u}) < 1 by simp))
  · refine ⟨Cardinal.aleph0_le_aleph _, ?_⟩
    rw [hc]
    simpa [k] using (Cardinal.aleph_lt_aleph.mpr ((natCast_lt_omega0 1).trans (Ordinal.omega0_lt_omega_one))).ne

end Lemmatheca.Entry.InfiniteSumsAndProducts
