import Lemmatheca.ManyCohenReals.Names

namespace Lemmatheca.Entry.ManyCohenReals
open Cardinal
universe u

/-- The column bounds for one or countably many columns still hold at the CH cardinal. -/
theorem weak_bounds_at_CH :
    (1 : Cardinal.{u}) ≤ Cardinal.aleph 1 ∧ ℵ₀ ≤ Cardinal.aleph 1 := by
  exact ⟨Cardinal.one_le_aleph0.trans (Cardinal.aleph0_le_aleph 1),
    Cardinal.aleph0_le_aleph 1⟩

/-- A preserved old lower bound of aleph three rules out the suggested exact value aleph two. -/
theorem larger_bound_excludes_aleph_two (c : Cardinal.{u}) (hc : Cardinal.aleph 3 ≤ c) :
    c ≠ Cardinal.aleph 2 := by
  intro he
  have hlt : Cardinal.aleph.{u} 2 < Cardinal.aleph 3 :=
    Cardinal.aleph_lt_aleph.mpr (by norm_num)
  exact (not_le_of_gt hlt) (he ▸ hc)

end Lemmatheca.Entry.ManyCohenReals
