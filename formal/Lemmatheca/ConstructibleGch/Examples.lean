import Lemmatheca.ConstructibleGch.InternalCardinals

namespace Lemmatheca.Entry.ConstructibleGch
open Lemmatheca.SetTheory.ConstructibleHierarchy
open scoped Ordinal ZFSet
universe u

theorem empty_subset_stage_failure :
    (∅ : ZFSet.{u}) ⊆ (0 : Ordinal.{u}).toZFSet ∧
      ¬ ∃ a < (1 : Ordinal.{u}), (∅ : ZFSet.{u}) ∈ level a := by
  constructor
  · intro x hx
    exact (ZFSet.notMem_empty x hx).elim
  · rintro ⟨a,ha,hx⟩
    have he : a = 0 := Order.lt_one_iff.mp ha
    rw [he, level_zero] at hx
    exact ZFSet.notMem_empty ∅ hx

end Lemmatheca.Entry.ConstructibleGch
