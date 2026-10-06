import Lemmatheca.SetTheory.CumulativeHierarchy

/-! Particular examples and counterexamples for the human entry. -/

set_option autoImplicit false
universe u
namespace Lemmatheca.Entry.CumulativeHierarchy
open Lemmatheca.SetTheory.CumulativeHierarchy
open Order
open scoped ZFSet Ordinal Cardinal
open Lemmatheca.SetTheory.FoundationAndRank

/-- A singleton of omega is finite but not hereditarily finite. -/
theorem finite_vs_hereditary :
    Finite ({(ω : Ordinal.{u}).toZFSet} : ZFSet.{u}) ∧
    ¬ HereditarilyFinite ({(ω : Ordinal.{u}).toZFSet} : ZFSet.{u}) ∧
    (ω : Ordinal.{u}).toZFSet.rank = ω ∧
    ({(ω : Ordinal.{u}).toZFSet} : ZFSet.{u}).rank = ω + 1 ∧
    (ZFSet.vonNeumann (ω : Ordinal.{u})).rank = ω := by
  refine ⟨?_, ?_, Ordinal.rank_toZFSet _, ?_, ZFSet.rank_vonNeumann _⟩
  · apply Set.finite_coe_iff.mpr
    simp
  · rw [(hereditarilyFinite_iff _).1, ZFSet.rank_singleton, Ordinal.rank_toZFSet]
    exact not_lt.mpr (Order.le_succ _)
  · simp [Order.succ_eq_add_one]

end Lemmatheca.Entry.CumulativeHierarchy
