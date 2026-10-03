import Lemmatheca.SetTheory.WellOrders
import Mathlib.SetTheory.ZFC.Ordinal
import Mathlib.SetTheory.Ordinal.Family

/-! Von Neumann sets are related to mathlib's well-order types by `Ordinal.toZFSetIso`.
A `ZFSet.{u}` has small membership domains; arbitrary `Set Ordinal.{u}` need not.
The new statements in this module are intentionally unfinished at pipeline step 4. -/

namespace Lemmatheca.SetTheory

open Ordinal Order
open scoped ZFSet Ordinal
universe u

theorem ordinal_union (S : ZFSet.{u}) (hS : ∀ a ∈ S, ZFSet.IsOrdinal a) :
    ZFSet.IsOrdinal (⋃₀ S) := by sorry

theorem ordinal_union_lub (S : ZFSet.{u}) (hS : ∀ a ∈ S, ZFSet.IsOrdinal a) :
    (∀ a ∈ S, a ⊆ ⋃₀ S) ∧
    ∀ b : ZFSet.{u}, ZFSet.IsOrdinal b → (∀ a ∈ S, a ⊆ b) → ⋃₀ S ⊆ b := by sorry

theorem ordinal_limit_union (a : ZFSet.{u}) (ha : a.IsOrdinal) :
    IsSuccLimit a.rank ↔ a ≠ ∅ ∧ ZFSet.sUnion a = a := by sorry

theorem ordinal_union_limit (S : ZFSet.{u}) (hS : ∀ a ∈ S, a.IsOrdinal)
    (hne : S.Nonempty) (hng : ∀ a ∈ S, ∃ b ∈ S, a ∈ b) :
    IsSuccLimit (ZFSet.sUnion S).rank := by sorry

theorem no_set_of_all_ordinals :
    ¬ ∃ S : ZFSet.{u}, ∀ a : ZFSet.{u}, a.IsOrdinal → a ∈ S := by sorry

end Lemmatheca.SetTheory
