import Lemmatheca.SetTheory.WellOrders
import Mathlib.SetTheory.ZFC.Ordinal

/-! Von Neumann sets are related to mathlib's well-order types by `Ordinal.toZFSetIso`.
A `ZFSet.{u}` has small membership domains; arbitrary `Set Ordinal.{u}` need not.
Unions and limit stages are expressed directly in the von Neumann representation. -/

namespace Lemmatheca.SetTheory

open Ordinal Order
open scoped ZFSet Ordinal
universe u

theorem ordinal_union (S : ZFSet.{u}) (hS : ∀ a ∈ S, ZFSet.IsOrdinal a) :
    ZFSet.IsOrdinal (⋃₀ S) := by
  refine ZFSet.isOrdinal_iff_forall_mem_isOrdinal.mpr ⟨?_, ?_⟩
  · exact ZFSet.IsTransitive.sUnion' (fun a ha => (hS a ha).isTransitive)
  · intro a ha
    obtain ⟨b, hb, hab⟩ := ZFSet.mem_sUnion.mp ha
    exact (hS b hb).mem hab

theorem ordinal_union_lub (S : ZFSet.{u}) (_hS : ∀ a ∈ S, ZFSet.IsOrdinal a) :
    (∀ a ∈ S, a ⊆ ⋃₀ S) ∧
    ∀ b : ZFSet.{u}, ZFSet.IsOrdinal b → (∀ a ∈ S, a ⊆ b) → ⋃₀ S ⊆ b := by
  constructor
  · intro a ha x hx
    exact ZFSet.mem_sUnion_of_mem hx ha
  · intro b _ hb x hx
    obtain ⟨a, ha, hxa⟩ := ZFSet.mem_sUnion.mp hx
    exact hb a ha hxa

theorem ordinal_limit_union (a : ZFSet.{u}) (ha : a.IsOrdinal) :
    IsSuccLimit a.rank ↔ a ≠ ∅ ∧ ZFSet.sUnion a = a := by
  have hz : a.rank ≠ 0 ↔ a ≠ ∅ := by
    change ¬ a.rank = 0 ↔ ¬ a = ∅
    rw [← ZFSet.rank_empty, ha.rank_inj ZFSet.isOrdinal_empty]
  rw [Ordinal.isSuccLimit_iff, hz]
  refine and_congr_right fun hn => ?_
  rw [Order.isSuccPrelimit_iff_succ_lt]
  constructor
  · intro h
    apply ZFSet.ext
    intro b
    constructor
    · exact fun hb => ha.isTransitive.sUnion_subset hb
    · intro hb
      have hbr := (ha.mem hb).rank_lt_iff_mem ha |>.mpr hb
      have hc := h b.rank hbr
      rw [Order.succ_eq_add_one] at hc
      have hm : (b.rank + 1).toZFSet ∈ a :=
        (ZFSet.isOrdinal_toZFSet _).rank_lt_iff_mem ha |>.mp (by simpa using hc)
      apply ZFSet.mem_sUnion_of_mem _ hm
      rw [Ordinal.toZFSet_add_one, (ha.mem hb).toZFSet_rank_eq]
      simp
  · intro he b hb
    have hbm : b.toZFSet ∈ a :=
      (ZFSet.isOrdinal_toZFSet b).rank_lt_iff_mem ha |>.mp (by simpa using hb)
    rw [← he] at hbm
    obtain ⟨c, hc, hbc⟩ := ZFSet.mem_sUnion.mp hbm
    have hbc' : b < c.rank := by
      simpa using ((ZFSet.isOrdinal_toZFSet b).rank_lt_iff_mem (ha.mem hc)).mpr hbc
    exact lt_of_le_of_lt (Order.succ_le_of_lt hbc') (ZFSet.rank_lt_of_mem hc)

theorem ordinal_union_limit (S : ZFSet.{u}) (hS : ∀ a ∈ S, a.IsOrdinal)
    (hne : S.Nonempty) (hng : ∀ a ∈ S, ∃ b ∈ S, a ∈ b) :
    IsSuccLimit (ZFSet.sUnion S).rank := by
  apply (ordinal_limit_union _ (ordinal_union S hS)).mpr
  constructor
  · obtain ⟨a, ha⟩ := hne
    obtain ⟨b, hb, hab⟩ := hng a ha
    have ham := ZFSet.mem_sUnion_of_mem hab hb
    intro he
    simp [he] at ham
  · apply ZFSet.ext
    intro x
    constructor
    · exact fun hx => (ordinal_union S hS).isTransitive.sUnion_subset hx
    · intro hx
      obtain ⟨a, ha, hxa⟩ := ZFSet.mem_sUnion.mp hx
      obtain ⟨b, hb, hab⟩ := hng a ha
      exact ZFSet.mem_sUnion_of_mem hxa (ZFSet.mem_sUnion_of_mem hab hb)

theorem no_set_of_all_ordinals :
    ¬ ∃ S : ZFSet.{u}, ∀ a : ZFSet.{u}, a.IsOrdinal → a ∈ S := by
  rintro ⟨S, hS⟩
  have h := ZFSet.rank_lt_of_mem (hS S.rank.toZFSet (ZFSet.isOrdinal_toZFSet _))
  simp at h

end Lemmatheca.SetTheory
