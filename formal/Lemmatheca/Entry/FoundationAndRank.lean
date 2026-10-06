import Lemmatheca.SetTheory.NaturalNumbersAsSets
import Lemmatheca.SetTheory.FoundationAndRank

/-! Particular examples and counterexamples for the human entry. -/

set_option autoImplicit false

namespace Lemmatheca.Entry.FoundationAndRank
open Lemmatheca.SetTheory.FoundationAndRank
open scoped ZFSet Ordinal
universe u v

theorem membership_not_transitive :
    let z : ZFSet.{u} := ∅
    let a : ZFSet.{u} := {z}
    let b : ZFSet.{u} := {a}
    z ∈ a ∧ a ∈ b ∧ z ∉ b ∧ ZFSet.IsTransitive ({z, a, b} : ZFSet.{u}) := by
  dsimp
  refine ⟨by simp,by simp,?_,?_⟩
  · simp only [ZFSet.mem_singleton]
    intro h
    have hm : (∅ : ZFSet.{u}) ∈ ({∅} : ZFSet.{u}) := by simp
    rw [← h] at hm
    exact ZFSet.notMem_empty _ hm
  · intro y hy z hz
    simp only [ZFSet.mem_insert_iff, ZFSet.mem_singleton] at hy ⊢
    rcases hy with rfl | rfl | rfl
    · exact (ZFSet.notMem_empty z hz).elim
    · exact Or.inl (ZFSet.mem_singleton.mp hz)
    · exact Or.inr (Or.inl (ZFSet.mem_singleton.mp hz))

theorem rank_inclusion_not_strict :
    let z : ZFSet.{u} := ∅
    let a : ZFSet.{u} := {z}
    let b : ZFSet.{u} := {a}
    ({b} : ZFSet.{u}) ⊂ ({z, b} : ZFSet.{u}) ∧
      ({b} : ZFSet.{u}).rank = 3 ∧ ({z, b} : ZFSet.{u}).rank = 3 ∧
      ({a, b} : ZFSet.{u}).rank = 3 ∧ b.rank = 2 ∧ a.rank = 1 := by
  dsimp
  have hs : (∅ : ZFSet.{u}) ≠ ({{∅}} : ZFSet.{u}) := by
    intro h
    have hm : ({∅} : ZFSet.{u}) ∈ ({{∅}} : ZFSet.{u}) := by simp
    rw [← h] at hm
    exact ZFSet.notMem_empty _ hm
  have ht : ({{{∅}}} : ZFSet.{u}) ⊂ ({∅,{{∅}}} : ZFSet.{u}) := by
    change ({{{∅}}} : ZFSet.{u}) ≤ ({∅,{{∅}}} : ZFSet.{u}) ∧
      ¬ ({∅,{{∅}}} : ZFSet.{u}) ≤ ({{{∅}}} : ZFSet.{u})
    constructor
    · intro y hy
      exact ZFSet.mem_pair.mpr (Or.inr (ZFSet.mem_singleton.mp hy))
    · intro h
      exact hs (ZFSet.mem_singleton.mp (h (ZFSet.mem_pair.mpr (Or.inl rfl))))
  refine ⟨ht,?_,?_,?_,?_,?_⟩ <;>
    norm_num [ZFSet.rank_pair,Order.succ_eq_add_one]

theorem omega_rank_size :
    ZFSet.omega.{u}.rank = Ordinal.omega0 ∧ ZFSet.omega.{u}.card = Cardinal.aleph0 ∧
    ({ZFSet.omega} : ZFSet.{u}).rank = Ordinal.omega0 + 1 ∧
    ({{ZFSet.omega}} : ZFSet.{u}).rank = Ordinal.omega0 + 2 ∧
    ({ZFSet.omega} : ZFSet.{u}).card = 1 ∧ ({{ZFSet.omega}} : ZFSet.{u}).card = 1 := by
  rw [Lemmatheca.SetTheory.NaturalNumbersAsSets.omega_eq_ordinal]
  norm_num [Order.succ_eq_add_one,Ordinal.card_toZFSet,Ordinal.card_omega0,add_assoc]

theorem closure_examples :
    let z : ZFSet.{u} := ∅
    let a : ZFSet.{u} := {z}
    let b : ZFSet.{u} := {a}
    let x : ZFSet.{u} := {a, b}
    transitiveClosure x = {z, a, b} ∧ transitiveClosure ({x} : ZFSet.{u}) = {z, a, b, x} ∧
      transitiveClosure (∅ : ZFSet.{u}) = ∅ ∧ x ∉ transitiveClosure x := by
  dsimp
  let z : ZFSet.{u} := ∅
  let a : ZFSet.{u} := {z}
  let b : ZFSet.{u} := {a}
  let x : ZFSet.{u} := {a,b}
  let T : ZFSet.{u} := {z,a,b}
  let U : ZFSet.{u} := {z,a,b,x}
  have hT : T.IsTransitive := membership_not_transitive.2.2.2
  have hU : U.IsTransitive := by
    intro y hy w hw
    change y ∈ ({z,a,b,x} : ZFSet.{u}) at hy
    simp only [ZFSet.mem_insert_iff,ZFSet.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl | rfl
    · exact (ZFSet.notMem_empty w hw).elim
    · have he := ZFSet.mem_singleton.mp hw
      rw [he]
      simp [U]
    · have he := ZFSet.mem_singleton.mp hw
      rw [he]
      simp [U]
    · rcases ZFSet.mem_pair.mp hw with rfl | rfl <;> simp [U]
  have hc := transitiveClosure_spec x
  have hc' := transitiveClosure_spec ({x} : ZFSet.{u})
  have ha : a ∈ transitiveClosure x := hc.2.1 (ZFSet.mem_pair.mpr (Or.inl rfl))
  have hb : b ∈ transitiveClosure x := hc.2.1 (ZFSet.mem_pair.mpr (Or.inr rfl))
  have hz : z ∈ transitiveClosure x := hc.1 a ha (ZFSet.mem_singleton.mpr rfl)
  have hX : transitiveClosure x = T := by
    apply le_antisymm
    · apply hc.2.2 T hT
      intro y hy
      rcases ZFSet.mem_pair.mp hy with rfl | rfl <;> simp [T]
    · intro y hy
      change y ∈ ({z,a,b} : ZFSet.{u}) at hy
      simp only [ZFSet.mem_insert_iff,ZFSet.mem_singleton] at hy
      rcases hy with rfl | rfl | rfl
      · exact hz
      · exact ha
      · exact hb
  have hx' : x ∈ transitiveClosure ({x} : ZFSet.{u}) := hc'.2.1 (ZFSet.mem_singleton.mpr rfl)
  have hinc : transitiveClosure x ⊆ transitiveClosure ({x} : ZFSet.{u}) :=
    hc.2.2 _ hc'.1 (hc'.1 x hx')
  have hX' : transitiveClosure ({x} : ZFSet.{u}) = U := by
    apply le_antisymm
    · apply hc'.2.2 U hU
      intro y hy
      rw [ZFSet.mem_singleton.mp hy]
      simp [U]
    · intro y hy
      change y ∈ ({z,a,b,x} : ZFSet.{u}) at hy
      simp only [ZFSet.mem_insert_iff,ZFSet.mem_singleton] at hy
      rcases hy with rfl | rfl | rfl | rfl
      · exact hinc hz
      · exact hinc ha
      · exact hinc hb
      · exact hx'
  refine ⟨hX,hX',transitiveClosure_fixed ∅ ZFSet.isTransitive_empty,?_⟩
  intro hx
  rw [hX] at hx
  change x ∈ ({z,a,b} : ZFSet.{u}) at hx
  simp only [ZFSet.mem_insert_iff,ZFSet.mem_singleton] at hx
  have hax : a ∈ x := ZFSet.mem_pair.mpr (Or.inl rfl)
  have hbx : b ∈ x := ZFSet.mem_pair.mpr (Or.inr rfl)
  rcases hx with he | he | he
  · rw [he] at hax
    exact ZFSet.notMem_empty a hax
  · rw [he] at hbx
    have hbz : b = z := ZFSet.mem_singleton.mp hbx
    have hab : a ∈ b := ZFSet.mem_singleton.mpr rfl
    rw [hbz] at hab
    exact ZFSet.notMem_empty a hab
  · rw [he] at hbx
    exact ZFSet.mem_irrefl b hbx

end Lemmatheca.Entry.FoundationAndRank
