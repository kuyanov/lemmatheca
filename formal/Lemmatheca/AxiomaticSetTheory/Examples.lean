import Lemmatheca.AxiomaticSetTheory.AxiomaticSetTheory

/-! Particular examples and counterexamples for the human entry. -/

set_option autoImplicit false

namespace Lemmatheca.Entry.AxiomaticSetTheory
open Lemmatheca.SetTheory.AxiomaticSetTheory
open scoped ZFSet
universe u

theorem foundation_two_minima :
    let z : ZFSet.{u} := ∅
    let one : ZFSet.{u} := {z}
    let two : ZFSet.{u} := {z, one}
    let A : ZFSet.{u} := {one, {two}}
    one ∈ A ∧ ({two} : ZFSet.{u}) ∈ A ∧ one ≠ ∅ ∧ ({two} : ZFSet.{u}) ≠ ∅ ∧
      one ≠ ({two} : ZFSet.{u}) ∧ one ∩ A = ∅ ∧ ({two} : ZFSet.{u}) ∩ A = ∅ := by
  dsimp
  have hs (x : ZFSet.{u}) : ({x} : ZFSet.{u}) ≠ ∅ := by
    intro h
    have hm : x ∈ ({x} : ZFSet.{u}) := ZFSet.mem_singleton.mpr rfl
    rw [h] at hm
    exact ZFSet.notMem_empty x hm
  have hp : ({∅, {∅}} : ZFSet.{u}) ≠ ({∅} : ZFSet.{u}) := by
    intro h
    have hm : ({∅} : ZFSet.{u}) ∈ ({∅,{∅}} : ZFSet.{u}) := by simp
    rw [h, ZFSet.mem_singleton] at hm
    exact hs ∅ hm
  have hn : ({∅, {∅}} : ZFSet.{u}) ≠ ({{∅,{∅}}} : ZFSet.{u}) := by
    intro h
    have hm : ({∅,{∅}} : ZFSet.{u}) ∈ ({{∅,{∅}}} : ZFSet.{u}) := by simp
    rw [← h] at hm
    exact ZFSet.mem_irrefl _ hm
  have hdistinct : ({∅} : ZFSet.{u}) ≠ ({{∅, {∅}}} : ZFSet.{u}) := by
    intro h
    have he := ZFSet.singleton_injective h
    have hm : (∅ : ZFSet.{u}) ∈ ({∅, {∅}} : ZFSet.{u}) := by simp
    rw [← he] at hm
    exact ZFSet.notMem_empty _ hm
  refine ⟨by simp, by simp, hs ∅, hs _, hdistinct, ?_, ?_⟩
  · apply ZFSet.ext
    intro x
    simp only [ZFSet.mem_inter, ZFSet.mem_pair, ZFSet.mem_singleton, ZFSet.notMem_empty]
    simp only [iff_false, not_and, not_or]
    rintro rfl
    exact ⟨Ne.symm (hs ∅), Ne.symm (hs _)⟩
  · apply ZFSet.ext
    intro x
    simp only [ZFSet.mem_inter, ZFSet.mem_pair, ZFSet.mem_singleton, ZFSet.notMem_empty]
    simp only [iff_false, not_and, not_or]
    rintro rfl
    exact ⟨hp,hn⟩

end Lemmatheca.Entry.AxiomaticSetTheory
