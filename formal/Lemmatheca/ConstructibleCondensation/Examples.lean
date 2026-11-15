import Lemmatheca.ConstructibleCondensation.Heights

namespace Lemmatheca.Entry.ConstructibleCondensation
open Lemmatheca.SetTheory.ConstructibleHierarchy
open Lemmatheca.SetTheory.ConstructibleCondensation
open scoped ZFSet Ordinal
universe u

theorem first_levels :
    level (1 : Ordinal.{u}) = {(0 : Ordinal.{u}).toZFSet} ∧
    level (2 : Ordinal.{u}) = (2 : Ordinal.{u}).toZFSet := by
  constructor
  · simpa only [Ordinal.toZFSet_zero] using
      (Lemmatheca.SetTheory.ConstructibleHierarchy.first_levels.{u}).2.1
  · rw [Lemmatheca.SetTheory.ConstructibleHierarchy.first_levels.2.2]
    have h1 : (1 : Ordinal.{u}).toZFSet = {(∅ : ZFSet.{u})} := by
      rw [show (1 : Ordinal.{u}) = 0+1 from (zero_add _).symm,
        Ordinal.toZFSet_add_one, Ordinal.toZFSet_zero]
      apply ZFSet.ext
      intro z
      simp only [ZFSet.mem_insert_iff, ZFSet.notMem_empty, or_false, ZFSet.mem_singleton]
    have h2 : (2 : Ordinal.{u}).toZFSet =
        insert (1 : Ordinal.{u}).toZFSet (1 : Ordinal.{u}).toZFSet := by
      simpa only [one_add_one_eq_two] using Ordinal.toZFSet_add_one (1 : Ordinal.{u})
    rw [h2, h1]
    apply ZFSet.ext
    intro z
    simp only [ZFSet.mem_insert_iff, ZFSet.mem_singleton]
    exact or_comm


theorem singleton_one_separates :
    {(1 : Ordinal.{u}).toZFSet} ∈ level (3 : Ordinal.{u}) ∧
    {(1 : Ordinal.{u}).toZFSet} ∉ (3 : Ordinal.{u}).toZFSet := by
  constructor
  · have h1 : (1 : Ordinal.{u}).toZFSet ∈ level (2 : Ordinal.{u}) :=
      (level_ordinal_part 2 1).mpr (by simpa only [one_add_one_eq_two] using lt_add_one (1 : Ordinal.{u}))
    have h := (singletonIntoDef (level (2 : Ordinal.{u})) ⟨_,h1⟩).property
    rw [(singletonIntoDef_spec (level (2 : Ordinal.{u}))).1] at h
    simpa only [show (3 : Ordinal.{u}) = 2+1 from rfl, level_successor] using h
  · intro h
    have ho := (ZFSet.isOrdinal_toZFSet (3 : Ordinal.{u})).mem h
    have h01 : (0 : Ordinal.{u}).toZFSet ∈ (1 : Ordinal.{u}).toZFSet :=
      Ordinal.toZFSet_mem_toZFSet_iff.mpr zero_lt_one
    have h1s : (1 : Ordinal.{u}).toZFSet ∈ ({(1 : Ordinal.{u}).toZFSet} : ZFSet.{u}) :=
      ZFSet.mem_singleton.mpr rfl
    have he := ZFSet.mem_singleton.mp (ho.isTransitive.mem_trans h01 h1s)
    exact zero_ne_one (Ordinal.toZFSet_injective he)


theorem three_counterexample :
    ((3 : Ordinal.{u}).toZFSet).IsTransitive ∧
      ordinalHeight (3 : Ordinal.{u}).toZFSet = 3 ∧
      ∀ a : Ordinal.{u}, (3 : Ordinal.{u}).toZFSet ≠ level a := by
  refine ⟨(ZFSet.isOrdinal_toZFSet _).isTransitive, height_ordinal _, ?_⟩
  intro a he
  have ha : a = 3 := by
    rw [← height_level a, ← he, height_ordinal]
  subst a
  exact singleton_one_separates.2 (he.symm ▸ singleton_one_separates.1)


end Lemmatheca.Entry.ConstructibleCondensation
