import Lemmatheca.ConstructibleHierarchy.Definability
import Lemmatheca.RankReflection.Reflection
import Lemmatheca.CumulativeHierarchy.CumulativeHierarchy

namespace Lemmatheca.SetTheory.ConstructibleHierarchy
open scoped Ordinal ZFSet
universe u
noncomputable section

/-- The actual transfinite recursion: definable subsets at successors and the
set-indexed union of earlier stages at a nonzero limit. -/
def level (a : Ordinal.{u}) : ZFSet.{u} :=
  Ordinal.limitRecOn a ∅ (fun _ prev => Def prev)
    (fun l _ prev => ZFSet.iUnion (fun b : Set.Iio l => prev b.val b.property))

theorem level_zero : level (0 : Ordinal.{u}) = ∅ := by
  simp only [level,Ordinal.limitRecOn_zero]
theorem level_successor (a : Ordinal.{u}) : level (a+1) = Def (level a) := by
  simp only [level,Ordinal.limitRecOn_add_one]
theorem level_limit (l : Ordinal.{u}) (hl : Order.IsSuccLimit l) :
    level l = ZFSet.iUnion (fun b : Set.Iio l => level b.val) := by
  simp only [level,Ordinal.limitRecOn_limit l _ _ _ hl]
theorem level_limit_members (l : Ordinal.{u}) (hl : Order.IsSuccLimit l)
    (x : ZFSet.{u}) : x ∈ level l ↔ ∃ b < l, x ∈ level b := by
  rw [level_limit l hl,ZFSet.mem_iUnion]
  exact ⟨fun ⟨b,hb⟩ => ⟨b.val,b.property,hb⟩,fun ⟨b,hb,hx⟩ => ⟨⟨b,hb⟩,hx⟩⟩

theorem level_unique (F : Ordinal.{u} → ZFSet.{u}) (h0 : F 0 = ∅)
    (hs : ∀ a, F (a+1) = Def (F a))
    (hl : ∀ l, Order.IsSuccLimit l →
      F l = ZFSet.iUnion (fun b : Set.Iio l => F b.val)) : F = level := by
  funext a
  induction a using Ordinal.limitRecOn with
  | zero => exact h0.trans level_zero.symm
  | add_one a ih => rw [hs,level_successor,ih]
  | limit l hlim ih =>
    rw [hl l hlim,level_limit l hlim]
    congr 1
    funext b
    exact ih b.val b.property

def IsConstructible (x : ZFSet.{u}) : Prop := ∃ a, x ∈ level a

theorem level_transitive (a : Ordinal.{u}) : (level a).IsTransitive := by
  induction a using Ordinal.limitRecOn with
  | zero => rw [level_zero]; exact ZFSet.isTransitive_empty
  | add_one a ih => rw [level_successor]; exact (transitive_Def _ ih).2
  | limit l hl ih =>
    rw [level_limit l hl]
    exact ZFSet.IsTransitive.iUnion (fun b : Set.Iio l => ih b.val b.property)
theorem level_monotone {a b : Ordinal.{u}} (h : a ≤ b) : level a ⊆ level b := by
  induction b using Ordinal.limitRecOn generalizing a with
  | zero =>
    have ha : a = 0 := le_antisymm h bot_le
    subst a
    exact fun _ hx => hx
  | add_one b ih =>
    rcases lt_or_eq_of_le h with hab | rfl
    · have hab' : a ≤ b := by simpa only [← Order.succ_eq_add_one,Order.lt_succ_iff] using hab
      rw [level_successor]
      exact fun _ hx => (transitive_Def _ (level_transitive b)).1 (ih hab' hx)
    · exact fun _ hx => hx
  | limit l hl ih =>
    rcases lt_or_eq_of_le h with hal | rfl
    · exact fun x hx => (level_limit_members l hl x).mpr ⟨a,hal,hx⟩
    · exact fun _ hx => hx
theorem level_mem_successor (a : Ordinal.{u}) : level a ∈ level (a+1) := by
  rw [level_successor]
  exact (full_and_empty_mem _).1
theorem level_subset_rank (a : Ordinal.{u}) : level a ⊆ ZFSet.vonNeumann a := by
  induction a using Ordinal.limitRecOn with
  | zero => rw [level_zero]; exact fun x hx => (ZFSet.notMem_empty x hx).elim
  | add_one a ih =>
    intro x hx
    rw [level_successor] at hx
    rw [ZFSet.vonNeumann_add_one,ZFSet.mem_powerset]
    exact fun _ hy => ih ((ZFSet.mem_powerset.mp (Def_subset_powerset _ hx)) hy)
  | limit l hl ih =>
    intro x hx
    obtain ⟨b,hb,hx⟩ := (level_limit_members l hl x).mp hx
    exact ZFSet.vonNeumann_strictMono.monotone hb.le (ih b hb hx)

private theorem ordinal_set_from_smaller (a : Ordinal.{u})
    (h : ∀ b < a, b.toZFSet ∈ level a) :
    ZFSet.sep ZFSet.IsOrdinal (level a) = a.toZFSet := by
  ext x
  rw [ZFSet.mem_sep,Ordinal.mem_toZFSet_iff]
  constructor
  · rintro ⟨hx,ho⟩
    exact ⟨x.rank,ZFSet.mem_vonNeumann.mp (level_subset_rank a hx),ho.toZFSet_rank_eq⟩
  · rintro ⟨b,hb,rfl⟩
    exact ⟨h b hb,ZFSet.isOrdinal_toZFSet b⟩

private theorem smaller_ordinal_mem (a b : Ordinal.{u}) (hb : b < a) :
    b.toZFSet ∈ level a := by
  induction a using Ordinal.limitRecOn generalizing b with
  | zero => exact (not_lt_bot hb).elim
  | add_one a ih =>
    have hba : b ≤ a := by simpa only [← Order.succ_eq_add_one,Order.lt_succ_iff] using hb
    rcases lt_or_eq_of_le hba with hlt | heq
    · exact level_monotone (le_add_right (le_refl _)) (ih b hlt)
    · subst b
      rw [level_successor,← ordinal_set_from_smaller a ih,← ordinalCode_correct _ (level_transitive a)]
      exact ZFSet.mem_range_self (ordinalCode (level a))
  | limit l hl ih =>
    exact (level_limit_members l hl b.toZFSet).mpr
      ⟨b+1,hl.succ_lt hb,ih (b+1) (hl.succ_lt hb) b (lt_add_one b)⟩

/-- This is the exact bounded ordinal test code specified at a successor stage. -/
theorem level_ordinal_code (a : Ordinal.{u}) :
    definedSubset (level a) (ordinalCode (level a)) = a.toZFSet := by
  exact (ordinalCode_correct _ (level_transitive a)).trans
    (ordinal_set_from_smaller a (fun b hb => smaller_ordinal_mem a b hb))
theorem level_ordinal_part (a b : Ordinal.{u}) : b.toZFSet ∈ level a ↔ b < a := by
  constructor
  · intro h
    exact (Lemmatheca.SetTheory.CumulativeHierarchy.ordinal_part a b).mp (level_subset_rank a h)
  · exact smaller_ordinal_mem a b
theorem level_ordinals (a : Ordinal.{u}) :
    ZFSet.sep ZFSet.IsOrdinal (level a) = a.toZFSet := by
  exact ordinal_set_from_smaller a (fun b hb => smaller_ordinal_mem a b hb)

theorem constructible_transitive {x y : ZFSet.{u}}
    (hx : x ∈ y) (hy : IsConstructible y) : IsConstructible x := by
  obtain ⟨a,ha⟩ := hy
  exact ⟨a,level_transitive a y ha hx⟩
theorem constructible_ordinals (a : Ordinal.{u}) : IsConstructible a.toZFSet := by
  exact ⟨a+1,(level_ordinal_part _ _).mpr (lt_add_one _)⟩
theorem constructible_not_set (X : ZFSet.{u}) :
    ∃ x : ZFSet.{u}, IsConstructible x ∧ x ∉ X := by
  refine ⟨X.rank.toZFSet,constructible_ordinals _,?_⟩
  intro h
  have hl := ZFSet.rank_lt_of_mem h
  exact (lt_irrefl X.rank) (by simpa only [Ordinal.rank_toZFSet] using hl)

theorem finite_levels (n : ℕ) : level (n : Ordinal.{u}) = ZFSet.vonNeumann n := by
  induction n with
  | zero => rw [Nat.cast_zero,level_zero,ZFSet.vonNeumann_zero]
  | succ n ih =>
    let : Finite (ZFSet.vonNeumann (n : Ordinal.{u})) :=
      Lemmatheca.SetTheory.CumulativeHierarchy.finite_stages.2.2.2.2.1 n
    rw [Nat.cast_add_one,level_successor,ih,finite_Def,ZFSet.vonNeumann_add_one]
theorem omega_level : level (ω : Ordinal.{u}) = ZFSet.vonNeumann ω := by
  rw [level_limit _ Ordinal.isSuccLimit_omega0,
    ZFSet.vonNeumann_of_isSuccPrelimit Ordinal.isSuccLimit_omega0.isSuccPrelimit]
  congr 1
  funext b
  obtain ⟨n,hn⟩ := Ordinal.lt_omega0.mp b.property
  rw [hn,finite_levels]
theorem first_levels : level (0 : Ordinal.{u}) = ∅ ∧ level (1 : Ordinal.{u}) = {∅} ∧
    level (2 : Ordinal.{u}) = {∅,{∅}}  := by
  have h1 : level (1 : Ordinal.{u}) = ZFSet.vonNeumann 1 := by simpa using finite_levels (1 : ℕ)
  have h2 : level (2 : Ordinal.{u}) = ZFSet.vonNeumann 2 := by simpa using finite_levels (2 : ℕ)
  exact ⟨level_zero,h1.trans Lemmatheca.SetTheory.CumulativeHierarchy.finite_stages.2.1,
    h2.trans Lemmatheca.SetTheory.CumulativeHierarchy.finite_stages.2.2.1⟩
theorem omega_level_hereditarily_finite (x : ZFSet.{u}) :
    x ∈ level (ω : Ordinal.{u}) ↔
      Lemmatheca.SetTheory.CumulativeHierarchy.HereditarilyFinite x := by
  rw [omega_level]
  exact (Lemmatheca.SetTheory.CumulativeHierarchy.hereditarilyFinite_iff x).2.symm

/-- This supplies the actual continuous transitive hierarchy to the general
finite-family reflection argument, without assuming ZF in its union. -/
def constructibleHierarchy : Lemmatheca.SetTheory.RankReflection.Hierarchy.{u} where
  level := level
  transitive := level_transitive
  monotone := level_monotone
  continuous := level_limit_members

theorem constructibleHierarchy_nonempty :
    Lemmatheca.SetTheory.RankReflection.NonemptyUnion constructibleHierarchy.{u} := by
  refine ⟨1,∅,?_⟩
  change (∅ : ZFSet.{u}) ∈ level 1
  rw [first_levels.2.1]
  exact ZFSet.mem_singleton.mpr rfl

end
end Lemmatheca.SetTheory.ConstructibleHierarchy
