import Lemmatheca.ConstructibleCondensation.Collapse

namespace Lemmatheca.SetTheory.ConstructibleCondensation
open FirstOrder FirstOrder.Language
open Lemmatheca.SetTheory.MembershipModels
open scoped ZFSet Ordinal Cardinal
universe u
noncomputable section
variable {D : ZFSet.{u}}
local instance condensationHullStructure : membershipLanguage.Structure D :=
  actualMembershipStructure D

private theorem hull_with_parameters (k : Ordinal.{u}) (hk : ω ≤ k)
    (hkd : k.toZFSet ⊆ D) (s : Set D)
    (hs : Cardinal.mk s ≤ Cardinal.mk k.toZFSet) :
    ∃ X : ElementarySubmodel D, ContainsOrdinalPoints X k ∧ s ⊆ X ∧
      Cardinal.mk X = Cardinal.mk k.toZFSet := by
  classical
  have hinf : ℵ₀ ≤ Cardinal.mk k.toZFSet := by
    rw [ZFSet.cardinalMk_coe_sort, Ordinal.card_toZFSet, Cardinal.aleph0_le_lift]
    exact Ordinal.aleph0_le_card.mpr hk
  let f : k.toZFSet → D := fun a => ⟨a.val, hkd a.property⟩
  have hfinj : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    exact congrArg (fun z : D => z.val) hab
  have hseed : Cardinal.mk (Set.range f ∪ s : Set D) ≤ Cardinal.mk k.toZFSet := by
    calc
      _ ≤ Cardinal.mk (Set.range f) + Cardinal.mk s := Cardinal.mk_union_le _ _
      _ ≤ Cardinal.mk k.toZFSet + Cardinal.mk k.toZFSet :=
        add_le_add Cardinal.mk_range_le hs
      _ = _ := Cardinal.add_eq_self hinf
  have hlang : membershipLanguage.card ≤ ℵ₀ :=
    Cardinal.mk_le_aleph0_iff.mpr countable_membership_symbols
  obtain ⟨X,hXS,hcard⟩ := membershipLanguage.exists_elementarySubstructure_card_eq
    (Set.range f ∪ s) (Cardinal.mk k.toZFSet) hinf
    (by simpa only [Cardinal.lift_id, Cardinal.lift_id'] using hseed)
    (by
      have h : Cardinal.lift.{u+1} membershipLanguage.card ≤ ℵ₀ := by
        simpa only [Cardinal.lift_aleph0] using Cardinal.lift_le.mpr hlang
      simpa only [Cardinal.lift_id, Cardinal.lift_id'] using h.trans hinf)
    (by simpa only [Cardinal.lift_id, Cardinal.lift_id'] using Cardinal.mk_le_of_injective hfinj)
  refine ⟨X, ?_, ?_, ?_⟩
  · intro z hz
    exact ⟨⟨f ⟨z,hz⟩,hXS (Or.inl (show f ⟨z,hz⟩ ∈ Set.range f from Set.mem_range_self _))⟩,rfl⟩
  · intro a ha
    exact hXS (Or.inr ha)
  · simpa only [Cardinal.lift_id, Cardinal.lift_id'] using hcard

theorem small_hull (k : Ordinal.{u}) (hk : ω ≤ k) (hkd : k.toZFSet ⊆ D) (x : D) :
    ∃ X : ElementarySubmodel D,
      ContainsOrdinalPoints X k ∧ x ∈ X ∧ Cardinal.mk X = Cardinal.mk k.toZFSet := by
  have hinf : ℵ₀ ≤ Cardinal.mk k.toZFSet := by
    rw [ZFSet.cardinalMk_coe_sort, Ordinal.card_toZFSet, Cardinal.aleph0_le_lift]
    exact Ordinal.aleph0_le_card.mpr hk
  obtain ⟨X,hpoints,hparam,hcard⟩ := hull_with_parameters k hk hkd {x}
    (by simpa only [Cardinal.mk_singleton] using Cardinal.one_le_aleph0.trans hinf)
  exact ⟨X,hpoints,hparam (Set.mem_singleton x),hcard⟩

theorem small_hull_with_index (hD : D.IsTransitive) (k : Ordinal.{u}) (hk : ω ≤ k)
    (hkd : k.toZFSet ∈ D) (x : D) :
    ∃ X : ElementarySubmodel D,
      ContainsOrdinalPoints X k ∧ x ∈ X ∧ (⟨k.toZFSet,hkd⟩ : D) ∈ X ∧
        Cardinal.mk X = Cardinal.mk k.toZFSet := by
  have hinf : ℵ₀ ≤ Cardinal.mk k.toZFSet := by
    rw [ZFSet.cardinalMk_coe_sort, Ordinal.card_toZFSet, Cardinal.aleph0_le_lift]
    exact Ordinal.aleph0_le_card.mpr hk
  let y : D := ⟨k.toZFSet,hkd⟩
  have hs : Cardinal.mk ({x,y} : Set D) ≤ Cardinal.mk k.toZFSet := by
    calc
      _ ≤ Cardinal.mk ({y} : Set D) + 1 := Cardinal.mk_insert_le
      _ ≤ Cardinal.mk k.toZFSet + Cardinal.mk k.toZFSet :=
        add_le_add (by simpa only [Cardinal.mk_singleton] using Cardinal.one_le_aleph0.trans hinf)
          (Cardinal.one_le_aleph0.trans hinf)
      _ = _ := Cardinal.add_eq_self hinf
  obtain ⟨X,hpoints,hparam,hcard⟩ :=
    hull_with_parameters k hk (by intro z hz; exact hD.mem_trans hz hkd) {x,y} hs
  exact ⟨X,hpoints,hparam (Set.mem_insert x {y}),
    hparam (Set.mem_insert_of_mem x (Set.mem_singleton y)),hcard⟩

end
end Lemmatheca.SetTheory.ConstructibleCondensation
