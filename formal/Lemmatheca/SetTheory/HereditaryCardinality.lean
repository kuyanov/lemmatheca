import Lemmatheca.SetTheory.CumulativeHierarchy
import Mathlib.SetTheory.Cardinal.Regular

/-! Hereditary cardinality and the sets Hκ in the universe-relative ZFSet model.
The singleton convention counts the starting set itself. -/
set_option autoImplicit false
universe u v
namespace Lemmatheca.SetTheory.HereditaryCardinality
open scoped ZFSet Ordinal Cardinal
open Lemmatheca.SetTheory.FoundationAndRank

/-- Cardinality of the starting set together with all membership descendants. -/
def hereditaryCard (x : ZFSet.{u}) : Cardinal.{u} := (transitiveClosure {x}).card

/-- A hereditary cardinality bound; regularity is not part of this definition. -/
def HereditarilySmall (κ : Cardinal.{u}) (x : ZFSet.{u}) : Prop := hereditaryCard x < κ

/-- Separation within Vκ gives the hereditary level; its exact specification is below. -/
noncomputable def hereditaryLevel (κ : Cardinal.{u}) : ZFSet.{u} :=
  ZFSet.sep (HereditarilySmall κ) (ZFSet.vonNeumann κ.ord)

/-- Hereditary countability includes finite sets of membership descendants. -/
def HereditarilyCountable (x : ZFSet.{u}) : Prop := Countable (transitiveClosure {x})


private theorem finite_iff_card_lt (x : ZFSet.{u}) : Finite x ↔ x.card < ℵ₀ := by
  rw [← Cardinal.mk_lt_aleph0_iff, ZFSet.cardinalMk_coe_sort]
  simpa only [Cardinal.lift_aleph0] using (Cardinal.lift_lt.{u, u + 1} :
    Cardinal.lift.{u + 1} x.card < Cardinal.lift.{u + 1} ℵ₀ ↔ x.card < ℵ₀)

private theorem countable_iff_card_le (x : ZFSet.{u}) : Countable x ↔ x.card ≤ ℵ₀ := by
  rw [← Cardinal.mk_le_aleph0_iff, ZFSet.cardinalMk_coe_sort]
  simpa only [Cardinal.lift_aleph0] using (Cardinal.lift_le.{u + 1, u} :
    Cardinal.lift.{u + 1} x.card ≤ Cardinal.lift.{u + 1} ℵ₀ ↔ x.card ≤ ℵ₀)

private theorem small_from_container (κ : Cardinal.{u}) (x T : ZFSet.{u})
    (hT : T.IsTransitive) (hx : x ∈ T) (hsize : T.card < κ) : HereditarilySmall κ x := by
  exact (ZFSet.card_mono ((transitiveClosure_spec {x}).2.2 T hT
    (by intro z hz; exact ZFSet.mem_singleton.mp hz ▸ hx))).trans_lt hsize

private theorem insert_transitive (x T : ZFSet.{u}) (hT : T.IsTransitive) (hx : x ⊆ T) :
    (insert x T).IsTransitive := by
  intro y hy z hz
  rcases ZFSet.mem_insert_iff.mp hy with rfl | hy
  · exact ZFSet.mem_insert_iff.mpr (Or.inr (hx hz))
  · exact ZFSet.mem_insert_iff.mpr (Or.inr (hT y hy hz))

private theorem insert_card_lt (κ : Cardinal.{u}) (hκ : ℵ₀ ≤ κ) (x T : ZFSet.{u})
    (hT : T.card < κ) : (insert x T).card < κ :=
  (ZFSet.card_insert_le).trans_lt (Cardinal.add_one_lt_of_lt hκ hT)

theorem card_le_hereditaryCard (x : ZFSet.{u}) : x.card ≤ hereditaryCard x := by
  exact ZFSet.card_mono ((transitiveClosure_spec {x}).1 x
    ((transitiveClosure_spec {x}).2.1 (by simp)))

theorem small_transitive_ranks (θ : Cardinal.{u}) (hθ : θ.IsRegular)
    (T : ZFSet.{u}) (hT : T.IsTransitive) (hsize : T.card < θ) :
    ∀ y ∈ T, y.rank < θ.ord := by
  intro y
  induction y using ZFSet.inductionOn with
  | _ y ih =>
    intro hy
    have hsub : y ⊆ T := hT y hy
    have hycard : y.card < θ := (ZFSet.card_mono hsub).trans_lt hsize
    rw [rank_equation]
    simp only [Order.succ_eq_add_one]
    apply Ordinal.lift_iSup_add_one_lt_of_lt_cof
    · rw [Cardinal.lift_id'.{u, u + 1}, ← Ordinal.lift_cof, hθ.cof_ord, ZFSet.cardinalMk_coe_sort]
      exact Cardinal.lift_lt.{u, u + 1}.mpr hycard
    · intro z
      exact ih z.val z.property (hsub z.property)

/-- The rank bound holds for singular as well as regular infinite cardinals. -/
theorem hereditary_rank_lt (κ : Cardinal.{u}) (hκ : ℵ₀ ≤ κ)
    (x : ZFSet.{u}) (hx : HereditarilySmall κ x) : x.rank < κ.ord := by
  let T := transitiveClosure {x}
  have hT := transitiveClosure_spec {x}
  have hxT : x ∈ T := hT.2.1 (by simp)
  have hsize : T.card < κ := hx
  by_cases hfin : T.card < ℵ₀
  · have hf : Lemmatheca.SetTheory.CumulativeHierarchy.HereditarilyFinite x :=
      (finite_iff_card_lt T).mpr hfin
    exact ((Lemmatheca.SetTheory.CumulativeHierarchy.hereditarilyFinite_iff x).1.mp hf).trans_le
      (by simpa using Cardinal.ord_mono hκ)
  · have hinf : ℵ₀ ≤ T.card := le_of_not_gt hfin
    exact (small_transitive_ranks (Order.succ T.card) (Cardinal.isRegular_succ hinf)
      T hT.1 (Order.lt_succ T.card) x hxT).trans_le
      (Cardinal.ord_mono (Order.succ_le_of_lt hsize))

/-- Sethood, the exact membership condition, and the hierarchy bound. -/
theorem hereditaryLevel_spec (κ : Cardinal.{u}) (hκ : ℵ₀ ≤ κ) :
    (∀ x : ZFSet.{u}, x ∈ hereditaryLevel κ ↔ HereditarilySmall κ x) ∧
    hereditaryLevel κ ⊆ ZFSet.vonNeumann κ.ord := by
  have hm : ∀ x : ZFSet.{u}, x ∈ hereditaryLevel κ ↔ HereditarilySmall κ x := by
    intro x
    simp only [hereditaryLevel, ZFSet.mem_sep]
    exact ⟨And.right, fun hx => ⟨ZFSet.mem_vonNeumann.mpr (hereditary_rank_lt κ hκ x hx), hx⟩⟩
  exact ⟨hm, fun x hx => (ZFSet.mem_sep.mp hx).1⟩

theorem hereditaryLevel_transitive (κ : Cardinal.{u}) (hκ : ℵ₀ ≤ κ) :
    (hereditaryLevel κ).IsTransitive := by
  intro x hx y hy
  apply ((hereditaryLevel_spec κ hκ).1 y).mpr
  have hxsmall := ((hereditaryLevel_spec κ hκ).1 x).mp hx
  exact small_from_container κ y (transitiveClosure {x}) (transitiveClosure_spec {x}).1
    ((transitiveClosure_spec {x}).1 x ((transitiveClosure_spec {x}).2.1 (by simp)) hy) hxsmall

theorem hereditaryLevel_mono (κ ℓ : Cardinal.{u}) (hκ : ℵ₀ ≤ κ) (h : κ ≤ ℓ) :
    hereditaryLevel κ ⊆ hereditaryLevel ℓ := by
  intro x hx
  exact ((hereditaryLevel_spec ℓ (hκ.trans h)).1 x).mpr
    ((((hereditaryLevel_spec κ hκ).1 x).mp hx).trans_le h)

theorem hereditaryLevel_exhaustion (x : ZFSet.{u}) :
    ∃ κ : Cardinal.{u}, ℵ₀ ≤ κ ∧ x ∈ hereditaryLevel κ := by
  let κ := Order.succ (max ℵ₀ (hereditaryCard x))
  have hk : ℵ₀ ≤ κ := (le_max_left _ _).trans (Order.le_succ _)
  refine ⟨κ, hk, ((hereditaryLevel_spec κ hk).1 x).mpr ?_⟩
  exact (le_max_right _ _).trans_lt (Order.lt_succ _)

theorem ordinal_transitiveClosure (α : Ordinal.{u}) :
    transitiveClosure {α.toZFSet} = (α + 1).toZFSet := by
  apply le_antisymm
  · apply (transitiveClosure_spec {α.toZFSet}).2.2 _ (ZFSet.isOrdinal_toZFSet _).isTransitive
    intro y hy
    exact ZFSet.mem_singleton.mp hy ▸ Ordinal.toZFSet_mem_toZFSet_iff.mpr (lt_add_one α)
  · rw [Ordinal.toZFSet_add_one]
    intro y hy
    rcases ZFSet.mem_insert_iff.mp hy with rfl | hy
    · exact (transitiveClosure_spec {α.toZFSet}).2.1 (by simp)
    · exact (transitiveClosure_spec {α.toZFSet}).1 α.toZFSet
        ((transitiveClosure_spec {α.toZFSet}).2.1 (by simp)) hy

theorem ordinal_mem_hereditaryLevel (κ : Cardinal.{u}) (hκ : ℵ₀ ≤ κ)
    (α : Ordinal.{u}) : α.toZFSet ∈ hereditaryLevel κ ↔ α < κ.ord := by
  rw [(hereditaryLevel_spec κ hκ).1 α.toZFSet]
  change (transitiveClosure {α.toZFSet}).card < κ ↔ α < κ.ord
  rw [ordinal_transitiveClosure, Ordinal.card_toZFSet, ← Cardinal.lt_ord]
  exact ⟨fun h => (lt_add_one α).trans h, (Cardinal.isSuccLimit_ord hκ).add_one_lt⟩

theorem hereditaryLevel_basic_closure (κ : Cardinal.{u}) (hκ : ℵ₀ ≤ κ)
    (x y : ZFSet.{u}) (hx : x ∈ hereditaryLevel κ) (hy : y ∈ hereditaryLevel κ) :
    (∀ z : ZFSet.{u}, z ⊆ x → z ∈ hereditaryLevel κ) ∧
    {x,y} ∈ hereditaryLevel κ ∧ ZFSet.sUnion x ∈ hereditaryLevel κ := by
  have hsx : (transitiveClosure {x}).card < κ :=
    ((hereditaryLevel_spec κ hκ).1 x).mp hx
  have hsy : (transitiveClosure {y}).card < κ :=
    ((hereditaryLevel_spec κ hκ).1 y).mp hy
  have hxT : x ∈ transitiveClosure {x} := (transitiveClosure_spec {x}).2.1 (by simp)
  have hyT : y ∈ transitiveClosure {y} := (transitiveClosure_spec {y}).2.1 (by simp)
  have hxsub := (transitiveClosure_spec {x}).1 x hxT
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    apply ((hereditaryLevel_spec κ hκ).1 z).mpr
    exact small_from_container κ z (insert z (transitiveClosure {x}))
      (insert_transitive _ _ (transitiveClosure_spec {x}).1 (hz.trans hxsub))
      (by simp) (insert_card_lt κ hκ z _ hsx)
  · let T := transitiveClosure {x} ∪ transitiveClosure {y}
    have hT : T.IsTransitive := (transitiveClosure_spec {x}).1.union (transitiveClosure_spec {y}).1
    have hsize : T.card < κ := (ZFSet.card_union_le).trans_lt
      (Cardinal.add_lt_of_lt hκ hsx hsy)
    have hpair : ({x,y} : ZFSet.{u}) ⊆ T := by
      intro z hz
      rcases ZFSet.mem_pair.mp hz with rfl | rfl
      · exact ZFSet.mem_union.mpr (Or.inl hxT)
      · exact ZFSet.mem_union.mpr (Or.inr hyT)
    apply ((hereditaryLevel_spec κ hκ).1 {x,y}).mpr
    exact small_from_container κ {x,y} (insert {x,y} T)
      (insert_transitive _ _ hT hpair) (by simp) (insert_card_lt κ hκ {x,y} T hsize)
  · have hu : ZFSet.sUnion x ⊆ transitiveClosure {x} := by
      intro z hz
      obtain ⟨w, hw, hz⟩ := ZFSet.mem_sUnion.mp hz
      exact (transitiveClosure_spec {x}).1 w (hxsub hw) hz
    apply ((hereditaryLevel_spec κ hκ).1 (ZFSet.sUnion x)).mpr
    exact small_from_container κ (ZFSet.sUnion x) (insert (ZFSet.sUnion x) (transitiveClosure {x}))
      (insert_transitive _ _ (transitiveClosure_spec {x}).1 hu) (by simp)
      (insert_card_lt κ hκ (ZFSet.sUnion x) _ hsx)

theorem hereditaryLevel_small_collection (κ : Cardinal.{u}) (hκ : κ.IsRegular)
    (A : ZFSet.{u}) (hA : A ⊆ hereditaryLevel κ) (hsize : A.card < κ) :
    A ∈ hereditaryLevel κ := by
  let f : Shrink A → ZFSet.{u} := fun i => transitiveClosure {(equivShrink A).symm i |>.val}
  let T := ZFSet.iUnion f
  have hT : T.IsTransitive := ZFSet.IsTransitive.iUnion (fun i => (transitiveClosure_spec _).1)
  have hsum : (Cardinal.sum fun i => (f i).card) < κ :=
    Cardinal.sum_lt_of_isRegular hκ hsize (fun i =>
      ((hereditaryLevel_spec κ hκ.aleph0_le).1 _).mp (hA ((equivShrink A).symm i).property))
  have hbound : T.card ≤ Cardinal.sum (fun i => (f i).card) := by
    simpa only [Cardinal.lift_id] using ZFSet.lift_card_iUnion_le_sum_card (f := f)
  have hcard : T.card < κ := hbound.trans_lt hsum
  have hAT : A ⊆ T := by
    intro x hx
    apply ZFSet.mem_iUnion.mpr
    refine ⟨(equivShrink A) ⟨x,hx⟩, ?_⟩
    simp only [Equiv.symm_apply_apply]
    exact (transitiveClosure_spec {x}).2.1 (by simp)
  apply ((hereditaryLevel_spec κ hκ.aleph0_le).1 A).mpr
  exact small_from_container κ A (insert A T) (insert_transitive A T hT hAT) (by simp)
    (insert_card_lt κ hκ.aleph0_le A T hcard)

theorem hereditaryLevel_small_family (κ : Cardinal.{u}) (hκ : κ.IsRegular)
    {ι : Type u} (x : ι → ZFSet.{u}) (hsize : Cardinal.mk ι < κ)
    (hx : ∀ i, x i ∈ hereditaryLevel κ) :
    ZFSet.range x ∈ hereditaryLevel κ ∧ ZFSet.iUnion x ∈ hereditaryLevel κ := by
  have hA : ZFSet.range x ⊆ hereditaryLevel κ := by
    intro y hy
    obtain ⟨i, rfl⟩ := ZFSet.mem_range.mp hy
    exact hx i
  have hbound : (ZFSet.range x).card ≤ Cardinal.mk ι := by
    simpa only [Cardinal.lift_id] using ZFSet.lift_card_range_le (f := x)
  have hcard : (ZFSet.range x).card < κ := hbound.trans_lt hsize
  have hm := hereditaryLevel_small_collection κ hκ (ZFSet.range x) hA hcard
  exact ⟨hm, (hereditaryLevel_basic_closure κ hκ.aleph0_le _ _ hm hm).2.2⟩

theorem hereditaryLevel_aleph0 :
    hereditaryLevel (ℵ₀ : Cardinal.{u}) = ZFSet.vonNeumann (ω : Ordinal.{u}) := by
  apply ZFSet.ext
  intro x
  rw [(hereditaryLevel_spec _ le_rfl).1 x, ← (Lemmatheca.SetTheory.CumulativeHierarchy.hereditarilyFinite_iff x).2]
  exact (finite_iff_card_lt (transitiveClosure {x})).symm

theorem hereditarilyCountable_iff_level (x : ZFSet.{u}) :
    HereditarilyCountable x ↔ x ∈ hereditaryLevel (ℵ₁ : Cardinal.{u}) := by
  rw [(hereditaryLevel_spec _ Cardinal.isRegular_aleph_one.aleph0_le).1 x]
  change Countable (transitiveClosure {x}) ↔ (transitiveClosure {x}).card < ℵ₁
  rw [Cardinal.lt_aleph_one_iff]
  exact countable_iff_card_le _

theorem natural_subset_hereditarilyCountable (A : ZFSet.{u})
    (hA : A ⊆ (ω : Ordinal.{u}).toZFSet) : HereditarilyCountable A := by
  apply (hereditarilyCountable_iff_level A).mpr
  have hw : (ω : Ordinal.{u}).toZFSet ∈ hereditaryLevel (ℵ₁ : Cardinal.{u}) :=
    (ordinal_mem_hereditaryLevel _ Cardinal.isRegular_aleph_one.aleph0_le _).mpr (by simp)
  exact (hereditaryLevel_basic_closure _ Cardinal.isRegular_aleph_one.aleph0_le _ _ hw hw).1 A hA

theorem countable_collection_hereditarilyCountable (A : ZFSet.{u})
    (hA : ∀ x ∈ A, HereditarilyCountable x) (hsize : Countable A) :
    HereditarilyCountable A := by
  apply (hereditarilyCountable_iff_level A).mpr
  apply hereditaryLevel_small_collection _ Cardinal.isRegular_aleph_one A
  · intro x hx
    exact (hereditarilyCountable_iff_level x).mp (hA x hx)
  · exact Cardinal.lt_aleph_one_iff.mpr ((countable_iff_card_le A).mp hsize)

/-- The power-set witness simultaneously separates hereditary size from rank
and shows failure of power-set closure at the first uncountable bound. -/
theorem hereditaryCountable_strict_hierarchy :
    hereditaryLevel (ℵ₁ : Cardinal.{u}) ⊂ ZFSet.vonNeumann (ω₁ : Ordinal.{u}) ∧
    (ω : Ordinal.{u}).toZFSet ∈ hereditaryLevel (ℵ₁ : Cardinal.{u}) ∧
    ZFSet.powerset (ω : Ordinal.{u}).toZFSet ∉ hereditaryLevel (ℵ₁ : Cardinal.{u}) ∧
    (ZFSet.powerset (ω : Ordinal.{u}).toZFSet).rank = (ω : Ordinal.{u}) + 1 ∧
    ZFSet.powerset (ω : Ordinal.{u}).toZFSet ∈ ZFSet.vonNeumann (ω₁ : Ordinal.{u}) := by
  have hw : (ω : Ordinal.{u}).toZFSet ∈ hereditaryLevel (ℵ₁ : Cardinal.{u}) :=
    (ordinal_mem_hereditaryLevel _ Cardinal.isRegular_aleph_one.aleph0_le _).mpr (by simp)
  have hpnot : ZFSet.powerset (ω : Ordinal.{u}).toZFSet ∉ hereditaryLevel (ℵ₁ : Cardinal.{u}) := by
    intro hp
    have hs := ((hereditaryLevel_spec _ Cardinal.isRegular_aleph_one.aleph0_le).1 _).mp hp
    have hc := (card_le_hereditaryCard _).trans_lt hs
    rw [ZFSet.card_powerset, Ordinal.card_toZFSet, Ordinal.card_omega0] at hc
    exact (Cardinal.aleph_one_le_iff.mpr (Cardinal.cantor ℵ₀)).not_gt hc
  have hr : (ZFSet.powerset (ω : Ordinal.{u}).toZFSet).rank = (ω : Ordinal.{u}) + 1 := by
    simp [Order.succ_eq_add_one]
  have hpV : ZFSet.powerset (ω : Ordinal.{u}).toZFSet ∈ ZFSet.vonNeumann (ω₁ : Ordinal.{u}) := by
    rw [ZFSet.mem_vonNeumann, hr]
    exact (Cardinal.isSuccLimit_omega _).add_one_lt (by simp)
  refine ⟨?_, hw, hpnot, hr, hpV⟩
  rw [ssubset_iff_subset_not_subset]
  refine ⟨?_, ?_⟩
  · simpa only [Cardinal.ord_aleph] using
      (hereditaryLevel_spec (ℵ₁ : Cardinal.{u}) Cardinal.isRegular_aleph_one.aleph0_le).2
  · intro h
    exact hpnot (h hpV)

/-- Taking one more singleton adds just that singleton to its descendant closure. -/
theorem transitiveClosure_singleton_singleton (x : ZFSet.{u}) :
    transitiveClosure {{x}} = insert {x} (transitiveClosure {x}) := by
  have hx : x ∈ transitiveClosure {x} := (transitiveClosure_spec {x}).2.1 (by simp)
  have hsingle : {x} ∈ transitiveClosure {{x}} := (transitiveClosure_spec {{x}}).2.1 (by simp)
  have hxouter : x ∈ transitiveClosure {{x}} := (transitiveClosure_spec {{x}}).1 {x} hsingle (by simp)
  apply le_antisymm
  · apply (transitiveClosure_spec {{x}}).2.2 _
      (insert_transitive {x} _ (transitiveClosure_spec {x}).1 (by
        intro y hy; exact ZFSet.mem_singleton.mp hy ▸ hx))
    intro y hy
    exact ZFSet.mem_singleton.mp hy ▸ (by simp)
  · intro y hy
    rcases ZFSet.mem_insert_iff.mp hy with rfl | hy
    · exact hsingle
    · exact (transitiveClosure_spec {x}).2.2 _ (transitiveClosure_spec {{x}}).1
        (by intro z hz; exact ZFSet.mem_singleton.mp hz ▸ hxouter) hy

end Lemmatheca.SetTheory.HereditaryCardinality
