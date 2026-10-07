import Lemmatheca.SetTheory.HereditaryCardinality

/-! Concrete hereditary-countability and singular-closure counterexamples. -/
set_option autoImplicit false
universe u
namespace Lemmatheca.Entry.HereditaryCardinality
open scoped ZFSet Ordinal Cardinal
open Lemmatheca.SetTheory.FoundationAndRank
open Lemmatheca.SetTheory.HereditaryCardinality

theorem countability_examples :
    Finite ({(ω : Ordinal.{u}).toZFSet} : ZFSet.{u}) ∧
    Finite ({(ω₁ : Ordinal.{u}).toZFSet} : ZFSet.{u}) ∧
    HereditarilyCountable ({(ω : Ordinal.{u}).toZFSet} : ZFSet.{u}) ∧
    ¬ HereditarilyCountable ({(ω₁ : Ordinal.{u}).toZFSet} : ZFSet.{u}) ∧
    transitiveClosure ({({(ω : Ordinal.{u}).toZFSet} : ZFSet.{u})} : ZFSet.{u}) =
      ({({(ω : Ordinal.{u}).toZFSet} : ZFSet.{u}), (ω : Ordinal.{u}).toZFSet} : ZFSet.{u}) ∪
        (ω : Ordinal.{u}).toZFSet ∧
    ¬ Countable (ZFSet.powerset (ω : Ordinal.{u}).toZFSet) ∧
    ¬ HereditarilyCountable (ZFSet.powerset (ω : Ordinal.{u}).toZFSet) := by
  have hfinite (x : ZFSet.{u}) : Finite ({x} : ZFSet.{u}) := by
    apply Cardinal.mk_lt_aleph0_iff.mp
    simpa only [ZFSet.cardinalMk_coe_sort, ZFSet.card_singleton, Cardinal.lift_one] using
      (Cardinal.one_lt_aleph0 : (1 : Cardinal.{u + 1}) < ℵ₀)
  have hw : (ω : Ordinal.{u}).toZFSet ∈ hereditaryLevel (ℵ₁ : Cardinal.{u}) :=
    (ordinal_mem_hereditaryLevel _ Cardinal.isRegular_aleph_one.aleph0_le _).mpr (by simp)
  have hsingleω : HereditarilyCountable ({(ω : Ordinal.{u}).toZFSet} : ZFSet.{u}) := by
    apply (hereditarilyCountable_iff_level _).mpr
    simpa only [ZFSet.pair_eq_singleton] using
      (hereditaryLevel_basic_closure _ Cardinal.isRegular_aleph_one.aleph0_le _ _ hw hw).2.1
  have hsingleω₁ : ¬ HereditarilyCountable ({(ω₁ : Ordinal.{u}).toZFSet} : ZFSet.{u}) := by
    intro h
    have hm := (hereditarilyCountable_iff_level _).mp h
    have ho := hereditaryLevel_transitive _ Cardinal.isRegular_aleph_one.aleph0_le _ hm
      (show (ω₁ : Ordinal.{u}).toZFSet ∈ ({(ω₁ : Ordinal.{u}).toZFSet} : ZFSet.{u}) by simp)
    have hlt := (ordinal_mem_hereditaryLevel _ Cardinal.isRegular_aleph_one.aleph0_le _).mp ho
    simp at hlt
  have hpnotCountable : ¬ Countable (ZFSet.powerset (ω : Ordinal.{u}).toZFSet) := by
    intro h
    have hc := Cardinal.mk_le_aleph0_iff.mpr h
    rw [ZFSet.cardinalMk_coe_sort, ZFSet.card_powerset, Ordinal.card_toZFSet,
      Ordinal.card_omega0, Cardinal.lift_power, Cardinal.lift_aleph0, Cardinal.lift_ofNat] at hc
    exact (Cardinal.cantor ℵ₀).not_ge hc
  refine ⟨hfinite _, hfinite _, hsingleω, hsingleω₁, ?_, hpnotCountable, ?_⟩
  · rw [transitiveClosure_singleton_singleton, ordinal_transitiveClosure, Ordinal.toZFSet_add_one]
    ext z
    simp only [ZFSet.mem_insert_iff, ZFSet.mem_union, ZFSet.mem_singleton]
    tauto
  · intro h
    exact hereditaryCountable_strict_hierarchy.2.2.1 ((hereditarilyCountable_iff_level _).mp h)

/-- The increasing finite-indexed aleph family at aleph omega. -/
noncomputable def alephFamily : ZFSet.{u} :=
  ZFSet.range (fun n : ℕ => (Cardinal.aleph (n : Ordinal.{u})).ord.toZFSet)

theorem singular_collection_example :
    (alephFamily : ZFSet.{u}).card = ℵ₀ ∧
    ℵ₀ < Cardinal.aleph (ω : Ordinal.{u}) ∧
    (alephFamily : ZFSet.{u}) ⊆ hereditaryLevel (Cardinal.aleph (ω : Ordinal.{u})) ∧
    (Cardinal.aleph (ω : Ordinal.{u})).ord.toZFSet ⊆
      transitiveClosure {(alephFamily : ZFSet.{u})} ∧
    (alephFamily : ZFSet.{u}) ∉ hereditaryLevel (Cardinal.aleph (ω : Ordinal.{u})) ∧
    ZFSet.sUnion (alephFamily : ZFSet.{u}) = (Cardinal.aleph (ω : Ordinal.{u})).ord.toZFSet := by
  let f : ℕ → ZFSet.{u} := fun n => (Cardinal.aleph (n : Ordinal.{u})).ord.toZFSet
  have hinj : Function.Injective f := by
    intro m n h
    have ho := Ordinal.toZFSet_injective h
    have hc := Cardinal.ord_injective ho
    have hn := Cardinal.isNormal_aleph.strictMono.injective hc
    exact_mod_cast hn
  have hcard : (alephFamily : ZFSet.{u}).card = ℵ₀ := by
    have h := Cardinal.mk_range_eq_of_injective hinj
    have he : (Set.range f : Set ZFSet.{u}) = (ZFSet.range f : Set ZFSet.{u}) :=
      (ZFSet.coe_range f).symm
    rw [he] at h
    change Cardinal.lift.{0} (Cardinal.mk (ZFSet.range f)) = Cardinal.lift.{u + 1} (Cardinal.mk ℕ) at h
    rw [Cardinal.lift_uzero, ZFSet.cardinalMk_coe_sort, Cardinal.mk_nat, Cardinal.lift_aleph0] at h
    apply Cardinal.lift_injective
    simpa only [alephFamily, f, Cardinal.lift_aleph0] using h
  have hlt : (ℵ₀ : Cardinal.{u}) < Cardinal.aleph (ω : Ordinal.{u}) := by simp
  have hsub : (alephFamily : ZFSet.{u}) ⊆ hereditaryLevel (Cardinal.aleph (ω : Ordinal.{u})) := by
    intro x hx
    obtain ⟨n, rfl⟩ := ZFSet.mem_range.mp hx
    apply (ordinal_mem_hereditaryLevel _ (Cardinal.aleph0_le_aleph _) _).mpr
    rw [Cardinal.ord_aleph, Cardinal.ord_aleph]
    exact (Ordinal.omega_strictMono (Ordinal.natCast_lt_omega0 n))
  have hsup : (⨆ n : ℕ, (Cardinal.aleph (n : Ordinal.{u})).ord) =
      (Cardinal.aleph (ω : Ordinal.{u})).ord := by
    simp only [Cardinal.ord_aleph]
    exact Ordinal.apply_omega0_of_isNormal Ordinal.isNormal_omega
  have hunion : ZFSet.sUnion (alephFamily : ZFSet.{u}) =
      (Cardinal.aleph (ω : Ordinal.{u})).ord.toZFSet := by
    ext z
    rw [ZFSet.mem_sUnion, Ordinal.mem_toZFSet_iff]
    constructor
    · rintro ⟨x, hx, hz⟩
      obtain ⟨n, rfl⟩ := ZFSet.mem_range.mp hx
      obtain ⟨α, hα, rfl⟩ := Ordinal.mem_toZFSet_iff.mp hz
      exact ⟨α, hα.trans_le (hsup ▸ Ordinal.le_iSup
        (fun n : ℕ => (Cardinal.aleph (n : Ordinal.{u})).ord) n), rfl⟩
    · rintro ⟨α, hα, rfl⟩
      rw [← hsup, Ordinal.lt_iSup_iff] at hα
      obtain ⟨n, hn⟩ := hα
      exact ⟨_, ZFSet.mem_range_self (f := f) n, Ordinal.toZFSet_mem_toZFSet_iff.mpr hn⟩
  have hclosure : (Cardinal.aleph (ω : Ordinal.{u})).ord.toZFSet ⊆
      transitiveClosure {(alephFamily : ZFSet.{u})} := by
    rw [← hunion]
    intro z hz
    obtain ⟨x, hx, hz⟩ := ZFSet.mem_sUnion.mp hz
    have hA := (transitiveClosure_spec {(alephFamily : ZFSet.{u})})
    exact hA.1 x (hA.1 _ (hA.2.1 (by simp)) hx) hz
  refine ⟨hcard, hlt, hsub, hclosure, ?_, hunion⟩
  intro hA
  have hsmall := ((hereditaryLevel_spec _ (Cardinal.aleph0_le_aleph _)).1 _).mp hA
  have hb := ZFSet.card_mono hclosure
  rw [Ordinal.card_toZFSet, Cardinal.card_ord] at hb
  exact hb.not_gt hsmall

end Lemmatheca.Entry.HereditaryCardinality
