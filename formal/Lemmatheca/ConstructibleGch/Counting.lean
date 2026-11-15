import Lemmatheca.ConstructibleHierarchy.Levels
import Lemmatheca.ConstructibleInnerModel.WellOrders
import Mathlib.SetTheory.ZFC.Cardinal
import Mathlib.SetTheory.Cardinal.Regular

namespace Lemmatheca.SetTheory.ConstructibleGch
open FirstOrder FirstOrder.Language
open Lemmatheca.SetTheory.ConstructibleHierarchy
open scoped Cardinal Ordinal ZFSet
universe u
noncomputable section

/-- The bound used for empty, finite and infinite parameter domains alike. -/
def codeBound (M : ZFSet.{u}) : Cardinal.{u} := max Cardinal.aleph0 M.card

/-- The actual code output, regarded as an element of its definability collection. -/
def codeOutput (M : ZFSet.{u}) : DefinitionCode M → Def M :=
  fun c => ⟨definedSubset M c, ZFSet.mem_range_self c⟩

theorem codeOutput_surjective (M : ZFSet.{u}) : Function.Surjective (codeOutput M) := by
  intro X
  obtain ⟨c,hc⟩ := ZFSet.mem_range.mp X.property
  exact ⟨c,Subtype.ext hc⟩

theorem codes_card_le (M : ZFSet.{u}) :
    Cardinal.mk (DefinitionCode M) ≤ Cardinal.lift.{u+1,u} (codeBound M) := by
  classical
  let e : DefinitionCode M → ℕ × List M := fun c =>
    (ConstructibleInnerModel.formulaNumber (ConstructibleInnerModel.codeShape M c),
      List.ofFn c.2.2)
  have hi : Function.Injective e := by
    rintro ⟨n,φ,a⟩ ⟨m,ψ,b⟩ h
    have hs := ConstructibleInnerModel.formulaNumber_injective (congrArg Prod.fst h)
    change (⟨n,φ⟩ : ConstructibleInnerModel.FormulaShape) = ⟨m,ψ⟩ at hs
    cases hs
    have hab : a = b := List.ofFn_injective (congrArg Prod.snd h)
    subst b
    rfl
  have hinf : Cardinal.aleph0 ≤ Cardinal.lift.{u+1,u} (codeBound M) :=
    Cardinal.aleph0_le_lift.mpr (le_max_left _ _)
  have hl : Cardinal.mk (List M) ≤ Cardinal.lift.{u+1,u} (codeBound M) := by
    calc
      Cardinal.mk (List M) ≤ max Cardinal.aleph0 (Cardinal.mk M) :=
        Cardinal.mk_list_le_max M
      _ = Cardinal.lift.{u+1,u} (codeBound M) := by
        simp only [codeBound, Cardinal.lift_max, Cardinal.lift_aleph0,
          ← ZFSet.cardinalMk_coe_sort]
  calc
    Cardinal.mk (DefinitionCode M) ≤ Cardinal.mk (ℕ × List M) :=
      Cardinal.mk_le_of_injective hi
    _ = Cardinal.aleph0 * Cardinal.mk (List M) := by
      simp only [Cardinal.mk_prod, Cardinal.mk_nat, Cardinal.lift_aleph0,
        Cardinal.lift_uzero]
    _ ≤ Cardinal.lift.{u+1,u} (codeBound M) * Cardinal.lift.{u+1,u} (codeBound M) :=
      mul_le_mul' hinf hl
    _ = Cardinal.lift.{u+1,u} (codeBound M) := Cardinal.mul_eq_self hinf

theorem def_card_le (M : ZFSet.{u}) : (Def M).card ≤ codeBound M := by
  apply Cardinal.lift_le.{u+1,u}.mp
  rw [← ZFSet.cardinalMk_coe_sort]
  exact (Cardinal.mk_le_of_surjective (codeOutput_surjective M)).trans (codes_card_le M)

theorem def_card_eq (M : ZFSet.{u}) (hM : Cardinal.aleph0 ≤ M.card) :
    (Def M).card = M.card := by
  apply le_antisymm
  · simpa only [codeBound, max_eq_right hM] using def_card_le M
  · apply Cardinal.lift_le.{u+1,u}.mp
    rw [← ZFSet.cardinalMk_coe_sort, ← ZFSet.cardinalMk_coe_sort]
    exact Cardinal.mk_le_of_injective (singletonIntoDef_spec M).2

theorem level_card_le (a : Ordinal.{u}) :
    (level a).card ≤ max Cardinal.aleph0 a.card := by
  induction a using Ordinal.limitRecOn with
  | zero =>
    rw [level_zero, ZFSet.card_empty]
    exact zero_le
  | add_one a ih =>
    rw [level_successor]
    calc
      (Def (level a)).card ≤ codeBound (level a) := def_card_le _
      _ ≤ max Cardinal.aleph0 a.card := max_le (le_max_left _ _) ih
      _ ≤ max Cardinal.aleph0 (a+1).card :=
        max_le_max le_rfl (Ordinal.card_le_card (le_add_right (le_refl a)))
  | limit l hl ih =>
    let μ := max Cardinal.aleph0 l.card
    have hinf : Cardinal.aleph0 ≤ Cardinal.lift.{u+1,u} μ :=
      Cardinal.aleph0_le_lift.mpr (le_max_left _ _)
    apply Cardinal.lift_le.{u+1,u}.mp
    rw [level_limit l hl]
    calc
      Cardinal.lift.{u+1,u} (ZFSet.iUnion (fun b : Set.Iio l => level b.val)).card ≤
          Cardinal.sum (fun b : Set.Iio l => (level b.val).card) :=
        ZFSet.lift_card_iUnion_le_sum_card
      _ ≤ Cardinal.sum (fun _ : Set.Iio l => μ) :=
        Cardinal.sum_le_sum _ _ (fun b => (ih b.val b.property).trans
          (max_le_max le_rfl (Ordinal.card_le_card b.property.le)))
      _ = Cardinal.lift.{u+1,u} l.card * Cardinal.lift.{u+1,u} μ := by
        simp only [Cardinal.sum_const, Cardinal.mk_Iio_ordinal,
          Cardinal.lift_lift]
      _ ≤ Cardinal.lift.{u+1,u} μ * Cardinal.lift.{u+1,u} μ :=
        mul_le_mul' (Cardinal.lift_le.mpr (le_max_right _ _)) le_rfl
      _ = Cardinal.lift.{u+1,u} μ := Cardinal.mul_eq_self hinf

/-- Each smaller ordinal is sent to that same actual ordinal in the level. -/
def ordinalIntoLevel (a : Ordinal.{u}) : Set.Iio a → level a :=
  fun b => ⟨b.val.toZFSet, (level_ordinal_part a b.val).mpr b.property⟩

theorem ordinalIntoLevel_spec (a : Ordinal.{u}) :
    (∀ b, (ordinalIntoLevel a b).val = b.val.toZFSet) ∧
      Function.Injective (ordinalIntoLevel a) := by
  refine ⟨fun _ => rfl, ?_⟩
  intro b c h
  apply Subtype.ext
  have he : b.val.toZFSet = c.val.toZFSet := congrArg Subtype.val h
  simpa only [Ordinal.rank_toZFSet] using congrArg ZFSet.rank he

theorem level_card_eq (a : Ordinal.{u}) (ha : Ordinal.omega0 ≤ a) :
    (level a).card = a.card := by
  apply le_antisymm
  · simpa only [max_eq_right (Ordinal.aleph0_le_card.mpr ha)] using level_card_le a
  · apply Cardinal.lift_le.{u+1,u}.mp
    rw [← ZFSet.cardinalMk_coe_sort, ← Cardinal.mk_Iio_ordinal]
    exact Cardinal.mk_le_of_injective (ordinalIntoLevel_spec a).2

/-- This is a supplied counting premise, distinct from the V=L subset-stage theorem. -/
def SubsetsInSuccessorLevel (k : Cardinal.{u}) : Prop :=
  ZFSet.powerset k.ord.toZFSet ⊆ level (Order.succ k).ord

theorem power_le_of_stage_bound (k : Cardinal.{u}) (hk : Cardinal.aleph0 ≤ k)
    (hstage : SubsetsInSuccessorLevel k) : 2 ^ k ≤ Order.succ k := by
  have hs : Ordinal.omega0 ≤ (Order.succ k).ord :=
    Ordinal.aleph0_le_card.mp (by
      rw [Cardinal.card_ord]
      exact hk.trans (Order.lt_succ k).le)
  have h := ZFSet.card_mono hstage
  rw [ZFSet.card_powerset, Ordinal.card_toZFSet, Cardinal.card_ord,
    level_card_eq _ hs, Cardinal.card_ord] at h
  exact h

theorem power_eq_of_stage_bound (k : Cardinal.{u}) (hk : Cardinal.aleph0 ≤ k)
    (hstage : SubsetsInSuccessorLevel k) : 2 ^ k = Order.succ k := by
  exact le_antisymm (power_le_of_stage_bound k hk hstage)
    (Order.succ_le_of_lt (Cardinal.cantor k))

end
end Lemmatheca.SetTheory.ConstructibleGch
