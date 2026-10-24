import Lemmatheca.RankReflection.RankModels
import Lemmatheca.Cofinality.Cofinality
import Mathlib.SetTheory.Cardinal.Regular

namespace Lemmatheca.SetTheory.InaccessibleCardinals
open FirstOrder FirstOrder.Language
open Lemmatheca.SetTheory.MembershipModels
open Lemmatheca.SetTheory.Absoluteness
open Lemmatheca.SetTheory.RankReflection
universe u
noncomputable section

/-- A supplied cardinal, with no assertion that any such cardinal exists. -/
def WeaklyInaccessible (k : Cardinal.{u}) : Prop :=
  Cardinal.aleph0 < k ∧ k.IsRegular ∧ Order.IsSuccLimit k

theorem strong_implies_weak (k : Cardinal.{u}) (hk : k.IsInaccessible) :
    WeaklyInaccessible k := by
  exact ⟨hk.aleph0_lt,hk.isRegular,hk.isSuccLimit⟩

theorem inaccessible_ordinal (k : Cardinal.{u}) (hk : k.IsInaccessible) :
    Order.IsSuccLimit k.ord ∧ Ordinal.omega0.{u} < k.ord := by
  exact ⟨Cardinal.isSuccLimit_ord hk.aleph0_lt.le,
    by simpa only [Cardinal.ord_aleph0] using Cardinal.ord_strictMono hk.aleph0_lt⟩

theorem stages_small (k : Cardinal.{u}) (hk : k.IsInaccessible)
    (b : Ordinal.{u}) (hb : b < k.ord) : (ZFSet.vonNeumann b).card < k := by
  rw [ZFSet.card_vonNeumann,← hk.preBeth_ord]
  exact Cardinal.preBeth_strictMono hb

theorem members_small (k : Cardinal.{u}) (hk : k.IsInaccessible)
    (x : ZFSet.{u}) (hx : x ∈ ZFSet.vonNeumann k.ord) : x.card < k := by
  exact (ZFSet.card_mono (ZFSet.subset_vonNeumann_self x)).trans_lt
    (stages_small k hk x.rank (ZFSet.mem_vonNeumann.mp hx))

/-- The actual supremum of the supplied output ranks plus one. -/
def outputBound (I : ZFSet.{u}) (f : I → ZFSet.{u}) : Ordinal.{u} :=
  ⨆ i : I, (f i).rank + 1

theorem small_family_range (k : Cardinal.{u}) (hunc : Cardinal.aleph0 < k)
    (hreg : k.IsRegular) (I : ZFSet.{u}) (hI : I.card < k)
    (f : I → ZFSet.{u}) (hf : ∀ i, f i ∈ ZFSet.vonNeumann k.ord) :
    outputBound I f < k.ord ∧
    (∀ i, f i ∈ ZFSet.vonNeumann (outputBound I f)) ∧
    ZFSet.range f ∈ ZFSet.vonNeumann k.ord := by
  let hreg' : k.IsRegular := ⟨hunc.le,hreg.2⟩
  have hb : outputBound I f < k.ord := by
    apply Ordinal.lift_iSup_add_one_lt_of_lt_cof
    · simpa only [ZFSet.cardinalMk_coe_sort,Cardinal.lift_lift,← Ordinal.lift_cof,
        hreg'.cof_ord,Cardinal.lift_lt] using hI
    · intro i
      exact ZFSet.mem_vonNeumann.mp (hf i)
  refine ⟨hb,?_,?_⟩
  · intro i
    exact ZFSet.mem_vonNeumann.mpr (Ordinal.lt_iSup_add_one (fun i : I => (f i).rank) i)
  · rw [ZFSet.mem_vonNeumann,ZFSet.rank_range]
    simpa only [outputBound,Order.succ_eq_add_one] using hb

/-- The fixed native matrix has parameter slots followed by input and output. -/
def ReplacementFunctional (D : ZFSet.{u}) (hD : D.IsTransitive) {n}
    (p : membershipLanguage.BoundedFormula Empty (n+2)) (a : Fin n → D) (x : D) : Prop :=
  ∀ i : x.val, ∃! y : D,
    setSatisfies D p (Fin.snoc (Fin.snoc a ⟨i.val,hD x.val x.property i.property⟩) y)

def replacementOutput (D : ZFSet.{u}) (hD : D.IsTransitive) {n}
    (p : membershipLanguage.BoundedFormula Empty (n+2)) (a : Fin n → D) (x : D)
    (hf : ReplacementFunctional D hD p a x) (i : x.val) : D := (hf i).choose

def replacementRange (D : ZFSet.{u}) (hD : D.IsTransitive) {n}
    (p : membershipLanguage.BoundedFormula Empty (n+2)) (a : Fin n → D) (x : D)
    (hf : ReplacementFunctional D hD p a x) : ZFSet.{u} :=
  ZFSet.range (fun i => (replacementOutput D hD p a x hf i).val)

theorem replacementOutput_spec (D : ZFSet.{u}) (hD : D.IsTransitive) {n}
    (p : membershipLanguage.BoundedFormula Empty (n+2)) (a : Fin n → D) (x : D)
    (hf : ReplacementFunctional D hD p a x) (i : x.val) :
    setSatisfies D p (Fin.snoc (Fin.snoc a ⟨i.val,hD x.val x.property i.property⟩)
      (replacementOutput D hD p a x hf i)) ∧
    ∀ y : D, setSatisfies D p
      (Fin.snoc (Fin.snoc a ⟨i.val,hD x.val x.property i.property⟩) y) →
      y = replacementOutput D hD p a x hf i := by
  exact (hf i).choose_spec

theorem inaccessible_replacement (k : Cardinal.{u}) (hk : k.IsInaccessible) {n}
    (p : membershipLanguage.BoundedFormula Empty (n+2))
    (a : Fin n → ZFSet.vonNeumann k.ord) (x : ZFSet.vonNeumann k.ord)
    (hf : ReplacementFunctional (ZFSet.vonNeumann k.ord)
      (ZFSet.isTransitive_vonNeumann _) p a x) :
    replacementRange (ZFSet.vonNeumann k.ord) (ZFSet.isTransitive_vonNeumann _) p a x hf ∈
      ZFSet.vonNeumann k.ord ∧
    ∀ y : ZFSet.vonNeumann k.ord,
      y.val ∈ replacementRange (ZFSet.vonNeumann k.ord)
        (ZFSet.isTransitive_vonNeumann _) p a x hf ↔
      ∃ i : x.val, setSatisfies (ZFSet.vonNeumann k.ord) p
        (Fin.snoc (Fin.snoc a
          ⟨i.val,ZFSet.isTransitive_vonNeumann _ x.val x.property i.property⟩) y) := by
  let D := ZFSet.vonNeumann k.ord
  let hD := ZFSet.isTransitive_vonNeumann k.ord
  have hrange := (small_family_range k hk.aleph0_lt hk.isRegular x.val
    (members_small k hk x.val x.property)
    (fun i => (replacementOutput D hD p a x hf i).val)
    (fun i => (replacementOutput D hD p a x hf i).property)).2.2
  refine ⟨hrange,?_⟩
  intro y
  rw [replacementRange,ZFSet.mem_range]
  constructor
  · rintro ⟨i,hi⟩
    have he : replacementOutput D hD p a x hf i = y := Subtype.ext hi
    exact ⟨i,he ▸ (replacementOutput_spec D hD p a x hf i).1⟩
  · rintro ⟨i,hi⟩
    exact ⟨i,congrArg Subtype.val ((replacementOutput_spec D hD p a x hf i).2 y hi).symm⟩

/-- A set relation on an object has the actual finite rank overhead stated in
 the human proof, using the existing Kuratowski pair encoding. -/
theorem relation_rank_overhead (l : Ordinal.{u}) (hl : Order.IsSuccLimit l)
    (x R : ZFSet.{u}) (hx : x ∈ ZFSet.vonNeumann l) (hR : R ⊆ ZFSet.prod x x) :
    R.rank ≤ x.rank + 3 ∧ R ∈ ZFSet.vonNeumann l := by
  have hxx : x ∪ x = x := by ext z; simp
  have hsub : R ⊆ ZFSet.powerset (ZFSet.powerset x) := by
    intro z hz
    have hp := hR hz
    unfold ZFSet.prod ZFSet.pairSep at hp
    simpa only [hxx] using (ZFSet.mem_sep.mp hp).1
  have hb : R.rank ≤ x.rank+3 := by
    have hr := ZFSet.rank_mono hsub
    simp only [ZFSet.rank_powerset,Order.succ_eq_add_one] at hr
    apply hr.trans
    convert (le_add_right (le_refl (x.rank+1+1)) : x.rank+1+1 ≤ x.rank+1+1+1) using 1
    norm_num [add_assoc]
  refine ⟨hb,ZFSet.mem_vonNeumann.mpr (hb.trans_lt ?_)⟩
  exact hl.add_natCast_lt (ZFSet.mem_vonNeumann.mp hx) 3

end
end Lemmatheca.SetTheory.InaccessibleCardinals
