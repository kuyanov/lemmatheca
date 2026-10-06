import Mathlib.Tactic
import Mathlib.SetTheory.ZFC.Class
import Mathlib.Algebra.Order.CompleteField
import Mathlib.Order.CountableDenseLinearOrder
import Mathlib.Analysis.Real.Cardinality
import Lemmatheca.SetTheory.NumberSystems

/-! Reusable DenseLinearOrders definitions and results. -/

/-! The formal ℝ is mathlib’s standard real-number construction.
Lemmatheca.SetTheory.NumberSystems.cut_real_order_equiv states the order-preserving bridge
from rational Dedekind cuts, fixing rational points. No ordered-field structure
on Cut is needed for this bridge. -/
set_option autoImplicit false
universe u
namespace Lemmatheca.SetTheory.DenseLinearOrders

/-- Every nonempty open interval meets the given subset. -/
def OrderDense {α : Type u} [LinearOrder α] (D : Set α) : Prop :=
  ∀ x y, x < y → ∃ d ∈ D, x < d ∧ d < y

/-- The order has a countable order-dense subset. -/
def OrderSeparable (α : Type u) [LinearOrder α] : Prop :=
  ∃ D : Set α, D.Countable ∧ OrderDense D

/-- Every nonempty bounded-above subset has a least upper bound. -/
def DedekindComplete (α : Type u) [LinearOrder α] : Prop :=
  ∀ S : Set α, S.Nonempty → BddAbove S → ∃ x, IsLUB S x

/-- The rational subset of the reals is countable and order-dense; the real order is complete. -/
theorem rational_dense_reals : (Set.range (fun q : ℚ => (q : ℝ))).Countable ∧
    OrderDense (Set.range (fun q : ℚ => (q : ℝ))) ∧ DedekindComplete ℝ := by
  refine ⟨Set.countable_range _, ?_, ?_⟩
  · intro x y hxy
    obtain ⟨q, hxq, hqy⟩ := exists_rat_btwn hxy
    exact ⟨q, ⟨q, rfl⟩, hxq, hqy⟩
  · intro S hS hb
    exact ⟨sSup S, isLUB_csSup hS hb⟩

/-- An identification of a countable dense subset with the rationals extends uniquely to the reals. -/
theorem dense_identification_extension {α : Type u} [LinearOrder α] [Nonempty α]
    [DenselyOrdered α] [NoMinOrder α] [NoMaxOrder α]
    (hc : DedekindComplete α) (D : Set α) (hD : OrderDense D) (e : D ≃o ℚ) :
    ∃! f : α ≃o ℝ, ∀ d : D, f d.val = (e d : ℝ) := by
  classical
  open Lemmatheca.SetTheory.NumberSystems in
    let L : α → Set ℚ := fun x => {q | (e.symm q).val < x}
    have hL : ∀ x, IsCut (L x) := by
      intro x
      obtain ⟨y, hy⟩ := exists_lt x
      obtain ⟨d, hdD, hyd, hdx⟩ := hD y x hy
      obtain ⟨z, hz⟩ := exists_gt x
      obtain ⟨b, hbD, hxb, hbz⟩ := hD x z hz
      refine ⟨⟨e ⟨d, hdD⟩, ?_⟩, ?_, ?_, ?_⟩
      · simpa only [L, Set.mem_ofPred_eq, e.symm_apply_apply] using hdx
      · intro hu
        have hm : e ⟨b, hbD⟩ ∈ L x := hu.symm ▸ Set.mem_univ _
        have hb : b < x := by simpa only [L, Set.mem_ofPred_eq, e.symm_apply_apply] using hm
        exact hxb.not_gt hb
      · intro q hq p hpq
        exact lt_trans (show (e.symm p).val < (e.symm q).val from e.symm.strictMono hpq) hq
      · intro q hq
        obtain ⟨d, hd, hqd, hdx⟩ := hD (e.symm q).val x hq
        refine ⟨e ⟨d, hd⟩, ?_, ?_⟩
        · simpa only [L, Set.mem_ofPred_eq, e.symm_apply_apply] using hdx
        · simpa only [e.apply_symm_apply] using e.strictMono (show e.symm q < (⟨d, hd⟩ : D) from hqd)
    let C : α → Cut := fun x => ⟨L x, hL x⟩
    have horder : ∀ x y, (C x).val ⊆ (C y).val ↔ x ≤ y := by
      intro x y
      constructor
      · intro h
        by_contra hxy
        obtain ⟨d, hd, hyd, hdx⟩ := hD y x (lt_of_not_ge hxy)
        have hx : e ⟨d, hd⟩ ∈ (C x).val := by
          simpa only [C, L, Set.mem_ofPred_eq, e.symm_apply_apply] using hdx
        have hy : d < y := by
          simpa only [C, L, Set.mem_ofPred_eq, e.symm_apply_apply] using h hx
        exact hyd.not_gt hy
      · intro h q hq
        exact lt_of_lt_of_le hq h
    obtain ⟨g, hg, hrat⟩ := cut_real_order_equiv
    let v : α → ℝ := fun x => g (C x)
    have hv : ∀ x y, v x ≤ v y ↔ x ≤ y := fun x y => (hg (C x) (C y)).symm.trans (horder x y)
    have hsurj : Function.Surjective v := by
      intro r
      let A := g.symm r
      have hsep : ∀ q ∈ A.val, ∀ p ∉ A.val, q < p := by
        intro q hq p hp
        rcases lt_trichotomy q p with h | h | h
        · exact h
        · exact False.elim (hp (h ▸ hq))
        · exact False.elim (hp (A.property.2.2.1 q hq p h))
      let S : Set α := {d | ∃ hd : d ∈ D, e ⟨d, hd⟩ ∈ A.val}
      obtain ⟨q, hq⟩ := A.property.1
      have hne : S.Nonempty := ⟨(e.symm q).val, (e.symm q).property, by simpa⟩
      have hex : ∃ p, p ∉ A.val := by
        by_contra! h
        exact A.property.2.1 (Set.eq_univ_of_forall h)
      obtain ⟨p, hp⟩ := hex
      have hub : (e.symm p).val ∈ upperBounds S := by
        rintro d ⟨hd, hda⟩
        exact (show (⟨d, hd⟩ : D) < e.symm p from
          by simpa only [e.symm_apply_apply] using e.symm.strictMono (hsep _ hda _ hp)).le
      obtain ⟨x, hx⟩ := hc S hne ⟨_, hub⟩
      have hCA : C x = A := by
        apply Subtype.ext
        ext q
        constructor
        · intro hqx
          by_contra hq
          have hub : (e.symm q).val ∈ upperBounds S := by
            rintro d ⟨hd, hda⟩
            exact (show (⟨d, hd⟩ : D) < e.symm q from
              by simpa only [e.symm_apply_apply] using e.symm.strictMono (hsep _ hda _ hq)).le
          exact hqx.not_ge (hx.2 hub)
        · intro hq
          obtain ⟨p, hp, hqp⟩ := A.property.2.2.2 q hq
          have hpx : (e.symm p).val ≤ x := hx.1 ⟨(e.symm p).property, by simpa⟩
          exact lt_of_lt_of_le (show (e.symm q).val < (e.symm p).val from
            e.symm.strictMono hqp) hpx
      exact ⟨x, by dsimp [v]; rw [hCA]; exact g.apply_symm_apply r⟩
    let f : α ≃o ℝ := OrderIso.ofSurjective (OrderEmbedding.ofStrictMono v
      (strictMono_of_le_iff_le (fun x y => (hv x y).symm))) hsurj
    have hfix : ∀ d : D, f d.val = (e d : ℝ) := by
      intro d
      change g (C d.val) = _
      have hC : C d.val = rationalCut (e d) := by
        apply Subtype.ext
        ext q
        change (e.symm q).val < d.val ↔ q < e d
        change (e.symm q < d ↔ q < e d)
        simpa only [e.symm_apply_apply] using
          (e.symm.lt_iff_lt (x := q) (y := e d))
      rw [hC]
      exact hrat (e d)
    refine ⟨f, hfix, ?_⟩
    intro f' hf'
    apply OrderIso.ext
    funext x
    apply le_antisymm
    · by_contra h
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (lt_of_not_ge h)
      let d := e.symm q
      have hdx : d.val < x := (f'.lt_iff_lt).mp (by simpa only [hf', d, e.apply_symm_apply] using hq2)
      have hdxf : (q : ℝ) < f x := by
        simpa only [hfix, d, e.apply_symm_apply] using f.strictMono hdx
      exact hq1.not_gt hdxf
    · by_contra h
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (lt_of_not_ge h)
      let d := e.symm q
      have hdx : d.val < x := (f.lt_iff_lt).mp (by simpa only [hfix, d, e.apply_symm_apply] using hq2)
      have hdxf : (q : ℝ) < f' x := by
        simpa only [hf', d, e.apply_symm_apply] using f'.strictMono hdx
      exact hq1.not_gt hdxf

/-- Complete separable dense linear orders without endpoints are isomorphic to the real order. -/
theorem real_order_characterization (α : Type u) [LinearOrder α] [Nonempty α]
    [DenselyOrdered α] [NoMinOrder α] [NoMaxOrder α]
    (hc : DedekindComplete α) (hs : OrderSeparable α) : Nonempty (α ≃o ℝ) := by
  obtain ⟨D, hcount, hdense⟩ := hs
  let : Countable D := Set.countable_coe_iff.mpr hcount
  let : Nonempty D := by
    obtain ⟨x⟩ := ‹Nonempty α›
    obtain ⟨y, hy⟩ := exists_gt x
    obtain ⟨d, hd, _⟩ := hdense x y hy
    exact ⟨⟨d, hd⟩⟩
  let : DenselyOrdered D := ⟨by
    intro a b hab
    obtain ⟨d, hd, had, hdb⟩ := hdense a.val b.val hab
    exact ⟨⟨d, hd⟩, had, hdb⟩⟩
  let : NoMinOrder D := ⟨by
    intro a
    obtain ⟨x, hx⟩ := exists_lt a.val
    obtain ⟨d, hd, _, hda⟩ := hdense x a.val hx
    exact ⟨⟨d, hd⟩, hda⟩⟩
  let : NoMaxOrder D := ⟨by
    intro a
    obtain ⟨x, hx⟩ := exists_gt a.val
    obtain ⟨d, hd, had, _⟩ := hdense a.val x hx
    exact ⟨⟨d, hd⟩, had⟩⟩
  obtain ⟨e⟩ := Order.iso_of_countable_dense D ℚ
  exact ⟨(dense_identification_extension hc D hdense e).choose⟩

/-- The rational order is not Dedekind complete. -/
theorem rationals_not_complete : ¬ DedekindComplete ℚ := by
  intro hc
  have hs : OrderSeparable ℚ := ⟨Set.univ, Set.countable_univ, by
    intro x y hxy
    obtain ⟨q, hxq, hqy⟩ := exists_between hxy
    exact ⟨q, Set.mem_univ q, hxq, hqy⟩⟩
  obtain ⟨e⟩ := real_order_characterization ℚ hc hs
  have hcount : Countable ℝ := Function.Injective.countable e.symm.injective
  exact not_countable hcount

/-- Every point is the least upper bound of the dense-subset points strictly below it. -/
theorem dense_lower_lub {α : Type u} [LinearOrder α] [DenselyOrdered α] [NoMinOrder α]
    (D : Set α) (hD : OrderDense D) (x : α) : IsLUB {d | d ∈ D ∧ d < x} x := by
  constructor
  · intro d hd
    exact hd.2.le
  · intro y hy
    by_contra h
    obtain ⟨d, hdD, hyd, hdx⟩ := hD y x (lt_of_not_ge h)
    exact hyd.not_ge (hy ⟨hdD, hdx⟩)

end Lemmatheca.SetTheory.DenseLinearOrders
