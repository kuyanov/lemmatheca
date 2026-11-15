import Lemmatheca.CardinalSaturationAndHomogeneity.Saturation
import Mathlib.SetTheory.Cardinal.Regular

namespace Lemmatheca.ModelTheory.CardinalSaturation

open Cardinal Ordinal

universe w z

variable {M : Type w} {κ : Cardinal.{z}}

/-- Increasing stage sets, with the actual union at every nonzero limit. -/
def ContinuousIncreasing (A : Ordinal.{z} → Set M) : Prop :=
  Monotone A ∧ ∀ α, Order.IsSuccLimit α → A α = ⋃ β : Set.Iio α, A β.val

/-- Every successor adds at most two actual points. -/
def AddsAtMostTwo (A : Ordinal.{z} → Set M) : Prop :=
  ∀ α, #(A (α + 1) \ A α : Set M) ≤ 2

private theorem added_points_bound (A : Ordinal.{z} → Set M)
    (hA : ContinuousIncreasing A) (hstep : AddsAtMostTwo A) (α : Ordinal.{z}) :
    Cardinal.lift.{z} (#(A α \ A 0 : Set M)) ≤ 2 * Cardinal.lift.{w} α.card := by
  classical
  have cover : ∀ a, ∀ x ∈ A a, x ∈ A 0 ∨
      ∃ b < a, x ∈ A (b+1) \ A b := by
    intro a
    induction a using Ordinal.limitRecOn with
    | zero => exact fun _ hx => Or.inl hx
    | add_one a ih =>
      intro x hx
      by_cases ha : x ∈ A a
      · rcases ih x ha with h0 | ⟨b,hb,hx⟩
        · exact Or.inl h0
        · exact Or.inr ⟨b, hb.trans (lt_add_one a), hx⟩
      · exact Or.inr ⟨a, lt_add_one a, hx, ha⟩
    | limit l hl ih =>
      intro x hx
      rw [hA.2 l hl] at hx
      obtain ⟨b,hb⟩ := Set.mem_iUnion.mp hx
      rcases ih b.val b.property x hb with h0 | ⟨c,hc,hx⟩
      · exact Or.inl h0
      · exact Or.inr ⟨c,hc.trans b.property,hx⟩
  let e : Shrink.{z} (Set.Iio α) ≃ Set.Iio α := (equivShrink _).symm
  let D : Shrink.{z} (Set.Iio α) → Set M := fun b =>
    A ((e b).val+1) \ A (e b).val
  have he : #(Shrink.{z} (Set.Iio α)) = α.card := by
    apply Cardinal.lift_injective.{z+1,z}
    rw [Cardinal.lift_mk_shrink'', Cardinal.mk_Iio_ordinal]
  have hs : (A α \ A 0 : Set M) ⊆ ⋃ b, D b := by
    intro x hx
    rcases (cover α x hx.1).resolve_left hx.2 with ⟨b,hb,hx⟩
    exact Set.mem_iUnion.mpr ⟨e.symm ⟨b,hb⟩, by
      simpa only [D, Equiv.apply_symm_apply] using hx⟩
  calc
    Cardinal.lift.{z} (#(A α \ A 0 : Set M)) ≤ Cardinal.lift.{z} (#(⋃ b, D b)) :=
      Cardinal.lift_le.mpr (Cardinal.mk_le_mk_of_subset hs)
    _ ≤ Cardinal.sum (fun b => #(D b)) := Cardinal.mk_iUnion_le_sum_mk_lift
    _ ≤ Cardinal.sum (fun _ : Shrink.{z} (Set.Iio α) => (2 : Cardinal.{w})) :=
      Cardinal.sum_le_sum _ _ (fun b => hstep (e b).val)
    _ = 2 * Cardinal.lift.{w} α.card := by
      simp only [Cardinal.sum_const, he, Cardinal.lift_ofNat, mul_comm]

theorem stage_size_bound (A : Ordinal.{z} → Set M)
    (hA : ContinuousIncreasing A) (hstep : AddsAtMostTwo A) (α : Ordinal.{z}) :
    Cardinal.lift.{z} (#(A α)) ≤
      Cardinal.lift.{z} (#(A 0)) + 2 * Cardinal.lift.{w} α.card := by
  have hs : A α ⊆ A 0 ∪ (A α \ A 0) := by
    intro x hx
    by_cases h0 : x ∈ A 0
    · exact Or.inl h0
    · exact Or.inr ⟨hx,h0⟩
  have h := Cardinal.lift_le.mpr
    ((Cardinal.mk_le_mk_of_subset hs).trans (Cardinal.mk_union_le _ _))
  rw [Cardinal.lift_add] at h
  exact h.trans (add_le_add le_rfl (added_points_bound A hA hstep α))

theorem finite_stage_bound (A : Ordinal.{z} → Set M)
    (hA : ContinuousIncreasing A) (hstep : AddsAtMostTwo A)
    (hzero : (A 0).Finite) (n : ℕ) : (A n).Finite := by
  induction n with
  | zero => simpa only [Nat.cast_zero] using hzero
  | succ n ih =>
    have hd : (A ((n : Ordinal.{z})+1) \ A n : Set M).Finite :=
      Cardinal.lt_aleph0_iff_set_finite.mp
        ((hstep n).trans_lt (Cardinal.natCast_lt_aleph0 (n := 2)))
    have hfin := ih.union hd
    rw [Set.union_sdiff_cancel (hA.1 (le_add_right (le_refl (n : Ordinal.{z}))))] at hfin
    simpa only [Nat.cast_add_one] using hfin

theorem stage_below (hκ : ℵ₀ ≤ κ) (A : Ordinal.{z} → Set M)
    (hA : ContinuousIncreasing A) (hstep : AddsAtMostTwo A)
    (hzero : Below κ (A 0)) (α : Ordinal.{z}) (hα : α < κ.ord) :
    Below κ (A α) := by
  have hκ' : ℵ₀ ≤ Cardinal.lift.{w} κ := Cardinal.aleph0_le_lift.mpr hκ
  have ha : Cardinal.lift.{w} α.card < Cardinal.lift.{w} κ :=
    Cardinal.lift_lt.mpr (Cardinal.lt_ord.mp hα)
  have htwo : (2 : Cardinal.{max w z}) < Cardinal.lift.{w} κ :=
    Cardinal.natCast_lt_aleph0.trans_le hκ'
  exact (stage_size_bound A hA hstep α).trans_lt
    (Cardinal.add_lt_of_lt hκ' hzero (Cardinal.mul_lt_of_lt hκ' htwo ha))

theorem countable_stage_bound (A : Ordinal.{z} → Set M)
    (hA : ContinuousIncreasing A) (hstep : AddsAtMostTwo A) :
    Cardinal.lift.{z} (#(A Ordinal.omega0 \ A 0 : Set M)) ≤ ℵ₀ := by
  simpa only [Ordinal.card_omega0, Cardinal.lift_aleph0, Cardinal.ofNat_mul_aleph0]
    using added_points_bound A hA hstep Ordinal.omega0

/-- The larger carrier cannot be enumerated by the chosen number of rounds. -/
theorem no_small_enumeration (X : Type w) (hX : ¬ AtMost κ X) :
    ¬ ∃ e : κ.out → X, Function.Surjective e := by
  rintro ⟨e,he⟩
  apply hX
  simpa only [AtMost, Cardinal.mk_out] using
    Cardinal.lift_mk_le_lift_mk_of_surjective he

end Lemmatheca.ModelTheory.CardinalSaturation
