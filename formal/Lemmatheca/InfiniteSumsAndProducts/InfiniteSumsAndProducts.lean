import Mathlib.Tactic
import Mathlib.SetTheory.ZFC.Ordinal
import Mathlib.Data.Nat.Nth
import Mathlib.Analysis.Real.Cardinality
import Mathlib.Analysis.Real.OfDigits
import Mathlib.Data.Fin.Pigeonhole
import Mathlib.Data.Rat.Denumerable
import Mathlib.SetTheory.Ordinal.CantorNormalForm
import Mathlib.Order.Extension.Linear

/-! Reusable InfiniteSumsAndProducts definitions and results. -/

namespace Lemmatheca.SetTheory.InfiniteSumsAndProducts
open Ordinal Order Set Function
open scoped Ordinal
universe u

theorem infinite_sum_eq_max {ι : Type u} [Infinite ι] (f : ι → Cardinal.{u})
    (hf : ∀ i, f i ≠ 0) :
    Cardinal.sum f = max (Cardinal.mk ι) (⨆ i, f i) := by
  classical
  have hI : Cardinal.mk ι ≤ Cardinal.sum f := by
    have h := Cardinal.sum_le_sum (fun _ : ι => (1 : Cardinal.{u})) f
      (fun i => Cardinal.one_le_iff_ne_zero.mpr (hf i))
    simpa using h
  have hS : (⨆ i, f i) ≠ 0 := by
    obtain ⟨i⟩ := (inferInstance : Nonempty ι)
    exact ne_of_gt ((pos_iff_ne_zero.mpr (hf i)).trans_le
      (le_ciSup Cardinal.bddAbove_of_small i))
  apply le_antisymm
  · exact (Cardinal.sum_le_mk_mul_iSup f).trans_eq
      (Cardinal.mul_eq_max_of_aleph0_le_left (Cardinal.aleph0_le_mk ι) hS)
  · exact max_le hI (Cardinal.iSup_le_sum f)

theorem sum_nonzero_support {ι : Type u} (f : ι → Cardinal.{u}) :
    Cardinal.sum f = Cardinal.sum (fun i : {i // f i ≠ 0} => f i.val) := by
  classical
  let e : (Σ i, (f i).out) ≃ (Σ i : {i // f i ≠ 0}, (f i.val).out) :=
    { toFun := fun x => ⟨⟨x.1, by
        have h : Cardinal.mk (f x.1).out ≠ 0 := Cardinal.mk_ne_zero_iff.mpr ⟨x.2⟩
        simpa using h⟩, x.2⟩
      invFun := fun x => ⟨x.1.val, x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun ⟨⟨_, _⟩, _⟩ => rfl }
  exact Cardinal.mk_congr e

/-- At each coordinate, select the least ordinal missed by its own summand. -/
noncomputable def konigDiagonal {ι : Type u} (k l : ι → Cardinal.{u})
    (F : (Σ i, (k i).ord.ToType) → ∀ i, (l i).ord.ToType) (i : ι) : Ordinal.{u} :=
  sInf {b | b < (l i).ord ∧ ∀ a, (F ⟨i, a⟩ i).toOrd.val ≠ b}

theorem konigDiagonal_spec {ι : Type u} (k l : ι → Cardinal.{u})
    (h : ∀ i, k i < l i)
    (F : (Σ i, (k i).ord.ToType) → ∀ i, (l i).ord.ToType) :
    (∀ i, konigDiagonal k l F i < (l i).ord) ∧
    (∀ x, ∃ i, (F x i).toOrd.val ≠ konigDiagonal k l F i) := by
  classical
  have hs (i : ι) : {b : Ordinal.{u} | b < (l i).ord ∧
      ∀ a, (F ⟨i, a⟩ i).toOrd.val ≠ b}.Nonempty := by
    have hn : ¬ Surjective (fun a : (k i).ord.ToType => F ⟨i, a⟩ i) := by
      intro hsurj
      have hle := Cardinal.mk_le_of_surjective hsurj
      simp only [Cardinal.mk_toType, Cardinal.card_ord] at hle
      exact (h i).not_ge hle
    simp only [Function.Surjective] at hn
    push Not at hn
    obtain ⟨b, hb⟩ := hn
    refine ⟨b.toOrd.val, b.toOrd.property, ?_⟩
    intro a he
    apply hb a
    apply ToType.mk.symm.injective
    exact Subtype.ext he
  have hmem (i : ι) := csInf_mem (hs i)
  refine ⟨fun i => (hmem i).1, ?_⟩
  rintro ⟨i, a⟩
  exact ⟨i, (hmem i).2 a⟩

theorem cofinal_sum (k : Cardinal.{u}) (hk : Cardinal.aleph0 ≤ k)
    (g : k.ord.cof.ord.ToType → Ordinal.{u}) (hg : ∀ i, g i < k.ord)
    (hc : ∀ b < k.ord, ∃ i, b ≤ g i) :
    Cardinal.sum (fun i => (g i).card) = k := by
  have hsup : (⨆ i, g i) = k.ord := by
    apply le_antisymm
    · exact Ordinal.iSup_le fun i => (hg i).le
    · apply le_of_not_gt
      intro hh
      obtain ⟨i, hi⟩ := hc ((⨆ i, g i) + 1)
        (by simpa using (Cardinal.isSuccLimit_ord hk).succ_lt hh)
      exact (lt_add_one _).not_ge (hi.trans (Ordinal.le_iSup g i))
  apply le_antisymm
  · calc
      Cardinal.sum (fun i => (g i).card) ≤ Cardinal.sum (fun _ : k.ord.cof.ord.ToType => k) :=
        Cardinal.sum_le_sum _ _ (fun i => (Cardinal.lt_ord.mp (hg i)).le)
      _ = k.ord.cof * k := by simp
      _ ≤ k * k := mul_le_mul' (Ordinal.cof_ord_le k) le_rfl
      _ = k := Cardinal.mul_eq_self hk
  · have hcard := Ordinal.card_iSup_le_sum_card.{u, u} g
    change (⨆ i, g i).card ≤ _ at hcard
    rw [hsup, Cardinal.card_ord] at hcard
    exact hcard

end Lemmatheca.SetTheory.InfiniteSumsAndProducts
