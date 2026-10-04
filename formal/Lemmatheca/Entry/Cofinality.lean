import Lemmatheca.Entry.OrdinalPowers
import Lemmatheca.Entry.InfiniteCardinalArithmetic
import Mathlib.SetTheory.Cardinal.Regular

/-! Cofinal subsets use the small representative `a.ToType`. Its elements have
ordinal positions `x.toOrd.val`, so all cardinalities stay in universe u. -/
namespace Lemmatheca.Entry.Cofinality
open Ordinal Order Set Function
open scoped Ordinal
universe u v w

theorem cofinal_iff_sup (a : Ordinal.{u}) (ha : IsSuccLimit a) (s : Set a.ToType) :
    IsCofinal s ↔ (⨆ x : s, x.val.toOrd.val) = a := by
  classical
  constructor
  · intro hc
    apply le_antisymm
    · exact Ordinal.iSup_le fun x => x.val.toOrd.property.le
    · apply le_of_not_gt
      intro hsup
      let x : a.ToType := ToType.mk ⟨(⨆ x : s, x.val.toOrd.val) + 1, by simpa using ha.succ_lt hsup⟩
      obtain ⟨y, hy, hxy⟩ := hc x
      have hpos : (⨆ x : s, x.val.toOrd.val) + 1 ≤ y.toOrd.val := by
        have h' := ToType.mk.symm.monotone hxy
        change (ToType.mk.symm x).val ≤ (ToType.mk.symm y).val at h'
        simpa only [x, OrderIso.symm_apply_apply] using h'
      exact (lt_add_one _).not_ge (hpos.trans (Ordinal.le_iSup (fun x : s => x.val.toOrd.val) ⟨y, hy⟩))
  · intro hs x
    by_contra h
    push Not at h
    have hh : (⨆ y : s, y.val.toOrd.val) ≤ x.toOrd.val :=
      Ordinal.iSup_le fun y => (ToType.mk.symm.monotone (h y.val y.property).le)
    exact x.toOrd.property.not_ge (hs ▸ hh)

noncomputable def cofinalSequence (a : Ordinal.{u})
    (f : a.cof.ord.ToType → Ordinal.{u}) : a.cof.ord.ToType → Ordinal.{u} :=
  (wellFounded_lt : WellFounded ((· < ·) : a.cof.ord.ToType → a.cof.ord.ToType → Prop)).fix
    (fun i ih => max (f i) (⨆ j : Set.Iio i, ih j.val j.property + 1))

theorem cofinalSequence_equation (a : Ordinal.{u})
    (f : a.cof.ord.ToType → Ordinal.{u}) (i : a.cof.ord.ToType) :
    cofinalSequence a f i = max (f i)
      (⨆ j : Set.Iio i, cofinalSequence a f j.val + 1) := by
  exact WellFounded.fix_eq _ _ i

theorem cofinalSequence_spec (a : Ordinal.{u}) (ha : IsSuccLimit a)
    (f : a.cof.ord.ToType → Ordinal.{u}) (hf : ∀ i, f i < a)
    (hc : ∀ b < a, ∃ i, b ≤ f i) :
    (∀ i, cofinalSequence a f i < a ∧ f i ≤ cofinalSequence a f i) ∧
    StrictMono (cofinalSequence a f) ∧
    (∀ b < a, ∃ i, b ≤ cofinalSequence a f i) := by
  have hg : ∀ i, cofinalSequence a f i < a := by
    intro i
    induction i using WellFoundedLT.induction with
    | ind i ih =>
      rw [cofinalSequence_equation]
      apply max_lt (hf i)
      apply Ordinal.iSup_lt_of_lt_cof
      · simpa only [Cardinal.mk_toType, Cardinal.card_ord] using
          (Cardinal.mk_Iio_lt i (by simp [Cardinal.mk_toType]))
      · intro j
        simpa using ha.succ_lt (ih j.val j.property)
  have hdom : ∀ i, f i ≤ cofinalSequence a f i := by
    intro i; rw [cofinalSequence_equation]; exact le_max_left _ _
  refine ⟨fun i => ⟨hg i, hdom i⟩, ?_, ?_⟩
  · intro i j hij
    rw [cofinalSequence_equation a f j]
    exact (lt_add_one _).trans_le ((Ordinal.le_iSup
      (fun x : Set.Iio j => cofinalSequence a f x.val + 1) ⟨i, hij⟩).trans (le_max_right _ _))
  · intro b hb
    obtain ⟨i, hi⟩ := hc b hb
    exact ⟨i, hi.trans (hdom i)⟩

/-- A cofinal range alone does not justify restricting to a cofinal domain subset.
Take f(2n)=n and f(2n+1)=0, and restrict to the odd numbers. -/
theorem cofinal_restriction_counterexample :
    ∃ (f : ℕ → ℕ) (s : Set ℕ),
      IsCofinal (range f) ∧ IsCofinal s ∧ ¬ IsCofinal (f '' s) := by
  let f : ℕ → ℕ := fun n => if n % 2 = 0 then n / 2 else 0
  refine ⟨f, {n | n % 2 = 1}, ?_, ?_, ?_⟩
  · intro n
    refine ⟨f (2 * n), Set.mem_range_self _, ?_⟩
    simp [f]
  · intro n
    refine ⟨2 * n + 1, ?_, by omega⟩
    simp
  · intro h
    obtain ⟨x, ⟨n, hn, rfl⟩, hx⟩ := h 1
    dsimp [f] at hx
    have hn' : n % 2 ≠ 0 := by change n % 2 = 1 at hn; omega
    simp [hn'] at hx

theorem regular_iff_bounded (k : Cardinal.{u}) (hk : Cardinal.aleph0 ≤ k) :
    k.IsRegular ↔ ∀ s : Set k.ord.ToType, Cardinal.mk s < k →
      ∃ b : k.ord.ToType, ∀ x ∈ s, x < b := by
  classical
  constructor
  · intro h s hs
    have hb : (⨆ x : s, x.val.toOrd.val + 1) < k.ord :=
      Ordinal.iSup_add_one_lt_of_lt_cof (by simpa [h.cof_ord] using hs)
        (fun x => x.val.toOrd.property)
    refine ⟨ToType.mk ⟨_, hb⟩, ?_⟩
    intro x hx
    apply ToType.mk.symm.lt_iff_lt.mp
    change x.toOrd.val < (ToType.mk.symm (ToType.mk _)).val
    rw [OrderIso.symm_apply_apply]
    exact Ordinal.lt_iSup_add_one (fun y : s => y.val.toOrd.val) ⟨x, hx⟩
  · intro hb
    refine ⟨hk, ?_⟩
    rw [← cof_toType]
    apply Order.le_cof_iff.mpr
    intro s hs
    by_contra h
    obtain ⟨b, hbound⟩ := hb s (lt_of_not_ge h)
    obtain ⟨x, hx, hbx⟩ := hs b
    exact (hbound x hx).not_ge hbx

theorem regular_iff_small_unions (k : Cardinal.{u}) (hk : Cardinal.aleph0 ≤ k) :
    k.IsRegular ↔ ∀ (ι α : Type u) (A : ι → Set α), Cardinal.mk ι < k →
      (∀ i, Cardinal.mk (A i) < k) → Cardinal.mk (⋃ i, A i) < k := by
  classical
  constructor
  · intro h ι α A hi hA
    exact (Cardinal.card_iUnion_lt_iff_forall_of_isRegular h hi).mpr hA
  · intro h
    apply (regular_iff_bounded k hk).mpr
    intro s hs
    by_contra hb
    push Not at hb
    let A : s → Set k.ord.ToType := fun x => Set.Iio x.val
    have hA (x : s) : Cardinal.mk (A x) < k :=
      by
      simpa only [Cardinal.mk_toType, Cardinal.card_ord] using
        (Cardinal.mk_Iio_lt x.val (by simp [Cardinal.mk_toType]))
    have hu : (⋃ x : s, A x) = Set.univ := by
      apply Set.eq_univ_of_forall
      intro y
      let b : k.ord.ToType := ToType.mk ⟨y.toOrd.val + 1,
        by simpa using (Cardinal.isSuccLimit_ord hk).succ_lt y.toOrd.property⟩
      obtain ⟨x, hx, hbx⟩ := hb b
      refine Set.mem_iUnion.mpr ⟨⟨x, hx⟩, ?_⟩
      change y < x
      apply lt_of_lt_of_le (b := b) _ hbx
      apply ToType.mk.symm.lt_iff_lt.mp
      change y.toOrd.val < (ToType.mk.symm b).val
      simp only [b, OrderIso.symm_apply_apply]
      exact lt_add_one _
    have hout := h s k.ord.ToType A hs hA
    rw [hu] at hout
    simp [Cardinal.mk_toType] at hout

/-- Select the least index containing a point of a union. -/
noncomputable def leastUnionIndex {ι : Type u} {α : Type v}
    [LinearOrder ι] [WellFoundedLT ι] (A : ι → Set α) (x : ⋃ i, A i) : ι :=
  wellFounded_lt.min {i | x.val ∈ A i} (Set.mem_iUnion.mp x.property)

theorem leastUnionIndex_mem {ι : Type u} {α : Type v}
    [LinearOrder ι] [WellFoundedLT ι] (A : ι → Set α) (x : ⋃ i, A i) :
    x.val ∈ A (leastUnionIndex A x) := by
  exact (wellFounded_lt : WellFounded ((· < ·) : ι → ι → Prop)).min_mem
    {i | x.val ∈ A i} (Set.mem_iUnion.mp x.property)

noncomputable def unionCode {ι : Type u} {α : Type v} {β : Type w}
    [LinearOrder ι] [WellFoundedLT ι] (A : ι → Set α) (e : ∀ i, A i → β)
    (x : ⋃ i, A i) : ι × β :=
  (leastUnionIndex A x, e _ ⟨x.val,
    wellFounded_lt.min_mem {i | x.val ∈ A i} (Set.mem_iUnion.mp x.property)⟩)

theorem unionCode_injective {ι : Type u} {α : Type v} {β : Type w}
    [LinearOrder ι] [WellFoundedLT ι] (A : ι → Set α) (e : ∀ i, A i → β)
    (he : ∀ i, Injective (e i)) : Injective (unionCode A e) := by
  intro x y h
  have hi : leastUnionIndex A x = leastUnionIndex A y := congrArg Prod.fst h
  have hv := congrArg Prod.snd h
  change e (leastUnionIndex A x) _ = e (leastUnionIndex A y) _ at hv
  have hkey : ∀ (i j : ι) (xx : A i) (yy : A j),
      i = j → e i xx = e j yy → xx.val = yy.val := by
    intro i j xx yy hij hvv
    subst j
    exact congrArg (fun z : A i => z.val) (he i hvv)
  exact Subtype.ext (hkey _ _ _ _ hi hv)

end Lemmatheca.Entry.Cofinality
