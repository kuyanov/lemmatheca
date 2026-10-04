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
    IsCofinal s ↔ (⨆ x : s, x.val.toOrd.val) = a := by sorry

noncomputable def cofinalSequence (a : Ordinal.{u})
    (f : a.cof.ord.ToType → Ordinal.{u}) : a.cof.ord.ToType → Ordinal.{u} :=
  (wellFounded_lt : WellFounded ((· < ·) : a.cof.ord.ToType → a.cof.ord.ToType → Prop)).fix
    (fun i ih => max (f i) (⨆ j : Set.Iio i, ih j.val j.property + 1))

theorem cofinalSequence_equation (a : Ordinal.{u})
    (f : a.cof.ord.ToType → Ordinal.{u}) (i : a.cof.ord.ToType) :
    cofinalSequence a f i = max (f i)
      (⨆ j : Set.Iio i, cofinalSequence a f j.val + 1) := by sorry

theorem cofinalSequence_spec (a : Ordinal.{u}) (ha : IsSuccLimit a)
    (f : a.cof.ord.ToType → Ordinal.{u}) (hf : ∀ i, f i < a)
    (hc : ∀ b < a, ∃ i, b ≤ f i) :
    (∀ i, cofinalSequence a f i < a ∧ f i ≤ cofinalSequence a f i) ∧
    StrictMono (cofinalSequence a f) ∧
    (∀ b < a, ∃ i, b ≤ cofinalSequence a f i) := by sorry

/-- A cofinal range alone does not justify restricting to a cofinal domain subset.
Take f(2n)=n and f(2n+1)=0, and restrict to the odd numbers. -/
theorem cofinal_restriction_counterexample :
    ∃ (f : ℕ → ℕ) (s : Set ℕ),
      IsCofinal (range f) ∧ IsCofinal s ∧ ¬ IsCofinal (f '' s) := by sorry

theorem regular_iff_bounded (k : Cardinal.{u}) (hk : Cardinal.aleph0 ≤ k) :
    k.IsRegular ↔ ∀ s : Set k.ord.ToType, Cardinal.mk s < k →
      ∃ b : k.ord.ToType, ∀ x ∈ s, x < b := by sorry

theorem regular_iff_small_unions (k : Cardinal.{u}) (hk : Cardinal.aleph0 ≤ k) :
    k.IsRegular ↔ ∀ (ι α : Type u) (A : ι → Set α), Cardinal.mk ι < k →
      (∀ i, Cardinal.mk (A i) < k) → Cardinal.mk (⋃ i, A i) < k := by sorry

/-- Select the least index containing a point of a union. -/
noncomputable def leastUnionIndex {ι : Type u} {α : Type v}
    [LinearOrder ι] [WellFoundedLT ι] (A : ι → Set α) (x : ⋃ i, A i) : ι :=
  wellFounded_lt.min {i | x.val ∈ A i} (Set.mem_iUnion.mp x.property)

theorem leastUnionIndex_mem {ι : Type u} {α : Type v}
    [LinearOrder ι] [WellFoundedLT ι] (A : ι → Set α) (x : ⋃ i, A i) :
    x.val ∈ A (leastUnionIndex A x) := by sorry

noncomputable def unionCode {ι : Type u} {α : Type v} {β : Type w}
    [LinearOrder ι] [WellFoundedLT ι] (A : ι → Set α) (e : ∀ i, A i → β)
    (x : ⋃ i, A i) : ι × β :=
  (leastUnionIndex A x, e _ ⟨x.val,
    wellFounded_lt.min_mem {i | x.val ∈ A i} (Set.mem_iUnion.mp x.property)⟩)

theorem unionCode_injective {ι : Type u} {α : Type v} {β : Type w}
    [LinearOrder ι] [WellFoundedLT ι] (A : ι → Set α) (e : ∀ i, A i → β)
    (he : ∀ i, Injective (e i)) : Injective (unionCode A e) := by sorry

end Lemmatheca.Entry.Cofinality
