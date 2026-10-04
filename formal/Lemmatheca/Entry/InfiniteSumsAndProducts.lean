import Lemmatheca.Entry.Cofinality
import Mathlib.SetTheory.Cardinal.Continuum

namespace Lemmatheca.Entry.InfiniteSumsAndProducts
open Ordinal Order Set Function
open scoped Ordinal
universe u

theorem infinite_sum_eq_max {ι : Type u} [Infinite ι] (f : ι → Cardinal.{u})
    (hf : ∀ i, f i ≠ 0) :
    Cardinal.sum f = max (Cardinal.mk ι) (⨆ i, f i) := by sorry

theorem sum_nonzero_support {ι : Type u} (f : ι → Cardinal.{u}) :
    Cardinal.sum f = Cardinal.sum (fun i : {i // f i ≠ 0} => f i.val) := by sorry

/-- At each coordinate, select the least ordinal missed by its own summand. -/
noncomputable def konigDiagonal {ι : Type u} (k l : ι → Cardinal.{u})
    (F : (Σ i, (k i).ord.ToType) → ∀ i, (l i).ord.ToType) (i : ι) : Ordinal.{u} :=
  sInf {b | b < (l i).ord ∧ ∀ a, (F ⟨i, a⟩ i).toOrd.val ≠ b}

theorem konigDiagonal_spec {ι : Type u} (k l : ι → Cardinal.{u})
    (h : ∀ i, k i < l i)
    (F : (Σ i, (k i).ord.ToType) → ∀ i, (l i).ord.ToType) :
    (∀ i, konigDiagonal k l F i < (l i).ord) ∧
    (∀ x, ∃ i, (F x i).toOrd.val ≠ konigDiagonal k l F i) := by sorry

theorem cofinal_sum (k : Cardinal.{u}) (hk : Cardinal.aleph0 ≤ k)
    (g : k.ord.cof.ord.ToType → Ordinal.{u}) (hg : ∀ i, g i < k.ord)
    (hc : ∀ b < k.ord, ∃ i, b ≤ g i) :
    Cardinal.sum (fun i => (g i).card) = k := by sorry

/-- This is a statement about the strength of the bound, not about the value
of the continuum. For example, aleph indexed by omega_1 is singular and has
cofinality aleph_1. No independence assertion is encoded here. -/
theorem uncountable_cofinality_not_regularity :
    ∃ k : Cardinal.{u}, Cardinal.aleph0 < k.ord.cof ∧ k.IsSingular := by sorry

end Lemmatheca.Entry.InfiniteSumsAndProducts
