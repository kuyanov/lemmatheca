import Lemmatheca.SetTheory.NormalFunctions
import Mathlib.Tactic

/-! Particular examples and counterexamples for the human entry. -/

set_option autoImplicit false
universe u
namespace Lemmatheca.Entry.NormalFunctions
open Lemmatheca.SetTheory.NormalFunctions
open Order
open scoped Ordinal

/-- Preserving nonempty suprema need not mean preserving the empty supremum. -/
theorem empty_supremum_example :
    (ω : Ordinal.{u}) ^ sSup (∅ : Set Ordinal.{u}) = 1 ∧
    sSup ((fun a : Ordinal.{u} => ω ^ a) '' ∅) = 0 := by
  simp

/-- The first three Goodstein terms starting at four and their decreasing ordinal measures. -/
theorem goodstein_four :
    goodstein 4 0 = 4 ∧ goodstein 4 1 = 26 ∧ goodstein 4 2 = 41 ∧
    ordinalMeasure 2 4 = (ω : Ordinal.{0}) ^ ω ∧
    ordinalMeasure 3 26 = (ω : Ordinal.{0}) ^ 2 * 2 + ω * 2 + 2 ∧
    ordinalMeasure 4 41 = (ω : Ordinal.{0}) ^ 2 * 2 + ω * 2 + 1 ∧
    ordinalMeasure 3 26 < ordinalMeasure 2 4 ∧ ordinalMeasure 4 41 < ordinalMeasure 3 26 := by
  let t₂ : ONote := .oadd (.oadd 1 1 0) 1 0
  let t₃ : ONote := .oadd (.oadd 0 2 0) 2 (.oadd 1 2 (.oadd 0 2 0))
  let t₄ : ONote := .oadd (.oadd 0 2 0) 2 (.oadd 1 2 (.oadd 0 1 0))
  have h₂ : hereditary 2 4 = t₂ := by
    symm
    apply (hereditary_spec 2 4 (by omega)).2.2.2
    · norm_num [t₂, Canonical, evalNat, ONote.ofNat]
    · norm_num [t₂, evalNat, ONote.ofNat]
  have h₃ : hereditary 3 26 = t₃ := by
    symm
    apply (hereditary_spec 3 26 (by omega)).2.2.2
    · norm_num [t₃, Canonical, evalNat, ONote.ofNat]
    · norm_num [t₃, evalNat, ONote.ofNat]
  have h₄ : hereditary 4 41 = t₄ := by
    symm
    apply (hereditary_spec 4 41 (by omega)).2.2.2
    · norm_num [t₄, Canonical, evalNat, ONote.ofNat]
    · norm_num [t₄, evalNat, ONote.ofNat]
  have hg₁ : goodstein 4 1 = 26 := by
    norm_num [goodstein, baseChange, h₂, t₂, evalNat, ONote.ofNat]
  have hg₂ : goodstein 4 2 = 41 := by
    change (if goodstein 4 1 = 0 then 0 else baseChange 3 4 (goodstein 4 1) - 1) = 41
    norm_num [hg₁, baseChange, h₃, t₃, evalNat, ONote.ofNat]
  refine ⟨rfl, hg₁, hg₂, ?_, ?_, ?_, ?_, ?_⟩
  · simp [ordinalMeasure, h₂, t₂, ONote.repr]
  · norm_num [ordinalMeasure, h₃, t₃, ONote.repr, ONote.ofNat, add_assoc]
    norm_num [← Ordinal.opow_natCast]
  · norm_num [ordinalMeasure, h₄, t₄, ONote.repr, ONote.ofNat, add_assoc]
    norm_num [← Ordinal.opow_natCast]
  · have h := goodstein_descent 4 0 (by decide)
    change ordinalMeasure 3 (goodstein 4 1) < ordinalMeasure 2 4 at h
    rwa [hg₁] at h
  · simpa only [hg₁, hg₂, Nat.reduceAdd] using goodstein_descent 4 1 (by rw [hg₁]; decide)

end Lemmatheca.Entry.NormalFunctions
