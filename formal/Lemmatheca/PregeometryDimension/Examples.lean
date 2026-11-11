import Lemmatheca.PregeometryDimension.Identity
import Lemmatheca.StronglyMinimalSets.Examples
import Mathlib.SetTheory.Cardinal.Arithmetic

namespace Lemmatheca.Entry.PregeometryDimension
open FirstOrder FirstOrder.Language
open Lemmatheca.ModelTheory.StronglyMinimalSets
open Lemmatheca.ModelTheory.StronglyMinimalSets.Pregeometry
open Lemmatheca.Entry.StronglyMinimalSets
universe w
noncomputable section

theorem equality_acl_identity {M : Type w} [FirstOrder.Language.empty.Structure M] [Infinite M] :
    aclPregeometry FirstOrder.Language.empty.infiniteTheory equality_stronglyMinimalTheory =
      identityPregeometry M := by
  have hcl : (aclPregeometry Language.empty.infiniteTheory equality_stronglyMinimalTheory (M := M)).cl =
      (identityPregeometry M).cl := by
    funext A
    exact (Lemmatheca.Entry.DefinableAndAlgebraicClosure.infinite_equality_closures A).2
  cases h₁ : aclPregeometry Language.empty.infiniteTheory equality_stronglyMinimalTheory (M := M) with
  | mk cl₁ _ _ _ _ _ =>
    cases h₂ : identityPregeometry M with
    | mk cl₂ _ _ _ _ _ =>
      simp only [h₁, h₂] at hcl
      cases hcl
      rfl

def evenBase : Set ℕ := Set.range (fun n : ℕ => 2 * n)

theorem evenBase_cardinal : Cardinal.mk evenBase = Cardinal.aleph0 := by
  rw [evenBase, Cardinal.mk_range_eq _ (by
    intro m n h
    change 2 * m = 2 * n at h
    omega), Cardinal.mk_nat]

theorem nat_relative_even :
    (identityPregeometry ℕ).relativeDimension evenBase Set.univ = Cardinal.aleph0 := by
  rw [identity_relativeDimension]
  let f : ℕ → (Set.univ \ evenBase : Set ℕ) := fun n => ⟨2 * n + 1, by
    refine ⟨Set.mem_univ _, ?_⟩
    rintro ⟨k, hk⟩
    change 2 * k = 2 * n + 1 at hk
    omega⟩
  have hf : Function.Injective f := by
    intro m n h
    have he := congrArg Subtype.val h
    dsimp [f] at he
    omega
  apply le_antisymm
  · exact Cardinal.mk_le_aleph0
  · simpa using Cardinal.mk_le_of_injective hf

theorem nat_relative_all :
    (identityPregeometry ℕ).relativeDimension Set.univ Set.univ = 0 := by
  exact ((identityPregeometry ℕ).relativeDimension_eq_zero_iff _ _).mpr Set.Subset.rfl

theorem nat_absolute_dimension :
    (identityPregeometry ℕ).dimension Set.univ = Cardinal.aleph0 := by
  rw [identity_dimension]
  simp


end
end Lemmatheca.Entry.PregeometryDimension
