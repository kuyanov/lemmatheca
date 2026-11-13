import Lemmatheca.StronglyMinimalModelsAndDimension.Cardinality
import Lemmatheca.PregeometryDimension.Examples

namespace Lemmatheca.Entry.StronglyMinimalModelsAndDimension
open FirstOrder FirstOrder.Language Cardinal
open Lemmatheca.ModelTheory
open StronglyMinimalSets StronglyMinimalModelsAndDimension
open Lemmatheca.Entry.StronglyMinimalSets
universe w
noncomputable section
variable {M : Type w} [Language.empty.Structure M] [Infinite M]

theorem equality_basis_iff (B : Set M) :
    ModelBasis Language.empty.infiniteTheory equality_stronglyMinimalTheory B ↔ B = Set.univ := by
  change (aclPregeometry Language.empty.infiniteTheory equality_stronglyMinimalTheory (M := M)).IsBasis B Set.univ ↔ _
  rw [Lemmatheca.Entry.PregeometryDimension.equality_acl_identity]
  exact Pregeometry.identity_basis_iff B Set.univ

theorem equality_model_dimension :
    modelDimension Language.empty.infiniteTheory equality_stronglyMinimalTheory M = #M := by
  unfold modelDimension
  rw [Lemmatheca.Entry.PregeometryDimension.equality_acl_identity, Pregeometry.identity_dimension,
    Cardinal.mk_univ]

theorem equality_no_finite_dimension (n : ℕ) :
    modelDimension Language.empty.infiniteTheory equality_stronglyMinimalTheory M ≠ (n : Cardinal) := by
  rw [equality_model_dimension]
  exact ne_of_gt ((Cardinal.natCast_lt_aleph0 (n := n)).trans_le (Cardinal.aleph0_le_mk M))

omit [Language.empty.Structure M] [Infinite M] in
theorem equality_all_infinite_dimensions (κ : Cardinal.{w}) (hκ : ℵ₀ ≤ κ) :
    ∃ P : Language.empty.infiniteTheory.ModelType.{0,0,w},
      modelDimension Language.empty.infiniteTheory equality_stronglyMinimalTheory P = κ := by
  have hinfinite : ∃ P : Language.empty.infiniteTheory.ModelType.{0,0,0}, Infinite P :=
    ⟨Cardinal.empty_infinite_Theory_isComplete.1.some,
      (equality_stronglyMinimalTheory Cardinal.empty_infinite_Theory_isComplete.1.some).1⟩
  obtain ⟨P, hP⟩ := Theory.exists_model_card_eq hinfinite κ hκ (by simp)
  let : Infinite P := (Language.empty.model_infiniteTheory_iff).mp P.is_model
  exact ⟨P, (equality_model_dimension (M := P)).trans hP⟩

end
end Lemmatheca.Entry.StronglyMinimalModelsAndDimension
