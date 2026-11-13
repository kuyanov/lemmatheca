import Lemmatheca.StronglyMinimalModelsAndDimension.Classification
import Lemmatheca.StronglyMinimalTypes.Bounds

namespace Lemmatheca.ModelTheory.StronglyMinimalModelsAndDimension
open FirstOrder FirstOrder.Language Cardinal
open StronglyMinimalSets Closures
universe u v w
noncomputable section
local instance smdCardinalityPropDecidable : DecidablePred (fun p : Prop => p) := Classical.propDecidable
variable {L : Language.{u,v}} (T : L.Theory) (hT : T.IsComplete)
variable (hSM : StronglyMinimalTheory T)

/-- The common-universe language threshold; it does not depend on the model's size. -/
def languageBound : Cardinal.{max u v w} := max (Cardinal.lift.{w} L.card) ℵ₀

variable {M : Type w} [L.Structure M] [Nonempty M] [M ⊨ T]

omit hT in
theorem model_size_bound (B : Set M) (hB : ModelBasis T hSM B) :
    Cardinal.lift.{max u v} #M ≤
      max (Cardinal.lift.{max u v} #B) (languageBound (L := L)) := by
  have hspan := ((model_basis_iff T hSM B).mp hB).2
  have hb := StronglyMinimalTypes.acl_cardinal_bound (L := L) B
  rw [hspan, Cardinal.mk_univ] at hb
  simpa only [StronglyMinimalTypes.syntaxBound, languageBound, max_assoc, max_left_comm, max_comm] using hb

omit hT in
theorem large_model_dimension
    (hlarge : languageBound (L := L) < Cardinal.lift.{max u v} #M) :
    modelDimension T hSM M = #M := by
  obtain ⟨B, hB⟩ := exists_model_basis T hSM (M := M)
  rw [basis_dimension T hSM B hB]
  apply Cardinal.lift_injective.{max u v}
  apply le_antisymm
  · exact Cardinal.lift_le.mpr (Cardinal.mk_subtype_le B)
  · have hb := model_size_bound T hSM B hB
    exact (le_max_iff.mp hb).resolve_right (not_le_of_gt hlarge)

include hT hSM in
omit [L.Structure M] [Nonempty M] [M ⊨ T] in
theorem models_at_large_cardinal (κ : Cardinal.{w})
    (hκ : languageBound (L := L) < Cardinal.lift.{max u v} κ) :
    ∃ P : T.ModelType.{u,v,w}, #P = κ := by
  have hinfinite : ∃ P : T.ModelType.{u,v,max u v}, Infinite P :=
    ⟨hT.1.some, (hSM hT.1.some).1⟩
  apply Theory.exists_model_card_eq hinfinite κ
  · exact Cardinal.aleph0_le_lift.mp ((le_max_right _ _).trans hκ.le)
  · exact (le_max_left _ _).trans hκ.le

include hT hSM in
omit [L.Structure M] [Nonempty M] [M ⊨ T] in
theorem categorical_above_language (κ : Cardinal.{w})
    (hκ : languageBound (L := L) < Cardinal.lift.{max u v} κ) :
    κ.Categorical T := by
  intro P Q hP hQ
  apply (isomorphic_iff_dimension T hT hSM).mpr
  rw [large_model_dimension T hSM (M := P) (by rwa [hP]),
    large_model_dimension T hSM (M := Q) (by rwa [hQ]), hP, hQ]

include hT hSM in
omit [L.Structure M] [Nonempty M] [M ⊨ T] in
theorem unique_large_cardinal (κ : Cardinal.{w})
    (hκ : languageBound (L := L) < Cardinal.lift.{max u v} κ) :
    (∃ P : T.ModelType.{u,v,w}, #P = κ) ∧ κ.Categorical T := by
  exact ⟨models_at_large_cardinal T hT hSM κ hκ, categorical_above_language T hT hSM κ hκ⟩

omit T hT hSM [L.Structure M] [Nonempty M] [M ⊨ T] in
theorem countable_language_bound [Countable L.Symbols] :
    languageBound.{u,v,w} (L := L) = ℵ₀ := by
  apply max_eq_right
  exact Cardinal.lift_le_aleph0.mpr (Cardinal.mk_le_aleph0 (α := L.Symbols))

include hT hSM in
omit [L.Structure M] [Nonempty M] [M ⊨ T] in
theorem countable_uncountable_categorical [Countable L.Symbols] (κ : Cardinal.{w})
    (hκ : ℵ₀ < κ) :
    (∃ P : T.ModelType.{u,v,w}, #P = κ) ∧ κ.Categorical T := by
  apply unique_large_cardinal T hT hSM κ
  rw [countable_language_bound]
  simpa only [Cardinal.lift_aleph0] using (Cardinal.lift_lt.{w, max u v}.mpr hκ)

end
end Lemmatheca.ModelTheory.StronglyMinimalModelsAndDimension

