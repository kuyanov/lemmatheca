import Lemmatheca.IntuitionisticPropositionalTreeCountermodels.Paths

namespace Lemmatheca.ProofTheory.Intuitionistic.Kripke.StrictPaths

open Lemmatheca.MathematicalLogic.Propositional

universe u v
variable {α : Type u} {W : Type v} [PartialOrder W]

/-- The established pullback along the actual endpoint function. -/
def model (M : Model α W) (r : W) : Model α (Path r) :=
  pullback M last (last_monotone r)

theorem last_morphism (M : Model α W) (r : W) :
    IsBoundedMorphism (model M r) M (last : Path r → W) := by
  exact pullback_boundedMorphism M last (last_bounded r)

/-- A generated cone is the precise target in this surjectivity statement. -/
theorem generated_last_surjective (r : W) :
    Function.Surjective
      (last : Path (⟨r, le_rfl⟩ : {x : W // r ≤ x}) → {x : W // r ≤ x}) := by
  apply (last_surjective_iff (⟨r, le_rfl⟩ : {x : W // r ≤ x})).mpr
  intro x
  exact x.property

/-- The literal composite reads the original endpoint of this generated-cone path. -/
theorem generated_endpoint_morphism (M : Model α W) (r : W) :
    IsBoundedMorphism
      (model (generated M r) (⟨r, le_rfl⟩ : {x : W // r ≤ x})) M
      ((Subtype.val : {x : W // r ≤ x} → W) ∘ last) := by
  exact boundedMorphism_composition _ _ _ _ _
    (last_morphism (generated M r) (⟨r, le_rfl⟩ : {x : W // r ≤ x}))
    (generated_inclusion_boundedMorphism M r)

end Lemmatheca.ProofTheory.Intuitionistic.Kripke.StrictPaths
