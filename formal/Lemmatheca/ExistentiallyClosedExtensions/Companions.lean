import Lemmatheca.ExistentiallyClosedExtensions.Constructions

/-! The companion criterion keeps the original model condition explicit. -/
namespace Lemmatheca.ModelTheory.ExistentiallyClosedExtensions
open FirstOrder FirstOrder.Language
open Lemmatheca.ModelTheory
open ModelCompleteness InductiveTheories ModelCompanions
universe u v w
variable {L : Language.{u, v}}

/-- A theory describes the whole class, including the original theory's model condition. -/
def AxiomatizesEC (T U : L.Theory) : Prop :=
  ∀ M : Theory.ModelType.{u, v, max u v w} (∅ : L.Theory), M ⊨ U ↔ IsEC.{u, v, w} T M

/-- Elementary means axiomatizable in the original language, with no completeness condition. -/
def ElementaryECClass (T : L.Theory) : Prop := ∃ U : L.Theory, AxiomatizesEC.{u, v, w} T U

/-- A companion's models are first shown to satisfy the original inductive theory. -/
theorem companion_models_isEC (T U : L.Theory) (hT : IsInductive.{u, v, w} T)
    (hU : ModelCompanion.{u, v, w} T U)
    (M : Theory.ModelType.{u, v, max u v w} U) :
    IsEC.{u, v, w} T (Theory.ModelType.of ∅ M) := by
  obtain ⟨N, ⟨f⟩⟩ := hU.1.2 M
  obtain ⟨P, ⟨g⟩⟩ := hU.1.1 N
  have hcomp := modelComplete_implies_closed hU.2 M P (g.comp f)
  have hf := reflection_of_composite f g hcomp
  have hMT := reflecting_model_status T hT (Theory.ModelType.of ∅ M) N f hf
  refine ⟨hMT, ?_⟩
  intro N' f'
  obtain ⟨P', ⟨g'⟩⟩ := hU.1.1 N'
  exact reflection_of_composite f' g' (modelComplete_implies_closed hU.2 M P' (g'.comp f'))

/-- No containment between the original axiom sets is assumed. -/
theorem ec_models_companion (T U : L.Theory)
    (hU : ModelCompanion.{u, v, w} T U)
    (M : Theory.ModelType.{u, v, max u v w} (∅ : L.Theory))
    (hM : IsEC.{u, v, w} T M) : M ⊨ U := by
  let := hM.1
  obtain ⟨N, ⟨f⟩⟩ := hU.1.1 (Theory.ModelType.of T M)
  obtain ⟨P, ⟨g⟩⟩ := hU.1.2 N
  have hcomp := hM.2 P (g.comp f)
  have hf := reflection_of_composite f g hcomp
  exact reflecting_model_status U (modelComplete_inductive U hU.2).1 M N f hf

/-- Existence of closed extensions and Robinson's test give the reverse direction. -/
theorem axiomatizesEC_is_modelCompanion (T U : L.Theory)
    (hT : IsInductive.{u, v, w} T) (hU : AxiomatizesEC.{u, v, w} T U) :
    ModelCompanion.{u, v, w} T U := by
  refine ⟨⟨?_, ?_⟩, (modelComplete_iff_allClosed U).mpr ?_⟩
  · intro M
    obtain ⟨D,hD,_hcard⟩ := exists_closed_extension T hT M
    let N := D.limitModel hT
    have hEC : IsEC T (Theory.ModelType.of ∅ N) :=
      (isEC_iff_existing T N).mpr hD
    have hNU : N ⊨ U := (hU (Theory.ModelType.of ∅ N)).mpr hEC
    let := hNU
    exact ⟨Theory.ModelType.of U N, ⟨D.initialMap⟩⟩
  · intro M
    have hEC := (hU (Theory.ModelType.of ∅ M)).mp M.is_model
    let : M ⊨ T := hEC.1
    exact ⟨Theory.ModelType.of T M, ⟨Embedding.refl L M⟩⟩
  · intro M N f
    have hM := (hU (Theory.ModelType.of ∅ M)).mp M.is_model
    have hN := (hU (Theory.ModelType.of ∅ N)).mp N.is_model
    let : N ⊨ T := hN.1
    exact hM.2 (Theory.ModelType.of T N) f

/-- The precise criterion applies also to inconsistent theories. -/
theorem modelCompanion_iff_axiomatizesEC (T U : L.Theory) (hT : IsInductive.{u, v, w} T) :
    ModelCompanion.{u, v, w} T U ↔ AxiomatizesEC.{u, v, w} T U := by
  constructor
  · intro hU M
    constructor
    · intro hM
      let := hM
      exact companion_models_isEC T U hT hU (Theory.ModelType.of U M)
    · exact ec_models_companion T U hU M
  · exact axiomatizesEC_is_modelCompanion T U hT

/-- Quantifying the preceding exact class characterization gives the existence criterion. -/
theorem exists_modelCompanion_iff_elementary (T : L.Theory) (hT : IsInductive.{u, v, w} T) :
    (∃ U : L.Theory, ModelCompanion.{u, v, w} T U) ↔ ElementaryECClass.{u, v, w} T := by
  exact exists_congr (fun U => modelCompanion_iff_axiomatizesEC T U hT)

end Lemmatheca.ModelTheory.ExistentiallyClosedExtensions
