import Lemmatheca.JointConsistency.JointConsistency

namespace Lemmatheca.MathematicalLogic.CraigInterpolation
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic.FirstOrderProofs
open Lemmatheca.MathematicalLogic.ChangingLanguages
open Lemmatheca.MathematicalLogic.JointConsistency
universe u v w
variable {L : Language.{u,v}}
noncomputable section
local instance {α : Type*} : DecidableEq α := Classical.decEq _

/-- The two consequences and exact syntactic common-vocabulary condition. -/
def SentenceInterpolant (φ ψ θ : L.Sentence) : Prop :=
  (({φ} : L.Theory) ⊨ᵇ θ) ∧ (({θ} : L.Theory) ⊨ᵇ ψ) ∧
    formulaSymbols θ ⊆ formulaSymbols φ ∩ formulaSymbols ψ

private theorem included_term_symbols_aux (S : Finset L.Symbols) {α : Type w}
    (t : (supportedLanguage S).Term α) : termSymbols ((supportInclusion S).onTerm t) ⊆ S := by
  induction t with
  | var a => simp [LHom.onTerm,termSymbols]
  | func f ts ih =>
    intro x hx
    simp only [LHom.onTerm,termSymbols,Finset.mem_insert,Finset.mem_biUnion,
      Finset.mem_univ,true_and] at hx
    rcases hx with rfl | ⟨i,hi⟩
    · exact f.property
    · exact ih i hi

theorem included_formula_symbols (S : Finset L.Symbols) {α : Type w} {n : ℕ}
    (A : (supportedLanguage S).BoundedFormula α n) :
    formulaSymbols ((supportInclusion S).onBoundedFormula A) ⊆ S := by
  induction A with
  | falsum => simp [LHom.onBoundedFormula,formulaSymbols]
  | equal t₁ t₂ =>
    intro x hx
    simp only [LHom.onBoundedFormula,Term.bdEqual,formulaSymbols,Finset.mem_union] at hx
    exact hx.elim (fun ht => included_term_symbols_aux S t₁ ht) (fun ht => included_term_symbols_aux S t₂ ht)
  | rel R ts =>
    intro x hx
    simp only [LHom.onBoundedFormula,Relations.boundedFormula,formulaSymbols,Finset.mem_insert,Finset.mem_biUnion,
      Finset.mem_univ,true_and] at hx
    rcases hx with rfl | ⟨i,hi⟩
    · exact R.property
    · exact included_term_symbols_aux S (ts i) hi
  | imp A B ihA ihB =>
    intro x hx
    simp only [LHom.onBoundedFormula,formulaSymbols,Finset.mem_union] at hx
    exact hx.elim (fun ht => ihA ht) (fun ht => ihB ht)
  | all A ih => exact ih


/-- Craig's interpolant is an actual sentence of the exact intersection language. -/
theorem sentence_interpolation (φ ψ : L.Sentence) (h : ({φ} : L.Theory) ⊨ᵇ ψ) :
    ∃ η : (supportedLanguage (formulaSymbols φ ∩ formulaSymbols ψ)).Sentence,
      SentenceInterpolant φ ψ
        ((supportInclusion (formulaSymbols φ ∩ formulaSymbols ψ)).onSentence η) := by
  let S := formulaSymbols φ
  let T := formulaSymbols ψ
  let φ₁ := restrictFormula S φ (Finset.Subset.refl _)
  let ψ₂ := restrictFormula T ψ (Finset.Subset.refl _)
  have hφ : (supportInclusion S).onSentence φ₁ = φ := include_restrictFormula S φ _
  have hψ : (supportInclusion T).onSentence ψ₂ = ψ := include_restrictFormula T ψ _
  have hnegψ : (supportInclusion T).onSentence ψ₂.not = ψ.not := by
    change ((supportInclusion T).onSentence ψ₂).not = ψ.not
    rw [hψ]
  have hnot : ¬Inseparable (commonLeft S T) (commonRight S T) {φ₁} {ψ₂.not} := by
    intro hi
    have hs := (joint_model_iff S T {φ₁} {ψ₂.not}).mpr hi
    apply (Theory.models_iff_not_satisfiable ψ).mp h
    simpa only [LHom.onTheory,Set.image_singleton,hφ,hnegψ] using hs
  obtain ⟨η,hη₁,hη₂⟩ := Classical.not_not.mp hnot
  let θ := (supportInclusion (S ∩ T)).onSentence η
  have hcomp₁ : (supportInclusion S).onSentence ((commonLeft S T).onSentence η) = θ :=
    (congrFun (LHom.comp_onBoundedFormula (supportInclusion S) (commonLeft S T)) η).symm
  have hcomp₂ : (supportInclusion T).onSentence ((commonRight S T).onSentence η) = θ :=
    (congrFun (LHom.comp_onBoundedFormula (supportInclusion T) (commonRight S T)) η).symm
  have hnegη : (supportInclusion T).onSentence
      ((commonRight S T).onSentence η).not = θ.not := by
    change ((supportInclusion T).onSentence ((commonRight S T).onSentence η)).not = θ.not
    rw [hcomp₂]
  have hfirst : Derives {φ} θ := by
    have ht := derives_map (supportInclusion S) hη₁
    simpa only [LHom.onTheory,Set.image_singleton,hφ,hcomp₁] using ht
  have hsecond : Derives {ψ.not} θ.not := by
    have ht := derives_map (supportInclusion T) hη₂
    simpa only [LHom.onTheory,Set.image_singleton,hnegψ,hnegη] using ht
  refine ⟨η,(consequence_iff_derives).mpr hfirst,?_,included_formula_symbols (S ∩ T) η⟩
  apply Theory.models_sentence_iff.mpr
  intro M
  have hθ : M ⊨ θ := Theory.realize_sentence_of_mem ({θ} : L.Theory) (by simp)
  by_contra hnψ
  have hnθ := derives_sound hsecond (default : Empty → M) (by
    intro A hA
    rw [Set.mem_singleton_iff.mp hA]
    exact hnψ)
  exact hnθ hθ

theorem deductive_interpolation (φ ψ : L.Sentence) (h : Derives {φ} ψ) :
    ∃ θ : L.Sentence,
      formulaSymbols θ ⊆ formulaSymbols φ ∩ formulaSymbols ψ ∧
        Derives {φ} θ ∧ Derives {θ} ψ := by
  obtain ⟨η,hfirst,hsecond,hs⟩ := sentence_interpolation φ ψ (consequence_iff_derives.mpr h)
  exact ⟨_,hs,deductive_completeness hfirst,deductive_completeness hsecond⟩

theorem derives_factor (φ ψ θ : L.Sentence)
    (h₁ : Derives {φ} θ) (h₂ : Derives {θ} ψ) : Derives {φ} ψ := by
  apply deductive_completeness
  apply Theory.models_sentence_iff.mpr
  intro M
  have hφ : M ⊨ φ := Theory.realize_sentence_of_mem ({φ} : L.Theory) (by simp)
  have hθ := derives_sound h₁ (default : Empty → M) (by
    intro A hA
    rw [Set.mem_singleton_iff.mp hA]
    exact hφ)
  exact derives_sound h₂ (default : Empty → M) (by
    intro A hA
    rw [Set.mem_singleton_iff.mp hA]
    exact hθ)

theorem bot_interpolant (φ ψ : L.Sentence) (h : ¬({φ} : L.Theory).IsSatisfiable) :
    SentenceInterpolant φ ψ ⊥ := by
  refine ⟨?_,?_,?_⟩
  · apply Theory.models_sentence_iff.mpr
    intro M
    exact False.elim (h (Theory.Model.isSatisfiable M))
  · apply Theory.models_sentence_iff.mpr
    intro M
    have hf : M ⊨ (⊥ : L.Sentence) := Theory.realize_sentence_of_mem ({⊥} : L.Theory) (by simp)
    exact False.elim hf
  · simp [formulaSymbols]

theorem top_interpolant (φ ψ : L.Sentence) (h : (∅ : L.Theory) ⊨ᵇ ψ) :
    SentenceInterpolant φ ψ ⊤ := by
  refine ⟨?_,?_,?_⟩
  · apply Theory.models_sentence_iff.mpr
    intro M
    simp
  · apply Theory.models_sentence_iff.mpr
    intro M
    let : M ⊨ (∅ : L.Theory) := ⟨fun _ hA => False.elim hA⟩
    exact h.realize_sentence M
  · simp [formulaSymbols]
end
end Lemmatheca.MathematicalLogic.CraigInterpolation
