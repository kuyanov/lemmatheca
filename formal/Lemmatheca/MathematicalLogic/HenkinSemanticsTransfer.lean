import Lemmatheca.MathematicalLogic.HenkinSemanticsCore
import Lemmatheca.MathematicalLogic.HenkinCompleteness

namespace Lemmatheca.MathematicalLogic.HenkinSemantics
open FirstOrder FirstOrder.Language
noncomputable section
universe u v w w'
variable {L : Language.{u,v}}

private theorem presentation_modelsTheory {M : Type w} {U : Type w'}
    [L.Structure M] [(applicationLanguage L).Structure U] [Nonempty M]
    {D : SecondOrderLogic.RelationDomains M} (P : Presentation (L:=L) (U:=U) D)
    (hD : ∀ n, (D n).Nonempty) (T : Theory L) :
    U ⊨ translateTheory T ↔
      ∀ φ ∈ T, ∀ a r, (∀ n X, r n X ∈ D n) →
        SecondOrderLogic.realize D a r φ.val := by
  rw [FirstOrder.Language.Theory.model_iff]
  constructor
  · intro h φ hφ
    exact (P.sentence_realize hD φ).mp (h _ (Or.inr ⟨φ,hφ,rfl⟩))
  · intro h φ hφ
    rcases hφ with hb | ⟨ψ,hψ,rfl⟩
    · have hB : U ⊨ backgroundTheory L := background_model_iff.mpr (P.admissible hD)
      exact hB.realize_of_mem φ hb
    · exact (P.sentence_realize hD ψ).mpr (h ψ hψ)

private def decodedGeneralModel {U : Type (max u v)}
    [(applicationLanguage L).Structure U] (h : Admissible (L:=L) (U:=U)) :
    GeneralModel L where
  Carrier := DecodedIndividual L U
  str := decodedStructure h
  nonempty := (decoded_nonempty h).1
  domains := decodedDomains (L:=L) (U:=U)
  domains_nonempty := (decoded_nonempty h).2

theorem satisfiable_iff (T : Theory L) :
    Satisfiable T ↔ (translateTheory T).IsSatisfiable := by
  constructor
  · rintro ⟨H,hH⟩
    let _ := forwardStructure (L:=L) H.domains
    obtain ⟨P,_⟩ := exists_forward_presentation (L:=L) H.domains
    have hm : ForwardCarrier H.domains ⊨ translateTheory T :=
      (presentation_modelsTheory P H.domains_nonempty T).mpr hH
    let _ := hm
    exact FirstOrder.Language.Theory.Model.isSatisfiable (ForwardCarrier H.domains)
  · intro h
    let B := h.some
    have hb : Admissible (L:=L) (U:=B) := background_model_iff.mp
      (B.is_model.mono Set.subset_union_left)
    let H := decodedGeneralModel hb
    have P : @Presentation L H.Carrier B H.str B.struc H.domains :=
      decodedPresentation hb
    refine ⟨H,?_⟩
    exact (presentation_modelsTheory P H.domains_nonempty T).mp B.is_model

theorem consequence_iff (T : Theory L) (φ : Sentence L) :
    Models T φ ↔ (translateTheory T) ⊨ᵇ translateSentence φ := by
  constructor
  · intro h
    apply FirstOrder.Language.Theory.models_sentence_iff.mpr
    intro B
    have hb : Admissible (L:=L) (U:=B) := background_model_iff.mp
      (B.is_model.mono Set.subset_union_left)
    let H := decodedGeneralModel hb
    have P : @Presentation L H.Carrier B H.str B.struc H.domains :=
      decodedPresentation hb
    have hH := (presentation_modelsTheory P H.domains_nonempty T).mp B.is_model
    exact (P.sentence_realize H.domains_nonempty φ).mpr (h H hH)
  · intro h H hH
    let _ := forwardStructure (L:=L) H.domains
    obtain ⟨P,_⟩ := exists_forward_presentation (L:=L) H.domains
    have hm : ForwardCarrier H.domains ⊨ translateTheory T :=
      (presentation_modelsTheory P H.domains_nonempty T).mpr hH
    let _ := hm
    exact (P.sentence_realize H.domains_nonempty φ).mp
      (h.realize_sentence (ForwardCarrier H.domains))

private def applicationRelationFromCode :
    (Σ n, L.Relations n) ⊕ (Unit ⊕ (ℕ ⊕ ℕ)) → (Σ n, ApplicationRelation L n)
  | .inl ⟨n,R⟩ => ⟨n,.original R⟩
  | .inr (.inl _) => ⟨1,.individual⟩
  | .inr (.inr (.inl n)) => ⟨1,.relationSort n⟩
  | .inr (.inr (.inr n)) => ⟨n+1,.application n⟩

theorem countable_application_symbols [Countable L.Symbols] :
    Countable (applicationLanguage L).Symbols := by
  let _ : Countable (Σ n, L.Relations n) :=
    Function.Injective.countable (f := (Sum.inr :
      (Σ n, L.Relations n) → L.Symbols)) Sum.inr_injective
  have hsurj : Function.Surjective (applicationRelationFromCode (L:=L)) := by
    rintro ⟨n,R⟩
    cases R with
    | original R => exact ⟨.inl ⟨_,R⟩,rfl⟩
    | individual => exact ⟨.inr (.inl ()),rfl⟩
    | relationSort n => exact ⟨.inr (.inr (.inl n)),rfl⟩
    | application n => exact ⟨.inr (.inr (.inr n)),rfl⟩
  let _ : Countable (Σ n, ApplicationRelation L n) := hsurj.countable
  change Countable ((Σ n, L.Functions n) ⊕ (Σ n, ApplicationRelation L n))
  infer_instance

theorem completeness [Countable L.Symbols] (T : Theory L) (φ : Sentence L) :
    Models T φ ↔ Derives T φ := by
  let _ := countable_application_symbols (L:=L)
  exact (consequence_iff T φ).trans HenkinCompleteness.consequence_iff_derives

theorem compactness (T : Theory L) :
    Satisfiable T ↔ ∀ F : Finset (Sentence L), (↑F : Theory L) ⊆ T →
      Satisfiable (↑F : Theory L) := by
  classical
  constructor
  · rintro ⟨H,hH⟩ F hF
    exact ⟨H,fun φ hφ => hH φ (hF hφ)⟩
  · intro h
    rw [satisfiable_iff, FirstOrder.Language.Theory.isSatisfiable_iff_isFinitelySatisfiable]
    intro F hF
    let chooseOriginal (φ : (applicationLanguage L).Sentence) : Finset (Sentence L) :=
      if hφ : ∃ ψ ∈ T, translateSentence ψ = φ then {hφ.choose} else ∅
    let T₀ := F.biUnion chooseOriginal
    have hT₀ : (T₀ : Theory L) ⊆ T := by
      intro ψ hψ
      obtain ⟨φ,hφ,hψ⟩ := Finset.mem_biUnion.mp hψ
      by_cases he : ∃ ψ ∈ T, translateSentence ψ = φ
      · dsimp only [chooseOriginal] at hψ
        rw [dite_eq_left he] at hψ
        exact (Finset.mem_singleton.mp hψ) ▸ he.choose_spec.1
      · dsimp only [chooseOriginal] at hψ
        rw [dite_eq_right he] at hψ
        exact (Finset.notMem_empty _ hψ).elim
    have hm := (satisfiable_iff _).mp (h T₀ hT₀)
    apply hm.mono
    intro φ hφ
    rcases hF hφ with hb | ⟨ψ,hψ,he⟩
    · exact Or.inl hb
    · have hex : ∃ ψ ∈ T, translateSentence ψ = φ := ⟨ψ,hψ,he⟩
      apply Or.inr
      refine ⟨hex.choose,?_,hex.choose_spec.2⟩
      refine Finset.mem_biUnion.mpr ⟨φ,hφ,?_⟩
      dsimp only [chooseOriginal]
      rw [dite_eq_left hex]
      exact Finset.mem_singleton_self _

theorem compactness_with_scheme (T C : Theory L)
    (h : ∀ F : Finset (Sentence L), (↑F : Theory L) ⊆ T →
      Satisfiable ((↑F : Theory L) ∪ C)) :
    Satisfiable (T ∪ C) := by
  classical
  apply (compactness (T ∪ C)).mpr
  intro F hF
  let F₀ := F.filter (· ∈ T)
  have hF₀ : (F₀ : Theory L) ⊆ T := by
    intro φ hφ
    exact (Finset.mem_filter.mp hφ).2
  obtain ⟨H,hH⟩ := h F₀ hF₀
  refine ⟨H,fun φ hφ => ?_⟩
  rcases hF hφ with ht | hc
  · exact hH φ (Or.inl (Finset.mem_filter.mpr ⟨hφ,ht⟩))
  · exact hH φ (Or.inr hc)

end
end Lemmatheca.MathematicalLogic.HenkinSemantics
