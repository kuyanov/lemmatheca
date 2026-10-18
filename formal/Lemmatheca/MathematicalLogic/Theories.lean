import Lemmatheca.MathematicalLogic.HenkinCompleteness
import Lemmatheca.MathematicalLogic.Compactness

/-! Consequence closure and finite axiomatizability of classes of structures. -/
namespace Lemmatheca.MathematicalLogic.Theories
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic.FirstOrderProofs
universe u v
variable {L : Language.{u, v}}
noncomputable section

/-- The semantic presentation of deductive closure; the equivalence with the
corpus proof calculus is supplied below for countable signatures. -/
def consequenceClosure (T : L.Theory) : L.Theory := {φ | T ⊨ᵇ φ}

theorem mem_closure_iff_derives [Countable L.Symbols] (T : L.Theory) (φ : L.Sentence) :
    φ ∈ consequenceClosure T ↔ Derives T φ :=
  HenkinCompleteness.consequence_iff_derives

theorem subset_closure (T : L.Theory) : T ⊆ consequenceClosure T :=
  fun _ h => Theory.models_sentence_of_mem h

theorem model_closure (T : L.Theory) (M : Type*) [L.Structure M] [Nonempty M] :
    M ⊨ consequenceClosure T ↔ M ⊨ T := by
  constructor
  · intro h
    exact h.mono (subset_closure T)
  · intro h
    let := h
    exact ⟨fun _ hφ => hφ.realize_sentence M⟩

theorem closure_idempotent (T : L.Theory) :
    consequenceClosure (consequenceClosure T) = consequenceClosure T := by
  apply Set.Subset.antisymm
  · intro φ hφ
    apply Theory.models_sentence_iff.mpr
    intro M
    let := (model_closure T M).mpr M.is_model
    exact hφ.realize_sentence M
  · exact subset_closure _

/-- A fixed universe of nonempty structures, without additional axioms. -/
abbrev Structures (L : Language.{u, v}) := Theory.ModelType.{u, v, max u v} (∅ : L.Theory)

/-- A class of structures in the same fixed signature. -/
abbrev StructureClass (L : Language.{u, v}) := Set (Structures L)

/-- The class of models of an axiom set. -/
def modelClass (T : L.Theory) : StructureClass L := {M | M ⊨ T}

/-- Equivalent axiom sets describe the same structures. -/
def Equivalent (T U : L.Theory) : Prop := modelClass T = modelClass U

theorem equivalent_iff_closure_eq (T U : L.Theory) :
    Equivalent T U ↔ consequenceClosure T = consequenceClosure U := by
  constructor
  · intro h
    ext φ
    constructor
    · intro hφ
      apply Theory.models_sentence_iff.mpr
      intro M
      let A : Structures L := Theory.ModelType.of _ M
      have hAT : A ⊨ T := by
        have hAU : A ∈ modelClass U := M.is_model
        rwa [← h] at hAU
      let := hAT
      exact hφ.realize_sentence A
    · intro hφ
      apply Theory.models_sentence_iff.mpr
      intro M
      let A : Structures L := Theory.ModelType.of _ M
      have hAU : A ⊨ U := by
        have hAT : A ∈ modelClass T := M.is_model
        rwa [h] at hAT
      let := hAU
      exact hφ.realize_sentence A
  · intro h
    ext M
    change M ⊨ T ↔ M ⊨ U
    rw [← model_closure T M, h, model_closure U M]

/-- A theory is deductively closed when it already contains its consequences. -/
def IsDeductivelyClosed (T : L.Theory) : Prop := consequenceClosure T = T

theorem complete_iff_consistent_decides [Countable L.Symbols] (T : L.Theory) :
    T.IsComplete ↔ Consistent T ∧ ∀ φ : L.Sentence, Derives T φ ∨ Derives T φ.not := by
  constructor
  · intro h
    refine ⟨theory_consistent_of_model h.1.some.is_model, ?_⟩
    intro φ
    exact (h.2 φ).imp HenkinCompleteness.deductive_completeness
      HenkinCompleteness.deductive_completeness
  · rintro ⟨hcon, hdec⟩
    obtain ⟨M, hM, hne, _, hT⟩ := HenkinCompleteness.countable_model_existence hcon
    let := hM
    let := hne
    let := hT
    refine ⟨Theory.Model.isSatisfiable M, ?_⟩
    intro φ
    exact (hdec φ).imp HenkinCompleteness.consequence_iff_derives.mpr
      HenkinCompleteness.consequence_iff_derives.mpr

theorem completeTheory_closed (M : Type*) [L.Structure M] [Nonempty M] :
    IsDeductivelyClosed (L.completeTheory M) := by
  apply Set.Subset.antisymm
  · exact fun _ h => h.realize_sentence M
  · exact subset_closure _

/-- A class is axiomatizable by a possibly infinite set of sentences. -/
def IsAxiomatizable (C : StructureClass L) : Prop := ∃ T : L.Theory, C = modelClass T

/-- A finite list of sentences axiomatizes the class. -/
def IsFinitelyAxiomatizable (C : StructureClass L) : Prop :=
  ∃ Γ : Finset L.Sentence, C = modelClass (↑Γ : L.Theory)

/-- An empty conjunction is truth. -/
def finiteConjunction (Γ : Finset L.Sentence) : L.Sentence :=
  Γ.toList.foldr (· ⊓ ·) ⊤

theorem realize_finiteConjunction (Γ : Finset L.Sentence) (M : Type*) [L.Structure M] :
    M ⊨ finiteConjunction Γ ↔ M ⊨ (↑Γ : L.Theory) := by
  simp only [finiteConjunction, Sentence.Realize, Formula.Realize,
    BoundedFormula.realize_foldr_inf, Theory.model_iff, Finset.mem_toList,
    Finset.mem_coe]

theorem finitely_iff_single_sentence (C : StructureClass L) :
    IsFinitelyAxiomatizable C ↔ ∃ φ : L.Sentence, C = modelClass {φ} := by
  constructor
  · rintro ⟨Γ, rfl⟩
    refine ⟨finiteConjunction Γ, ?_⟩
    ext M
    exact (realize_finiteConjunction Γ M).symm.trans Theory.model_singleton_iff.symm
  · rintro ⟨φ, rfl⟩
    exact ⟨{φ}, by simp⟩

theorem finite_axiomatizability_iff_complement (C : StructureClass L) :
    IsFinitelyAxiomatizable C ↔ IsAxiomatizable C ∧ IsAxiomatizable Cᶜ := by
  classical
  constructor
  · intro h
    obtain ⟨φ, rfl⟩ := (finitely_iff_single_sentence C).mp h
    refine ⟨⟨{φ}, rfl⟩, ⟨{φ.not}, ?_⟩⟩
    ext M
    simp only [Set.mem_compl_iff, modelClass, Set.mem_ofPred_eq,
      Theory.model_singleton_iff, Sentence.realize_not]
  · rintro ⟨⟨T, hT⟩, ⟨U, hU⟩⟩
    have hno : ¬ (T ∪ U).IsSatisfiable := by
      rintro ⟨M⟩
      let A : Structures L := Theory.ModelType.of _ M
      have hAT : A ∈ modelClass T := M.is_model.mono Set.subset_union_left
      have hAU : A ∈ modelClass U := M.is_model.mono Set.subset_union_right
      rw [← hT] at hAT
      rw [← hU] at hAU
      exact hAU hAT
    rw [Theory.isSatisfiable_iff_isFinitelySatisfiable] at hno
    obtain ⟨Γ, hΓ⟩ := not_forall.mp hno
    have hsub : (↑Γ : L.Theory) ⊆ T ∪ U := (not_imp.mp hΓ).1
    have hunsat : ¬ Theory.IsSatisfiable (↑Γ : L.Theory) := (not_imp.mp hΓ).2
    let ΓT := Γ.filter (· ∈ T)
    refine ⟨ΓT, ?_⟩
    ext M
    constructor
    · intro hMC
      have hMT : M ⊨ T := by
        change M ∈ modelClass T
        rwa [← hT]
      exact hMT.mono (by intro φ hφ; exact (Finset.mem_filter.mp hφ).2)
    · intro hMΓT
      by_contra hnC
      have hMU : M ⊨ U := by
        change M ∈ modelClass U
        rwa [← hU]
      let : M ⊨ (↑Γ : L.Theory) := by
        constructor
        intro φ hφ
        rcases hsub hφ with hφT | hφU
        · exact hMΓT.realize_of_mem φ (Finset.mem_filter.mpr ⟨hφ, hφT⟩)
        · exact hMU.realize_of_mem φ hφU
      exact hunsat (Theory.Model.isSatisfiable M)

theorem infinitude_not_finitely_axiomatizable (L : Language.{u, v}) :
    ¬ IsFinitelyAxiomatizable (modelClass L.infiniteTheory) := by
  intro h
  obtain ⟨T, hT⟩ := ((finite_axiomatizability_iff_complement _).mp h).2
  apply Compactness.finitude_not_axiomatizable L
  refine ⟨T, ?_⟩
  intro M hM hne
  let := hM
  let := hne
  let A : Structures L := Theory.ModelType.of _ M
  have h : A ⊨ T ↔ ¬ A ⊨ L.infiniteTheory := by
    change A ∈ modelClass T ↔ A ∈ (modelClass L.infiniteTheory)ᶜ
    rw [← hT]
  rw [L.model_infiniteTheory_iff] at h
  exact h.trans not_infinite_iff_finite

theorem countable_same_theory [Countable L.Symbols]
    (M : Type*) [L.Structure M] [Nonempty M] :
    ∃ N : Theory.ModelType.{u, v, max u v} (L.completeTheory M),
      Countable N ∧ ElementarilyEquivalent L M N := by
  have hcon : Consistent (L.completeTheory M) := theory_consistent_of_model (M := M) inferInstance
  obtain ⟨N, hN, hne, hc, hmodel⟩ := HenkinCompleteness.countable_model_existence hcon
  let := hN
  let := hne
  let := hmodel
  refine ⟨Theory.ModelType.of _ N, hc, ?_⟩
  exact Theory.IsComplete.models_elementarily_equivalent (completeTheory.isComplete L M) M N

theorem empty_equality_theory_incomplete :
    ¬ (∅ : Language.empty.Theory).IsComplete := by
  intro h
  let : Language.empty.Structure Unit := Compactness.constantStructure _ _
  let : Language.empty.Structure Bool := Compactness.constantStructure _ _
  have heq := h.models_elementarily_equivalent Unit Bool
  have hsentence := (elementarilyEquivalent_iff.mp heq) (Sentence.cardGe Language.empty 2)
  simp only [Sentence.realize_cardGe] at hsentence
  simp at hsentence

end
end Lemmatheca.MathematicalLogic.Theories
