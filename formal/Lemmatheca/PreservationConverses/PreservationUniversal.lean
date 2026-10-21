import Lemmatheca.PreservationConverses.PreservationDiagrams

open Lemmatheca.MathematicalLogic

/-! Preservation results in the shared first-order syntax. -/
namespace Lemmatheca.ModelTheory.Preservation
open FirstOrder FirstOrder.Language
open Lemmatheca.ModelTheory.Theories
universe u v w
variable {L : Language.{u, v}}

private theorem unnamed_qf {α : Type*} {γ : L[[α]].Sentence} (h : γ.IsQF) :
    (Formula.equivSentence.symm γ).IsQF := by
  induction h with
  | falsum => exact .falsum
  | of_isAtomic h =>
    cases h with
    | equal => exact (BoundedFormula.IsAtomic.equal _ _).isQF
    | rel => exact (BoundedFormula.IsAtomic.rel _ _).isQF
  | imp _ _ ih ih' => exact ih.imp ih'

private theorem qf_restrict {α β : Type*} [DecidableEq α] {k : ℕ}
    {φ : L.BoundedFormula α k} (h : φ.IsQF) :
    ∀ f : φ.freeVarFinset → β, (φ.restrictFreeVar f).IsQF := by
  induction h with
  | falsum => exact fun _ => .falsum
  | of_isAtomic h =>
    cases h with
    | equal => exact fun _ => (BoundedFormula.IsAtomic.equal _ _).isQF
    | rel => exact fun _ => (BoundedFormula.IsAtomic.rel _ _).isQF
  | imp _ _ ih ih' => exact fun f => (ih _).imp (ih' _)

private theorem existential_exs {α : Type*} {k : ℕ} {φ : L.BoundedFormula α k}
    (h : φ.IsExistential) : φ.exs.IsExistential := by
  induction k with
  | zero => exact h
  | succ k ih => exact ih h.ex

private theorem qf_exClosure {α : Type*} [DecidableEq α] {φ : L.Formula α}
    (h : φ.IsQF) : φ.exClosure.IsExistential := by
  unfold Formula.exClosure Formula.iExs
  exact existential_exs (((qf_restrict h id).relabel _).relabel _).isExistential

private theorem qf_finiteConjunction {α : Type*} (Γ : Finset (L[[α]].Sentence))
    (h : ∀ γ ∈ Γ, γ.IsQF) : (finiteConjunction Γ).IsQF := by
  unfold finiteConjunction
  have hh : ∀ γ ∈ Γ.toList, γ.IsQF := fun γ hγ => h γ (Finset.mem_toList.mp hγ)
  generalize Γ.toList = s at *
  induction s with
  | nil => exact BoundedFormula.IsQF.top
  | cons γ s ih => exact (hh _ (by simp)).inf (ih (fun δ hδ => hh δ (by simp [hδ])))

/-- Every model satisfies all universal consequences of its theory. -/
theorem model_universalPart (T : L.Theory) (M : Type w) [L.Structure M]
    [Nonempty M] [M ⊨ T] : M ⊨ universalPart T := by
  exact ⟨fun _ hσ => hσ.2.realize_sentence M⟩

/-- A model of the universal part embeds into a genuine model of the original theory. -/
theorem model_universalPart_iff_embeds (T : L.Theory) (M : Type w) [L.Structure M]
    [Nonempty M] :
    M ⊨ universalPart T ↔
      ∃ (N : Type (max u v w)) (_ : L.Structure N) (_ : Nonempty N),
        (N ⊨ T) ∧ Nonempty (M ↪[L] N) := by
  classical
  constructor
  · intro hM
    let D := Diagrams.quantifierFreeDiagram L M
    let E := (L.lhomWithConstants M).onTheory T
    have hsat : (E ∪ D).IsSatisfiable := by
      apply Theory.isSatisfiable_iff_isFinitelySatisfiable.mpr
      intro Γ hΓ
      by_contra hno
      let Δ := Γ.filter (fun γ => γ ∈ D)
      let γ := finiteConjunction Δ
      let φ := Formula.equivSentence.symm γ
      have hγq : γ.IsQF := qf_finiteConjunction Δ
        (fun δ hδ => (Finset.mem_filter.mp hδ).2.1)
      have hγM : M ⊨ γ := (realize_finiteConjunction Δ M).mpr
        ⟨fun δ hδ => (Finset.mem_filter.mp hδ).2.2⟩
      have hχ : φ.exClosure.IsExistential := qf_exClosure (unnamed_qf hγq)
      obtain ⟨σ, hσ, he⟩ := exists_universal_not.{u, v, max u v, 0} hχ
      have heq : (∅ : L.Theory) ⊨ᵇ (σ.iff φ.exClosure.not) := by
        intro B v xs
        simpa only [BoundedFormula.realize_iff, BoundedFormula.realize_not] using he B v xs
      have hTσ : T ⊨ᵇ σ := by
        apply Theory.models_sentence_iff.mpr
        intro B
        have heB : (B ⊨ σ) ↔ ¬ (B ⊨ φ.exClosure) := by
          simpa only [Sentence.realize_iff, Sentence.realize_not] using heq.realize_sentence B
        apply heB.mpr
        intro hB
        obtain ⟨f, hf⟩ := Formula.exists_realize_equivSentence_iff_realize_exClosure.mpr hB
        let : L[[M]].Structure B := Diagrams.namedExpansion (L := L) f
        let : (L.lhomWithConstants M).IsExpansionOn B :=
          Diagrams.namedExpansion_isExpansion f
        have hBγ : B ⊨ γ := by
          simpa only [φ, Equiv.apply_symm_apply] using hf
        have hBD : B ⊨ (↑Δ : L[[M]].Theory) :=
          (realize_finiteConjunction Δ B).mp hBγ
        let : B ⊨ (↑Γ : L[[M]].Theory) := by
          constructor
          intro δ hδ
          rcases hΓ hδ with hE | hD
          · obtain ⟨θ, hθ, rfl⟩ := hE
            exact (LHom.realize_onSentence B _ θ).mpr (B.is_model.realize_of_mem θ hθ)
          · exact hBD.realize_of_mem δ (Finset.mem_filter.mpr ⟨hδ, hD⟩)
        exact hno (Theory.Model.isSatisfiable B)
      have hMσ := hM.realize_of_mem σ ⟨hσ, hTσ⟩
      have hMχ : M ⊨ φ.exClosure :=
        Formula.realize_exClosure_of_realize_equivSentence (by
          simpa only [φ, Equiv.apply_symm_apply] using hγM)
      have heM : (M ⊨ σ) ↔ ¬ (M ⊨ φ.exClosure) := by
        simpa only [Sentence.realize_iff, Sentence.realize_not] using heq.realize_sentence M
      exact heM.mp hMσ hMχ
    let N := hsat.some
    let : L.Structure N := (L.lhomWithConstants M).reduct N
    let : (L.lhomWithConstants M).IsExpansionOn N := LHom.isExpansionOn_reduct _ _
    have hND : N ⊨ D := N.is_model.mono Set.subset_union_right
    obtain ⟨f, _⟩ := Diagrams.model_signed_iff_canonical_embedding.mp
      (Diagrams.models_signed_iff_models_quantifierFree.mpr hND)
    have hNE : N ⊨ E := N.is_model.mono Set.subset_union_left
    exact ⟨N, inferInstance, inferInstance, (LHom.onTheory_model _ _).mp hNE, ⟨f⟩⟩
  · rintro ⟨N, sN, hne, hNT, ⟨f⟩⟩
    let := sN
    let := hne
    let := hNT
    have : (universalPart T).IsUniversal := ⟨fun _ hσ => hσ.1⟩
    let : N ⊨ universalPart T := model_universalPart T N
    exact Theory.IsUniversal.models_of_embedding f

/-- The equivalent universal axiom set is the particular universal part of the theory. -/
theorem universalPart_equivalent (T : L.Theory) (hT : SubstructurePreserved.{u, v, w} T) :
    (universalPart T).IsUniversal ∧ Theories.Equivalent T (universalPart T) := by
  classical
  refine ⟨⟨fun _ hσ => hσ.1⟩, ?_⟩
  ext M
  change M ⊨ T ↔ M ⊨ universalPart T
  constructor
  · intro hm
    let := hm
    exact model_universalPart T M
  · intro hm
    let := hm
    let A := Theory.ModelType.ulift.{u, v, max u v, w}
      (Theory.ModelType.of (universalPart T) M)
    obtain ⟨N, sN, hne, hNT, ⟨f⟩⟩ := (model_universalPart_iff_embeds T A).mp A.is_model
    let := sN
    let := hne
    have hAT : A ⊨ T := hT (Theory.ModelType.of ∅ A) (Theory.ModelType.of ∅ N) hNT f
    let e : M ≃[L] A := (Equiv.ulift.{w}.symm).inducedStructureEquiv
    let := hAT
    exact StrongHomClass.theory_model (T := T) e.symm

/-- The result is polymorphic in an ambient universe containing the language and models. -/
theorem substructure_preserved_iff_universal (T : L.Theory) :
    SubstructurePreserved.{u, v, w} T ↔ HasUniversalAxiomatization T := by
  constructor
  · intro hT
    exact ⟨universalPart T, universalPart_equivalent T hT⟩
  · rintro ⟨U, hU, heq⟩
    intro M N hNT f
    have hc := equivalent_iff_closure_eq T U |>.mp heq
    have eq_models (A : Type (max u v w)) [L.Structure A] [Nonempty A] : A ⊨ T ↔ A ⊨ U := by
      rw [← model_closure T A, hc, model_closure U A]
    let : N ⊨ U := (eq_models N).mp hNT
    let := hU
    exact (eq_models M).mpr (Theory.IsUniversal.models_of_embedding f)

end Lemmatheca.ModelTheory.Preservation
