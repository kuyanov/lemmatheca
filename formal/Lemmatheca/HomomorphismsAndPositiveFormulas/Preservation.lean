import Lemmatheca.HomomorphismsAndPositiveFormulas.PositiveDiagrams

/-! The classical homomorphism preservation converse for nonempty structures. -/
namespace Lemmatheca.ModelTheory.PositiveHomomorphisms
open FirstOrder FirstOrder.Language

universe u v w w'
variable {L : Language.{u, v}}

/-- Impose the original sentence and forbid every positive sentence false in this target. -/
def avoidanceTheory (σ : L.Sentence) (B : Type w) [L.Structure B] : L.Theory :=
  {σ} ∪ {γ | ∃ θ : L.Sentence, IsExistentialPositive θ ∧ ¬B ⊨ θ ∧ γ = θ.not}

theorem avoidanceTheory_satisfiable (σ : L.Sentence) (B : Type w)
    [L.Structure B] [Nonempty B] (hB : B ⊨ positiveConsequences σ) :
    (avoidanceTheory σ B).IsSatisfiable := by

  classical
  apply Theory.isSatisfiable_iff_isFinitelySatisfiable.mpr
  intro Γ hΓ
  by_contra hunsat
  let bad : L.Theory :=
    {γ | ∃ θ : L.Sentence, IsExistentialPositive θ ∧ ¬B ⊨ θ ∧ γ = θ.not}
  let D := Γ.filter (· ∈ bad)
  have hd (γ : D) : ∃ θ : L.Sentence,
      IsExistentialPositive θ ∧ ¬B ⊨ θ ∧ γ.val = θ.not :=
    (Finset.mem_filter.mp γ.prop).2
  let pick (γ : D) : L.Sentence := Classical.choose (hd γ)
  have hpick (γ : D) := Classical.choose_spec (hd γ)
  let s : List L.Sentence := D.attach.toList.map pick
  have hs (θ : L.Sentence) (hθ : θ ∈ s) : IsExistentialPositive θ ∧ ¬B ⊨ θ := by
    obtain ⟨γ, _, rfl⟩ := List.mem_map.mp hθ
    exact ⟨(hpick γ).1, (hpick γ).2.1⟩
  let δ : L.Sentence := s.foldr (· ⊔ ·) ⊥
  have hδ : IsExistentialPositive δ := positive_finite_disjunction s (fun θ hθ => (hs θ hθ).1)
  have himp : ({σ} : L.Theory) ⊨ᵇ δ := by
    apply Theory.models_sentence_iff.mpr
    intro A
    by_contra hnot
    have hnot_each (θ : L.Sentence) (hθ : θ ∈ s) : ¬A ⊨ θ := by
      intro ht
      apply hnot
      exact (BoundedFormula.realize_foldr_sup s default default).mpr ⟨θ, hθ, ht⟩
    have hmodel : A ⊨ (↑Γ : L.Theory) := by
      constructor
      intro γ hγ
      rcases hΓ hγ with hσ | hbad
      · obtain rfl := Set.mem_singleton_iff.mp hσ
        exact A.is_model.realize_of_mem _ rfl
      · have hγD : γ ∈ D := Finset.mem_filter.mpr ⟨hγ, hbad⟩
        let d : D := ⟨γ, hγD⟩
        have hmem : pick d ∈ s := List.mem_map.mpr ⟨d, by simp, rfl⟩
        change A ⊨ d.val
        rw [(hpick d).2.2]
        exact hnot_each (pick d) hmem
    let := hmodel
    exact hunsat (Theory.Model.isSatisfiable A)
  have hBδ := hB.realize_of_mem δ ⟨hδ, himp⟩
  obtain ⟨θ, hθ, ht⟩ := (BoundedFormula.realize_foldr_sup s default default).mp hBδ
  exact (hs θ hθ).2 ht

/-- The chosen avoiding model is the very source where the original sentence holds. -/
theorem avoidanceTheory_model {σ : L.Sentence} {A : Type w} {B : Type w'}
    [L.Structure A] [L.Structure B] (hA : A ⊨ avoidanceTheory σ B) :
    A ⊨ σ ∧ positiveTheory (L := L) A ⊆ positiveTheory (L := L) B := by

  refine ⟨hA.realize_of_mem σ (Or.inl rfl), ?_⟩
  intro θ hθ
  refine ⟨hθ.1, ?_⟩
  by_contra hn
  exact (hA.realize_of_mem θ.not (Or.inr ⟨θ, hθ.1, hn, rfl⟩)) hθ.2

private theorem homPreserved_base {σ : L.Sentence} (h : HomPreserved.{u, v, w} σ) :
    HomPreserved.{u, v, 0} σ := by
  intro M N f hM
  let M' : Theory.ModelType.{u, v, max u v w} (∅ : L.Theory) := M.ulift
  let N' : Theory.ModelType.{u, v, max u v w} (∅ : L.Theory) := N.ulift
  let eM : M ≃[L] M' := (Equiv.ulift.symm : M ≃ M').inducedStructureEquiv
  let eN : N ≃[L] N' := (Equiv.ulift.symm : N ≃ N').inducedStructureEquiv
  let f' : M' →[L] N' := eN.toHom.comp (f.comp eM.symm.toHom)
  have hM' := (eM.toElementaryEmbedding.map_sentence σ).mp hM
  exact (eN.toElementaryEmbedding.map_sentence σ).mpr (h M' N' f' hM')


theorem positiveConsequences_entail {σ : L.Sentence} (h : HomPreserved.{u, v, w} σ) :
    positiveConsequences σ ⊨ᵇ σ := by

  apply Theory.models_sentence_iff.mpr
  intro B
  obtain ⟨A⟩ := avoidanceTheory_satisfiable σ B B.is_model
  obtain ⟨hA, hpos⟩ := avoidanceTheory_model A.is_model
  obtain ⟨C, sC, hne, hj, hg⟩ := positiveTheory_subset_iff.mp hpos
  let := sC
  let := hne
  obtain ⟨j⟩ := hj
  obtain ⟨g⟩ := hg
  have hC := homPreserved_base h (Theory.ModelType.of (∅ : L.Theory) A)
    (Theory.ModelType.of (∅ : L.Theory) C) g hA
  exact (j.map_sentence σ).mpr hC

/-- The equivalent formula is the actual conjunction of finitely selected positive consequences. -/
theorem finite_positive_equivalent {σ : L.Sentence} (h : HomPreserved.{u, v, w} σ) :
    ∃ s : Finset L.Sentence,
      (↑s : L.Theory) ⊆ positiveConsequences σ ∧
      IsExistentialPositive (s.toList.foldr (· ⊓ ·) ⊤) ∧
      (∅ : L.Theory) ⊨ᵇ (σ.iff (s.toList.foldr (· ⊓ ·) ⊤)) := by

  classical
  obtain ⟨s, hs, hsσ⟩ := Theory.models_iff_finset_models.mp (positiveConsequences_entail h)
  refine ⟨s, hs, positive_finite_conjunction s.toList
    (fun θ hθ => (hs (Finset.mem_toList.mp hθ)).1), ?_⟩
  apply Theory.models_sentence_iff.mpr
  intro M
  rw [Sentence.realize_iff]
  constructor
  · intro hM
    apply (BoundedFormula.realize_foldr_inf s.toList default default).mpr
    intro θ hθ
    let : M ⊨ ({σ} : L.Theory) := ⟨fun γ hγ => (Set.mem_singleton_iff.mp hγ) ▸ hM⟩
    exact (hs (Finset.mem_toList.mp hθ)).2.realize_sentence M
  · intro hM
    have hall := (BoundedFormula.realize_foldr_inf s.toList default default).mp hM
    let : M ⊨ (↑s : L.Theory) :=
      ⟨fun θ hθ => hall θ (Finset.mem_toList.mpr hθ)⟩
    exact hsσ.realize_sentence M

theorem homPreserved_of_positive_equivalent {σ θ : L.Sentence}
    (hθ : IsExistentialPositive θ) (heq : (∅ : L.Theory) ⊨ᵇ (σ.iff θ)) :
    HomPreserved.{u, v, w} σ := by

  intro M N h hM
  have heM := (Sentence.realize_iff M).mp (heq.realize_sentence M)
  have heN := (Sentence.realize_iff N).mp (heq.realize_sentence N)
  apply heN.mpr
  have ht := hom_preserves_positive h hθ (default : Empty → M) default (heM.mp hM)
  simpa only [Sentence.Realize, Formula.Realize, Unique.eq_default] using ht

theorem homPreserved_iff_positive_equivalent (σ : L.Sentence) :
    HomPreserved.{u, v, w} σ ↔
      ∃ θ : L.Sentence, IsExistentialPositive θ ∧ (∅ : L.Theory) ⊨ᵇ (σ.iff θ) := by

  constructor
  · intro h
    obtain ⟨s, _, hp, he⟩ := finite_positive_equivalent h
    exact ⟨s.toList.foldr (· ⊓ ·) ⊤, hp, he⟩
  · rintro ⟨θ, hp, he⟩
    exact homPreserved_of_positive_equivalent hp he

end Lemmatheca.ModelTheory.PositiveHomomorphisms
