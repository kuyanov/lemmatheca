import Lemmatheca.HomomorphismsAndPositiveFormulas.PositiveFormulas

/-! Finite positive diagram patterns and their canonical maps. -/
namespace Lemmatheca.ModelTheory.PositiveHomomorphisms
open FirstOrder FirstOrder.Language
open Lemmatheca.ModelTheory

universe u v w w' w''
variable {L : Language.{u, v}} {A : Type w} {B : Type w'}
variable [L.Structure A] [L.Structure B]

theorem positiveDiagram_function_fact {n : ℕ} (f : L.Functions n) (a : Fin n → A) :
    ((Term.func (Sum.inl f) fun i => Constants.term (L.con (a i))).equal
      (Constants.term (L.con (Structure.funMap f a)))) ∈ Diagrams.positiveDiagram L A := by
  refine ⟨.equal _ _, ?_⟩
  rfl

theorem positiveDiagram_relation_fact {n : ℕ} (R : L.Relations n) (a : Fin n → A)
    (ha : Structure.RelMap R a) :
    Relations.formula (L := L[[A]]) (Sum.inl R) (fun i => Constants.term (L.con (a i))) ∈
      Diagrams.positiveDiagram L A := by
  exact ⟨.rel _ _, ha⟩

theorem model_positive_iff_canonical_hom [L[[A]].Structure B]
    [(L.lhomWithConstants A).IsExpansionOn B] :
    B ⊨ Diagrams.positiveDiagram L A ↔
      ∃ h : A →[L] B, (h : A → B) = Diagrams.canonicalMap L A B := by
  constructor
  · intro hB
    refine ⟨⟨Diagrams.canonicalMap L A B, ?_, ?_⟩, rfl⟩
    · intro n f a
      have hf := hB.realize_of_mem _ (positiveDiagram_function_fact f a)
      have hf' := (Formula.realize_equal).mp hf
      dsimp only [Term.realize] at hf'
      simpa only [Term.realize_constants, Language.withConstants_funMap_sumInl,
        Diagrams.canonicalMap, Function.comp_def] using hf'.symm
    · intro n R a ha
      have hr := hB.realize_of_mem _ (positiveDiagram_relation_fact R a ha)
      simpa only [Sentence.Realize, Formula.Realize, Relations.formula,
        Relations.boundedFormula, BoundedFormula.Realize, Term.realize_relabel,
        Term.realize_constants, Language.withConstants_relMap_sumInl,
        Diagrams.canonicalMap, Function.comp_def] using hr
  · rintro ⟨h, he⟩
    constructor
    intro γ hγ
    let φ : L.Formula A := Formula.equivSentence.symm γ
    have hφ : φ.IsAtomic := by
      cases hγ.1 <;> constructor
    have hA := (Formula.realize_equivSentence_symm_con A γ).mpr hγ.2
    have hB := Diagrams.hom_preserves_atomic h hφ id default hA
    apply (Formula.realize_equivSentence_symm_con B γ).mp
    change φ.Realize (Diagrams.canonicalMap L A B)
    simpa only [Formula.Realize, Unique.eq_default, Function.comp_id, he] using hB

theorem namedExpansion_models_positive_iff (f : A → B) :
    (letI := Diagrams.namedExpansion (L := L) f;
      B ⊨ Diagrams.positiveDiagram L A) ↔
      ∃ h : A →[L] B, (h : A → B) = f := by
  let : L[[A]].Structure B := Diagrams.namedExpansion (L := L) f
  let : (L.lhomWithConstants A).IsExpansionOn B :=
    Diagrams.namedExpansion_isExpansion f
  exact model_positive_iff_canonical_hom

/-- The actual finite conjunction, with the added constant names made into free variables. -/
noncomputable def diagramConjunction (Δ : Finset L[[A]].Sentence) : L.Formula A := by
  classical
  exact Δ.toList.foldr (fun γ φ => Formula.equivSentence.symm γ ⊓ φ) ⊤

/-- One position for each distinct added name that occurs in the conjunction. -/
noncomputable def patternArity (Δ : Finset L[[A]].Sentence) : ℕ := by
  classical
  exact Fintype.card (diagramConjunction Δ).freeVarFinset

/-- The actual source tuple listing those distinct names. -/
noncomputable def patternTuple (Δ : Finset L[[A]].Sentence) : Fin (patternArity (L := L) Δ) → A := by
  classical
  exact fun i => ((Fintype.equivFin (diagramConjunction Δ).freeVarFinset).symm i).val

/-- Remove unused variable names and use the finite position list, leaving all original symbols. -/
noncomputable def diagramPattern (Δ : Finset L[[A]].Sentence) :
    L.Formula (Fin (patternArity (L := L) Δ)) := by
  classical
  exact (diagramConjunction Δ).restrictFreeVar
    (Fintype.equivFin (diagramConjunction Δ).freeVarFinset)

omit [L.Structure A] in
/-- Truth of this exact conjunction agrees with the specified interpretation of all names. -/
theorem diagramPattern_realize [_sourceStructure : L.Structure A] (Δ : Finset L[[A]].Sentence) (f : A → B) :
    (diagramPattern Δ).Realize (f ∘ patternTuple (L := L) Δ) ↔
      (letI := Diagrams.namedExpansion (L := L) f;
        B ⊨ (↑Δ : L[[A]].Theory)) := by
  classical
  let : L[[A]].Structure B := Diagrams.namedExpansion (L := L) f
  let : (L.lhomWithConstants A).IsExpansionOn B :=
    Diagrams.namedExpansion_isExpansion f
  have hr : (diagramPattern Δ).Realize (f ∘ patternTuple (L := L) Δ) ↔
      (diagramConjunction Δ).Realize f := by
    unfold diagramPattern patternTuple patternArity
    apply BoundedFormula.realize_restrictFreeVar f
    intro a
    simp
  rw [hr]
  have fold_truth : ∀ s : List L[[A]].Sentence,
      (s.foldr (fun γ φ => Formula.equivSentence.symm γ ⊓ φ) ⊤).Realize f ↔
        ∀ γ ∈ s, B ⊨ γ := by
    intro s
    induction s with
    | nil => simp
    | cons γ s ih =>
      simp only [List.foldr_cons, Formula.realize_inf, ih, List.mem_cons,
        forall_eq_or_imp]
      exact and_congr (Formula.realize_equivSentence_symm_con B γ) Iff.rfl
  rw [diagramConjunction, fold_truth]
  constructor
  · exact fun h => ⟨fun γ hγ => h γ (Finset.mem_toList.mpr hγ)⟩
  · exact fun h γ hγ => h.realize_of_mem γ (Finset.mem_toList.mp hγ)

private theorem restricted_atomicConjunction {α β : Type*} [DecidableEq α] {n : ℕ} {φ : L.BoundedFormula α n}
    (hφ : IsAtomicConjunction φ) :
    ∀ f : φ.freeVarFinset → β, IsAtomicConjunction (φ.restrictFreeVar f) := by
  classical
  induction hφ with
  | atomic h =>
    intro f
    cases h <;> apply IsAtomicConjunction.atomic <;> constructor
  | top => intro f; exact .top
  | inf _ _ ih ih' =>
    intro f
    apply IsAtomicConjunction.inf
    · exact ih _
    · exact ih' _


/-- The finite witness sentence is fixed before the target structure is selected. -/
theorem finite_positive_pattern [Nonempty A] (Δ : Finset L[[A]].Sentence)
    (hΔ : (↑Δ : L[[A]].Theory) ⊆ Diagrams.positiveDiagram L A) :
    IsAtomicConjunction (diagramPattern Δ) ∧
      (diagramPattern Δ).IsQF ∧
      IsExistentialPositive (existentialClosure (diagramPattern Δ)) ∧
      (diagramPattern Δ).Realize (patternTuple (L := L) Δ) ∧
      ∀ (N : Type w'') [L.Structure N] [Nonempty N],
        (N ⊨ existentialClosure (diagramPattern Δ) ↔
          ∃ f : A → N, letI := Diagrams.namedExpansion (L := L) f;
            N ⊨ (↑Δ : L[[A]].Theory)) := by
  classical
  have hatom : ∀ γ ∈ Δ.toList, (Formula.equivSentence.symm γ).IsAtomic := by
    intro γ hγ
    have h := (hΔ (Finset.mem_toList.mp hγ)).1
    cases h <;> constructor
  have hconj : IsAtomicConjunction (diagramConjunction Δ) := by
    unfold diagramConjunction
    generalize Δ.toList = s at hatom ⊢
    induction s with
    | nil => exact .top
    | cons γ s ih =>
      exact .inf (.atomic (hatom γ (by simp)))
        (ih (fun δ hδ => hatom δ (by simp [hδ])))
  have hpat : IsAtomicConjunction (diagramPattern Δ) :=
    restricted_atomicConjunction hconj _
  have htrue : (diagramPattern Δ).Realize (patternTuple (L := L) Δ) := by
    apply (diagramPattern_realize Δ (id : A → A)).mpr
    exact ⟨fun γ hγ => (hΔ hγ).2⟩
  refine ⟨hpat, atomicConjunction_quantifierFree hpat,
    existentialClosure_positive (atomicConjunction_positive hpat), htrue, ?_⟩
  intro N _ _
  rw [existentialClosure_realize]
  constructor
  · rintro ⟨b, hb⟩
    let e : (diagramConjunction Δ).freeVarFinset ≃ Fin (patternArity (L := L) Δ) :=
      Fintype.equivFin _
    let f : A → N := fun a => if ha : a ∈ (diagramConjunction Δ).freeVarFinset
      then b (e ⟨a, ha⟩) else Classical.choice inferInstance
    refine ⟨f, (diagramPattern_realize Δ f).mp ?_⟩
    have hfb : f ∘ patternTuple (L := L) Δ = b := by
      funext i
      simp [f, patternTuple, e]
      exact congrArg b ((Fintype.equivFin _).apply_symm_apply i)
    simpa only [hfb] using hb
  · rintro ⟨f, hf⟩
    exact ⟨f ∘ patternTuple (L := L) Δ, (diagramPattern_realize Δ f).mpr hf⟩

/-- Disjoint tags for the positive source names and elementary target names. -/
def mixedTheory (L : Language.{u, v}) (A : Type w) (B : Type w')
    [L.Structure A] [L.Structure B] : L[[A ⊕ B]].Theory :=
  (L.lhomWithConstantsMap (Sum.inl : A → A ⊕ B)).onTheory (Diagrams.positiveDiagram L A) ∪
    (L.lhomWithConstantsMap (Sum.inr : B → A ⊕ B)).onTheory (L.elementaryDiagram B)

/-- A finite mixed fragment is realized on the original target carrier with its own names fixed. -/
theorem mixedTheory_finite_realization [Nonempty A] [Nonempty B]
    (h : positiveTheory (L := L) A ⊆ positiveTheory (L := L) B) (Δ : Finset L[[A ⊕ B]].Sentence)
    (hΔ : (↑Δ : L[[A ⊕ B]].Theory) ⊆ mixedTheory L A B) :
    ∃ f : A → B,
      letI := Diagrams.namedExpansion (L := L) (Sum.elim f id : A ⊕ B → B)
      B ⊨ (↑Δ : L[[A ⊕ B]].Theory) := by

  classical
  let kA := L.lhomWithConstantsMap (Sum.inl : A → A ⊕ B)
  let kB := L.lhomWithConstantsMap (Sum.inr : B → A ⊕ B)
  let D := Δ.filter (· ∈ kA.onTheory (Diagrams.positiveDiagram L A))
  have hd (γ : D) : ∃ φ ∈ Diagrams.positiveDiagram L A, kA.onSentence φ = γ.val :=
    (Finset.mem_filter.mp γ.prop).2
  let pick (γ : D) : L[[A]].Sentence := Classical.choose (hd γ)
  have hpick (γ : D) := Classical.choose_spec (hd γ)
  let P : Finset L[[A]].Sentence := D.attach.image pick
  have hP : (↑P : L[[A]].Theory) ⊆ Diagrams.positiveDiagram L A := by
    intro φ hφ
    obtain ⟨γ, _, rfl⟩ := Finset.mem_image.mp hφ
    exact (hpick γ).1
  obtain ⟨_, _, hpos, htrue, hpattern⟩ := finite_positive_pattern P hP
  have hA : A ⊨ existentialClosure (diagramPattern P) :=
    (existentialClosure_realize _).mpr ⟨patternTuple (L := L) P, htrue⟩
  have hB := (h ⟨hpos, hA⟩).2
  obtain ⟨f, hf⟩ := (hpattern B).mp hB
  refine ⟨f, ?_⟩
  let : L[[A ⊕ B]].Structure B :=
    Diagrams.namedExpansion (L := L) (Sum.elim f id : A ⊕ B → B)
  let : L[[A]].Structure B := Diagrams.namedExpansion (L := L) f
  let : kA.IsExpansionOn B := by
    constructor
    · intro n g xs
      cases g with
      | inl g => rfl
      | inr g =>
        cases n with
        | zero => rfl
        | succ n => exact g.elim
    · intro n R xs
      cases R with
      | inl R => rfl
      | inr R => exact R.elim
  let : L[[B]].Structure B := Diagrams.namedExpansion (L := L) (id : B → B)
  let : kB.IsExpansionOn B := by
    constructor
    · intro n g xs
      cases g with
      | inl g => rfl
      | inr g =>
        cases n with
        | zero => rfl
        | succ n => exact g.elim
    · intro n R xs
      cases R with
      | inl R => rfl
      | inr R => exact R.elim
  constructor
  intro γ hγ
  by_cases ha : γ ∈ kA.onTheory (Diagrams.positiveDiagram L A)
  · have hγD : γ ∈ D := Finset.mem_filter.mpr ⟨hγ, ha⟩
    let d : D := ⟨γ, hγD⟩
    have hmem : pick d ∈ P := Finset.mem_image.mpr ⟨d, by simp, rfl⟩
    have hφ := hf.realize_of_mem (pick d) hmem
    have ht := (LHom.realize_onSentence B kA (pick d)).mpr hφ
    change B ⊨ d.val
    rw [← (hpick d).2]
    exact ht
  · obtain ⟨φ, hφ, heq⟩ := (hΔ hγ).resolve_left ha
    rw [← heq]
    exact (LHom.realize_onSentence B kB φ).mpr hφ

theorem mixedTheory_satisfiable [Nonempty A] [Nonempty B]
    (h : positiveTheory (L := L) A ⊆ positiveTheory (L := L) B) :
    (mixedTheory L A B).IsSatisfiable := by

  apply Theory.isSatisfiable_iff_isFinitelySatisfiable.mpr
  intro Δ hΔ
  obtain ⟨f, hf⟩ := mixedTheory_finite_realization h Δ hΔ
  let : L[[A ⊕ B]].Structure B :=
    Diagrams.namedExpansion (L := L) (Sum.elim f id : A ⊕ B → B)
  let := hf
  exact Theory.Model.isSatisfiable B

/-- A model of the union supplies the maps determined by its two actual name families. -/
theorem mixedTheory_canonical_maps {C : Type w''} [L[[A ⊕ B]].Structure C] :
    letI : L.Structure C := (L.lhomWithConstants (A ⊕ B)).reduct C
    C ⊨ mixedTheory L A B →
      (∃ g : A →[L] C, ∀ a, g a = (L.con (Sum.inl a : A ⊕ B) : C)) ∧
      (∃ j : B ↪ₑ[L] C, ∀ b, j b = (L.con (Sum.inr b : A ⊕ B) : C)) := by

  let : L.Structure C := (L.lhomWithConstants (A ⊕ B)).reduct C
  intro hC
  let kA := L.lhomWithConstantsMap (Sum.inl : A → A ⊕ B)
  let : L[[A]].Structure C := kA.reduct C
  let : (L.lhomWithConstants A).IsExpansionOn C :=
    ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  have hA : C ⊨ Diagrams.positiveDiagram L A :=
    (LHom.onTheory_model kA _).mp (hC.mono Set.subset_union_left)
  obtain ⟨g, hg⟩ := model_positive_iff_canonical_hom.mp hA
  let kB := L.lhomWithConstantsMap (Sum.inr : B → A ⊕ B)
  let : L[[B]].Structure C := kB.reduct C
  let : (L.lhomWithConstants B).IsExpansionOn C :=
    ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  have hB : C ⊨ L.elementaryDiagram B :=
    (LHom.onTheory_model kB _).mp (hC.mono Set.subset_union_right)
  obtain ⟨j, hj⟩ := Diagrams.model_elementary_iff_canonical_elementary.mp hB
  exact ⟨⟨g, fun a => congrFun hg a⟩, ⟨j, fun b => congrFun hj b⟩⟩

/-- Positive information transfers exactly when the source maps into an elementary target extension. -/
theorem positiveTheory_subset_iff [Nonempty A] [Nonempty B] :
    positiveTheory (L := L) A ⊆ positiveTheory (L := L) B ↔
      ∃ (C : Type (max u v w w')) (_ : L.Structure C), Nonempty C ∧
        Nonempty (B ↪ₑ[L] C) ∧ Nonempty (A →[L] C) := by

  constructor
  · intro h
    let C := (mixedTheory_satisfiable h).some
    let : L.Structure C := (L.lhomWithConstants (A ⊕ B)).reduct C
    obtain ⟨⟨g, _⟩, ⟨j, _⟩⟩ := mixedTheory_canonical_maps C.is_model
    exact ⟨C, inferInstance, inferInstance, ⟨j⟩, ⟨g⟩⟩
  · rintro ⟨C, sC, hne, ⟨j⟩, ⟨g⟩⟩
    let := sC
    let := hne
    intro σ hσ
    refine ⟨hσ.1, ?_⟩
    have ht := hom_preserves_positive g hσ.1 (default : Empty → A) default hσ.2
    have hC : C ⊨ σ := by
      simpa only [Sentence.Realize, Formula.Realize, Unique.eq_default] using ht
    exact (j.map_sentence σ).mpr hC

end Lemmatheca.ModelTheory.PositiveHomomorphisms
