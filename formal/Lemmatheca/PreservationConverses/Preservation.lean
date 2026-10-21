import Lemmatheca.PreservationConverses.PreservationCardinality

open Lemmatheca.MathematicalLogic

/-! The universal and existential preservation converses, in the shared first-order syntax. -/
namespace Lemmatheca.ModelTheory.Preservation
open FirstOrder FirstOrder.Language
open Lemmatheca.ModelTheory.Theories
universe u v w
variable {L : Language.{u, v}}

/-- Existential equivalence gives preservation between models of the background theory. -/
theorem extensionPreserved_of_equivalent {T : L.Theory} {n : ℕ}
    {φ ψ : L.Formula (Fin n)} (hψ : ψ.IsExistential) (heq : T ⊨ᵇ (φ.iff ψ)) :
    ExtensionPreserved.{u, v, w} T φ := by
  intro M N f a ha
  have hM : φ.Realize a ↔ ψ.Realize a := by
    exact (Formula.realize_iff).mp (heq.realize_formula M)
  have hN : φ.Realize (f ∘ a) ↔ ψ.Realize (f ∘ a) := by
    exact (Formula.realize_iff).mp (heq.realize_formula N)
  apply hN.mpr
  have hf := hψ.realize_embedding f (hM.mp ha)
  simpa only [Formula.Realize, Subsingleton.elim (f ∘ (default : Fin 0 → M))
    (default : Fin 0 → N)] using hf

private theorem extensionPreserved_base {T : L.Theory} {n : ℕ}
    {φ : L.Formula (Fin n)} (h : ExtensionPreserved.{u, v, w} T φ) :
    ExtensionPreserved.{u, v, 0} T φ := by
  intro M N f a ha
  let M' : Theory.ModelType.{u, v, max u v w} T := M.ulift
  let N' : Theory.ModelType.{u, v, max u v w} T := N.ulift
  let eM : M ≃[L] M' := (Equiv.ulift.symm : M ≃ M').inducedStructureEquiv
  let eN : N ≃[L] N' := (Equiv.ulift.symm : N ≃ N').inducedStructureEquiv
  let f' : M' ↪[L] N' := eN.toEmbedding.comp (f.comp eM.symm.toEmbedding)
  have ha' : φ.Realize (eM ∘ a) :=
    (eM.toElementaryEmbedding.map_formula φ a).mpr ha
  have hn := h M' N' f' (eM ∘ a) ha'
  apply (eN.toElementaryEmbedding.map_formula φ (f ∘ a)).mp
  convert hn using 1
  funext i
  change eN (f (a i)) = eN (f (eM.symm (eM (a i))))
  simp

/-- Every tuple realizing the existential consequences realizes the preserved formula. -/
theorem existentialConsequences_entail {T : L.Theory} {n : ℕ}
    {φ : L.Formula (Fin n)} (hφ : ExtensionPreserved.{u, v, w} T φ)
    (M : Theory.ModelType.{u, v, max u v w} T) (a : Fin n → M)
    (ha : ∀ ψ ∈ existentialConsequences T φ, ψ.Realize a) : φ.Realize a := by
  classical
  let lhom := L.lhomWithConstants (Fin n)
  let bad : L[[Fin n]].Theory :=
    {γ | ∃ ψ : L.Formula (Fin n), ψ.IsExistential ∧ ¬ψ.Realize a ∧
      γ = Formula.equivSentence ψ.not}
  let U : L[[Fin n]].Theory :=
    (lhom.onTheory T ∪ {Formula.equivSentence φ}) ∪ bad
  have hU : U.IsSatisfiable := by
    apply Theory.isSatisfiable_iff_isFinitelySatisfiable.mpr
    intro Γ hΓ
    by_contra hunsat
    let B := Γ.filter (· ∈ bad)
    have hb (γ : {γ // γ ∈ B}) :
        ∃ ψ : L.Formula (Fin n), ψ.IsExistential ∧ ¬ψ.Realize a ∧
          γ.val = Formula.equivSentence ψ.not :=
      (Finset.mem_filter.mp γ.property).2
    let chooseψ (γ : {γ // γ ∈ B}) : L.Formula (Fin n) := Classical.choose (hb γ)
    have hchoose (γ : {γ // γ ∈ B}) := Classical.choose_spec (hb γ)
    let s : List (L.Formula (Fin n)) := B.attach.toList.map chooseψ
    have hs (ψ : L.Formula (Fin n)) (hψ : ψ ∈ s) :
        ψ.IsExistential ∧ ¬ψ.Realize a := by
      obtain ⟨γ, _, rfl⟩ := List.mem_map.mp hψ
      exact ⟨(hchoose γ).1, (hchoose γ).2.1⟩
    obtain ⟨χ, hχ, heχ⟩ := existential_finite_disjunction s (fun ψ hψ => (hs ψ hψ).1)
    have himp : T ⊨ᵇ (φ.imp χ) := by
      apply Theory.models_formula_iff.mpr
      intro N v
      rw [Formula.realize_imp]
      intro hv
      by_contra hnχ
      have hdisj : ¬ (s.foldr (· ⊔ ·) ⊥).Realize v := by
        intro hh
        exact hnχ ((Formula.realize_iff.mp (heχ.realize_formula N)).mpr hh)
      have hnot (ψ : L.Formula (Fin n)) (hψ : ψ ∈ s) : ¬ψ.Realize v := by
        intro hh
        apply hdisj
        exact (BoundedFormula.realize_foldr_sup s v default).mpr ⟨ψ, hψ, hh⟩
      let : L[[Fin n]].Structure N := Diagrams.namedExpansion (L := L) v
      have : lhom.IsExpansionOn N := Diagrams.namedExpansion_isExpansion v
      have hmodel : N ⊨ (↑Γ : L[[Fin n]].Theory) := by
        constructor
        intro γ hγ
        rcases hΓ hγ with (hγT | hγφ) | hγbad
        · obtain ⟨δ, hδ, rfl⟩ := hγT
          apply (LHom.realize_onSentence N lhom δ).mpr
          exact N.is_model.realize_of_mem δ hδ
        · obtain rfl := Set.mem_singleton_iff.mp hγφ
          exact (Formula.realize_equivSentence N φ).mpr hv
        · have hγB : γ ∈ B := Finset.mem_filter.mpr ⟨hγ, hγbad⟩
          let γB : {γ // γ ∈ B} := ⟨γ, hγB⟩
          have hmem : chooseψ γB ∈ s :=
            List.mem_map.mpr ⟨γB, by simp, rfl⟩
          change N ⊨ γB.val
          rw [(hchoose γB).2.2]
          apply (Formula.realize_equivSentence N _).mpr
          exact Formula.realize_not.mpr (hnot _ hmem)
      exact hunsat (Theory.Model.isSatisfiable N)
    have hχa := ha χ ⟨hχ, himp⟩
    have hsa := (Formula.realize_iff.mp (heχ.realize_formula M)).mp hχa
    obtain ⟨ψ, hψ, hh⟩ := (BoundedFormula.realize_foldr_sup s a default).mp hsa
    exact (hs ψ hψ).2 hh
  let A : Theory.ModelType.{_, _, max u v w} U := hU.some.ulift
  let : L.Structure A := lhom.reduct A
  have : lhom.IsExpansionOn A := LHom.isExpansionOn_reduct _ _
  have hAT : A ⊨ T :=
    (LHom.onTheory_model lhom T).mp (A.is_model.mono (by
      intro γ hγ
      exact Or.inl (Or.inl hγ)))
  let : A ⊨ T := hAT
  let N : Theory.ModelType.{u, v, max u v w} T := Theory.ModelType.of T A
  let b : Fin n → N := fun i => (L.con i : A)
  have hbφ : φ.Realize b := by
    apply (Formula.realize_equivSentence A φ).mp
    exact A.is_model.realize_of_mem _ (Or.inl (Or.inr rfl))
  have hinfo : existentialInformation (L := L) b ⊆ existentialInformation (L := L) a := by
    intro ψ hψ
    refine ⟨hψ.1, ?_⟩
    by_contra hnot
    have hmem : Formula.equivSentence ψ.not ∈ U :=
      Or.inr ⟨ψ, hψ.1, hnot, rfl⟩
    have hneg := A.is_model.realize_of_mem _ hmem
    have hn := (Formula.realize_equivSentence A ψ.not).mp hneg
    exact (Formula.realize_not.mp hn) hψ.2
  obtain ⟨C, SC, hne, j, f, heq⟩ := compatible_diagrams a b hinfo
  let : L.Structure C := SC
  let : Nonempty C := hne
  let : C ⊨ T := (j.theory_model_iff T).mp M.is_model
  have hcφ : φ.Realize (f ∘ b) :=
    hφ N (Theory.ModelType.of T C) f b hbφ
  have hab : f ∘ b = j ∘ a := funext heq
  rw [hab] at hcφ
  exact (j.map_formula φ a).mp hcφ

/-- The resulting existential formula is in the actual language and finite free context. -/
theorem extension_preserved_iff_existential {T : L.Theory} {n : ℕ}
    (φ : L.Formula (Fin n)) :
    ExtensionPreserved.{u, v, w} T φ ↔
      ∃ ψ : L.Formula (Fin n), ψ.IsExistential ∧ T ⊨ᵇ (φ.iff ψ) := by
  classical
  constructor
  · intro hφ
    have hb := extensionPreserved_base hφ
    let lhom := L.lhomWithConstants (Fin n)
    let G : L[[Fin n]].Theory :=
      {γ | ∃ ψ ∈ existentialConsequences T φ, γ = Formula.equivSentence ψ}
    let U : L[[Fin n]].Theory := lhom.onTheory T ∪ G
    have hUφ : U ⊨ᵇ Formula.equivSentence φ := by
      apply Theory.models_sentence_iff.mpr
      intro A
      let : L.Structure A := lhom.reduct A
      have : lhom.IsExpansionOn A := LHom.isExpansionOn_reduct _ _
      have hAT : A ⊨ T :=
        (LHom.onTheory_model lhom T).mp (A.is_model.mono Set.subset_union_left)
      let : A ⊨ T := hAT
      let M : Theory.ModelType.{u, v, max u v} T := Theory.ModelType.of T A
      let a : Fin n → M := fun i => (L.con i : A)
      apply (Formula.realize_equivSentence A φ).mpr
      apply existentialConsequences_entail hb M a
      intro ψ hψ
      apply (Formula.realize_equivSentence A ψ).mp
      exact A.is_model.realize_of_mem _ (Or.inr ⟨ψ, hψ, rfl⟩)
    obtain ⟨Δ, hΔ, hΔφ⟩ := Theory.models_iff_finset_models.mp hUφ
    let B := Δ.filter (· ∈ G)
    have hbψ (γ : {γ // γ ∈ B}) :
        ∃ ψ ∈ existentialConsequences T φ, γ.val = Formula.equivSentence ψ :=
      (Finset.mem_filter.mp γ.property).2
    let chooseψ (γ : {γ // γ ∈ B}) : L.Formula (Fin n) := Classical.choose (hbψ γ)
    have hchoose (γ : {γ // γ ∈ B}) := Classical.choose_spec (hbψ γ)
    let s : List (L.Formula (Fin n)) := B.attach.toList.map chooseψ
    have hs (ψ : L.Formula (Fin n)) (hψ : ψ ∈ s) : ψ ∈ existentialConsequences T φ := by
      obtain ⟨γ, _, rfl⟩ := List.mem_map.mp hψ
      exact (hchoose γ).1
    obtain ⟨χ, hχ, heχ⟩ := existential_finite_conjunction s (fun ψ hψ => (hs ψ hψ).1)
    refine ⟨χ, hχ, ?_⟩
    apply Theory.models_formula_iff.mpr
    intro N v
    rw [Formula.realize_iff]
    constructor
    · intro hv
      apply (Formula.realize_iff.mp (heχ.realize_formula N)).mpr
      apply (BoundedFormula.realize_foldr_inf s v default).mpr
      intro ψ hψ
      have hp := (hs ψ hψ).2.realize_formula N (v := v)
      exact (Formula.realize_imp.mp hp) hv
    · intro hv
      have hc := (Formula.realize_iff.mp (heχ.realize_formula N)).mp hv
      have hall := (BoundedFormula.realize_foldr_inf s v default).mp hc
      let : L[[Fin n]].Structure N := Diagrams.namedExpansion (L := L) v
      have : lhom.IsExpansionOn N := Diagrams.namedExpansion_isExpansion v
      have hmodel : N ⊨ (↑Δ : L[[Fin n]].Theory) := by
        constructor
        intro γ hγ
        rcases hΔ hγ with hγT | hγG
        · obtain ⟨δ, hδ, rfl⟩ := hγT
          apply (LHom.realize_onSentence N lhom δ).mpr
          exact N.is_model.realize_of_mem δ hδ
        · have hγB : γ ∈ B := Finset.mem_filter.mpr ⟨hγ, hγG⟩
          let γB : {γ // γ ∈ B} := ⟨γ, hγB⟩
          have hmem : chooseψ γB ∈ s := List.mem_map.mpr ⟨γB, by simp, rfl⟩
          change N ⊨ γB.val
          rw [(hchoose γB).2]
          exact (Formula.realize_equivSentence N _).mpr (hall _ hmem)
      let : N ⊨ (↑Δ : L[[Fin n]].Theory) := hmodel
      exact (Formula.realize_equivSentence N φ).mp (hΔφ.realize_sentence N)
  · rintro ⟨ψ, hψ, heq⟩
    exact extensionPreserved_of_equivalent hψ heq

/-- The dual formula preservation theorem, relative to any background theory. -/
theorem downward_preserved_iff_universal {T : L.Theory} {n : ℕ}
    (φ : L.Formula (Fin n)) :
    DownwardPreserved.{u, v, w} T φ ↔
      ∃ ψ : L.Formula (Fin n), ψ.IsUniversal ∧ T ⊨ᵇ (φ.iff ψ) := by
  classical
  constructor
  · intro hφ
    have hp : ExtensionPreserved.{u, v, w} T φ.not := by
      intro M N f a ha
      rw [Formula.realize_not] at ha ⊢
      exact fun hh => ha (hφ M N f a hh)
    obtain ⟨ψ, hψ, heψ⟩ := (extension_preserved_iff_existential φ.not).mp hp
    obtain ⟨χ, hχ, heχ⟩ := existential_negation_universal hψ
    refine ⟨χ, hχ, ?_⟩
    apply Theory.models_formula_iff.mpr
    intro M a
    have h1 := Formula.realize_iff.mp (heψ.realize_formula M (v := a))
    have h2 := Formula.realize_iff.mp (heχ.realize_formula M (v := a))
    simp only [Formula.realize_not] at h1 h2
    rw [Formula.realize_iff]
    tauto
  · rintro ⟨ψ, hψ, heq⟩ M N f a ha
    have hN := (Formula.realize_iff.mp (heq.realize_formula N (v := f ∘ a))).mp ha
    apply (Formula.realize_iff.mp (heq.realize_formula M (v := a))).mpr
    apply hψ.realize_embedding f
    simpa only [Formula.Realize, Subsingleton.elim (f ∘ (default : Fin 0 → M))
      (default : Fin 0 → N)] using hN


end Lemmatheca.ModelTheory.Preservation

