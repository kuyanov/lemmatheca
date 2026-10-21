import Lemmatheca.DiagramsAndExtensions.Diagrams

open Lemmatheca.MathematicalLogic

/-! Realizing finitely compatible one-point requests over a countable structure.
The names are actual constants in the shared first-order syntax, and the proof
uses finite proof support, soundness and the countable Henkin model theorem.
-/

namespace Lemmatheca.ModelTheory.Diagrams

open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic.FirstOrderProofs
open Lemmatheca.MathematicalLogic.HenkinCompleteness

universe u v w

variable {L : Language.{u, v}} {M : Type w} [L.Structure M]

noncomputable section

/-- A countable elementary extension realizing finitely realizable conditions on one new point.
This construction uses the specified old-name map and one common new point. -/
theorem exists_countable_elementary_realization [Countable L.Symbols] [Countable M]
    [Nonempty M] (p : Set (L.Formula (Option M)))
    (hp : ∀ s : Finset (L.Formula (Option M)), (↑s : Set _) ⊆ p →
      ∃ b : M, ∀ φ ∈ s, φ.Realize (fun o => o.elim b id)) :
    ∃ (N : Type (max u v w)) (_ : L.Structure N), Countable N ∧
      ∃ (h : M ↪ₑ[L] N) (b : N),
        ∀ φ ∈ p, φ.Realize (fun o => o.elim b (fun a => h a)) := by
  classical
  let E := (L.lhomWithConstantsMap (some : M → Option M)).onTheory (L.elementaryDiagram M)
  let T : L[[Option M]].Theory := E ∪ {γ | Formula.equivSentence.symm γ ∈ p}
  have hconsistent : Consistent T := by
    apply consistent_iff_finite.mpr
    intro Γ hΓ
    let s : Finset (L.Formula (Option M)) :=
      (Γ.filter fun γ => Formula.equivSentence.symm γ ∈ p).image Formula.equivSentence.symm
    have hs : (↑s : Set _) ⊆ p := by
      intro φ hφ
      obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hφ
      exact (Finset.mem_filter.mp hγ).2
    obtain ⟨b, hb⟩ := hp s hs
    let f : Option M → M := fun o => o.elim b id
    let : L[[Option M]].Structure M := namedExpansion (L := L) f
    have : (L.lhomWithConstants (Option M)).IsExpansionOn M :=
      namedExpansion_isExpansion f
    have : (L.lhomWithConstantsMap (some : M → Option M)).IsExpansionOn M := by
      constructor
      · intro n g a
        cases g with
        | inl g => rfl
        | inr g =>
          cases n with
          | zero => rfl
          | succ n => exact g.elim
      · intro n R a
        cases R with
        | inl R => rfl
        | inr R => exact R.elim
    have hmodel : M ⊨ (↑Γ : L[[Option M]].Theory) := by
      constructor
      intro γ hγ
      rcases hΓ hγ with he | hpγ
      · obtain ⟨δ, hδ, rfl⟩ := he
        exact (LHom.realize_onSentence M
          (L.lhomWithConstantsMap (some : M → Option M)) δ).mpr hδ
      · have hmem : Formula.equivSentence.symm γ ∈ s :=
          Finset.mem_image.mpr ⟨γ, Finset.mem_filter.mpr ⟨hγ, hpγ⟩, rfl⟩
        apply (Formula.realize_equivSentence_symm_con M γ).mp
        exact hb _ hmem
    exact theory_consistent_of_model hmodel
  obtain ⟨N, SN, hne, hc, hT⟩ := countable_model_existence hconsistent
  let : L[[Option M]].Structure N := SN
  have : Nonempty N := hne
  have : Countable N := hc
  let : L.Structure N := (L.lhomWithConstants (Option M)).reduct N
  have : (L.lhomWithConstants (Option M)).IsExpansionOn N :=
    LHom.isExpansionOn_reduct _ _
  let : L[[M]].Structure N := (L.lhomWithConstantsMap (some : M → Option M)).reduct N
  have : (L.lhomWithConstants M).IsExpansionOn N := by
    exact ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  have hE : N ⊨ E := hT.mono Set.subset_union_left
  have hdiag : N ⊨ L.elementaryDiagram M := (LHom.onTheory_model _ _).mp hE
  have := hdiag
  let h : M ↪ₑ[L] N := ElementaryEmbedding.ofModelsElementaryDiagram L M N
  let b : N := (L.con (none : Option M) : N)
  refine ⟨N, inferInstance, hc, h, b, ?_⟩
  intro φ hφ
  have hγ : Formula.equivSentence φ ∈ T :=
    Or.inr (by simpa using hφ)
  have hnamed := hT.realize_of_mem _ hγ
  have hreal := (Formula.realize_equivSentence N φ).mp hnamed
  convert hreal using 1
  funext o
  cases o <;> rfl

end
end Lemmatheca.ModelTheory.Diagrams
