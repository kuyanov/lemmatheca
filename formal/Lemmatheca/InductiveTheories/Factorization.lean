import Lemmatheca.InductiveTheories.Syntax

/-! Compactness factors the supplied existential-reflecting embedding through elementarity. -/
namespace Lemmatheca.ModelTheory.InductiveTheories
open FirstOrder FirstOrder.Language
open Lemmatheca.ModelTheory
open Lemmatheca.ModelTheory.ModelCompleteness
universe u v w w'
variable {L : Language.{u, v}}

/-- The fixed embedding, not merely an isomorphic copy of it, factors through elementarity. -/
theorem elementary_factorization {M : Type w} {N : Type w'}
    [L.Structure M] [L.Structure N] [Nonempty M] [Nonempty N]
    (f : M ↪[L] N) (hf : ExistentiallyClosedEmbedding f) :
    ∃ (P : Type (max u v w w')) (_ : L.Structure P) (_ : Nonempty P)
      (e : M ↪ₑ[L] P) (g : N ↪[L] P), ∀ a, g (f a) = e a := by


  classical
  let K := L[[M ⊕ N]]
  let name := fun φ : L.Formula (M ⊕ N) => Formula.equivSentence φ
  let E : K.Theory := {γ | ∃ φ : L.Formula M,
    φ.Realize id ∧ γ = name (φ.relabel Sum.inl)}
  let D : K.Theory := {γ | ∃ φ : L.Formula N,
    φ.IsQF ∧ φ.Realize id ∧ γ = name (φ.relabel Sum.inr)}
  let equation (a : M) : K.Sentence := name
    ((Term.var (Sum.inr (f a))).equal (Term.var (Sum.inl a)))
  let Q : K.Theory := Set.range equation
  let T := E ∪ D ∪ Q
  have hsat : T.IsSatisfiable := by
    apply Theory.isSatisfiable_iff_isFinitelySatisfiable.mpr
    intro Γ hΓ
    let J := Γ.filter (fun γ => γ ∈ Q)
    choose pick hpick using fun γ : J => (Finset.mem_filter.mp γ.property).2
    let idx := Fintype.equivFin J
    let a : Fin (Fintype.card J) → M := pick ∘ idx.symm
    have hinfo : Preservation.existentialInformation (L := L) (f ∘ a) ⊆
        Preservation.existentialInformation (L := L) a := by
      intro φ hφ
      exact ⟨hφ.1, hf _ φ hφ.1 a hφ.2⟩
    obtain ⟨C, SC, hC, j, g, halign⟩ := Preservation.compatible_diagrams a (f ∘ a) hinfo
    let := SC
    let := hC
    let : K.Structure C := Diagrams.namedExpansion (L := L) (Sum.elim j g)
    let : (L.lhomWithConstants (M ⊕ N)).IsExpansionOn C :=
      Diagrams.namedExpansion_isExpansion (Sum.elim j g)
    have hmodel : C ⊨ (↑Γ : K.Theory) := by
      constructor
      intro γ hγ
      rcases hΓ hγ with (hE | hD) | hQ
      · obtain ⟨φ, hφ, rfl⟩ := hE
        rw [Formula.realize_equivSentence, Formula.realize_relabel]
        exact (j.map_formula φ id).mpr hφ
      · obtain ⟨φ, hq, hφ, rfl⟩ := hD
        rw [Formula.realize_equivSentence, Formula.realize_relabel]
        have he := hq.realize_embedding g (v := id) (xs := (default : Fin 0 → N))
        have he0 : g ∘ (default : Fin 0 → N) = default := Subsingleton.elim _ _
        rw [he0] at he
        exact he.mpr hφ
      · let γ₀ : J := ⟨γ, Finset.mem_filter.mpr ⟨hγ, hQ⟩⟩
        have heq : equation (pick γ₀) = γ := hpick γ₀
        rw [← heq, Formula.realize_equivSentence]
        change g (f (pick γ₀)) = j (pick γ₀)
        simpa only [a, Function.comp_apply, idx.symm_apply_apply] using halign (idx γ₀)
    let := hmodel
    exact Theory.Model.isSatisfiable C
  let C := hsat.some
  let : L.Structure C := (L.lhomWithConstants (M ⊕ N)).reduct C
  let : (L.lhomWithConstants (M ⊕ N)).IsExpansionOn C := LHom.isExpansionOn_reduct _ _
  let : L[[M]].Structure C := (L.lhomWithConstantsMap (Sum.inl : M → M ⊕ N)).reduct C
  let : (L.lhomWithConstants M).IsExpansionOn C := ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  have hEC : C ⊨ L.elementaryDiagram M := by
    constructor
    intro γ hγ
    let φ := Formula.equivSentence.symm γ
    have hm : φ.Realize id := (Formula.realize_equivSentence_symm_con M γ).mpr hγ
    have hh := hsat.some.is_model.realize_of_mem (name (φ.relabel Sum.inl))
      (Or.inl (Or.inl ⟨φ, hm, rfl⟩))
    have hr := (Formula.realize_equivSentence C (φ.relabel Sum.inl)).mp hh
    rw [Formula.realize_relabel] at hr
    apply (Formula.realize_equivSentence_symm_con C γ).mp
    exact hr
  let := hEC
  let e : M ↪ₑ[L] C := ElementaryEmbedding.ofModelsElementaryDiagram L M C
  let : L[[N]].Structure C := (L.lhomWithConstantsMap (Sum.inr : N → M ⊕ N)).reduct C
  let : (L.lhomWithConstants N).IsExpansionOn C := ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  have hDC : C ⊨ Diagrams.quantifierFreeDiagram L N := by
    constructor
    intro γ hγ
    let φ := Formula.equivSentence.symm γ
    have hq : φ.IsQF := by
      dsimp only [φ]
      obtain ⟨k, θ, c, heq, _, hq⟩ := Diagrams.sentence_is_namedFormula γ
      have ht := hq.mp hγ.1
      rw [heq]
      simp only [Diagrams.namedFormula, Equiv.symm_apply_apply]
      exact ht.relabel _
    have hm : φ.Realize id := (Formula.realize_equivSentence_symm_con N γ).mpr hγ.2
    have hh := hsat.some.is_model.realize_of_mem (name (φ.relabel Sum.inr))
      (Or.inl (Or.inr ⟨φ, hq, hm, rfl⟩))
    have hr := (Formula.realize_equivSentence C (φ.relabel Sum.inr)).mp hh
    rw [Formula.realize_relabel] at hr
    apply (Formula.realize_equivSentence_symm_con C γ).mp
    exact hr
  obtain ⟨g, hg⟩ := Diagrams.model_signed_iff_canonical_embedding.mp
    (Diagrams.models_signed_iff_models_quantifierFree.mpr hDC)
  refine ⟨C, inferInstance, inferInstance, e, g, ?_⟩
  intro a
  have hh := hsat.some.is_model.realize_of_mem (equation a) (Or.inr (Set.mem_range_self a))
  rw [hg]
  change (L.con (f a) : C) = (L.con a : C)
  exact (Formula.realize_equivSentence C _).mp hh

end Lemmatheca.ModelTheory.InductiveTheories
