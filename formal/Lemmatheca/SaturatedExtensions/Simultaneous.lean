import Lemmatheca.SaturatedExtensions.Requests

/-! One compactness model answers all finite-parameter requests over its source. -/
namespace Lemmatheca.ModelTheory.SaturatedExtensions

open FirstOrder FirstOrder.Language
open Types CountableSaturatedModels

universe u v w w' z

variable {L : Language.{u, v}} {M : Type w} [L.Structure M] [hM : Nonempty M]

/-- Old-element names and request names are disjoint tagged families. -/
abbrev Names (L : Language.{u, v}) (M : Type w) [L.Structure M] :=
  M ⊕ Request L M

/-- Name the old parameters and use this request's variable for its answering point. -/
def requestFormula (r : Request L M)
    (φ : L[[(↑r.1 : Set M)]].Formula (Fin 1)) :
    L.Formula (Names L M) :=
  Formula.relabel (Sum.map id (fun _ : Fin 1 => r)) (parameterFormula (↑r.1 : Set M) φ)

omit hM in
/-- The actual translated formula has exactly the intended parameter interpretation. -/
theorem requestFormula_realize [Nonempty M] {N : Type w'} [L.Structure N]
    (f : M ↪ₑ[L] N) (a : Request L M → N) (r : Request L M)
    (φ : L[[(↑r.1 : Set M)]].Formula (Fin 1)) :
    (requestFormula r φ).Realize (Sum.elim f a) ↔
      @Formula.Realize _ (f.toEmbedding.withConstants (↑r.1 : Set M)) _ _ φ
        (fun _ => a r) := by
  rw [requestFormula, Formula.realize_relabel]
  have hv : Sum.elim f a ∘ Sum.map id (fun _ : Fin 1 => r) =
      Sum.elim f (fun _ : Fin 1 => a r) := by
    funext x
    cases x <;> rfl
  rw [hv]
  exact parameterFormula_realize f (↑r.1 : Set M) φ (fun _ => a r)

/-- All old-parameter conditions, in one shared free-name context. -/
def requestFormulas (L : Language.{u, v}) (M : Type w) [L.Structure M] :
    Set (L.Formula (Names L M)) :=
  {ψ | ∃ r : Request L M, ∃ φ ∈ formulas r.2, requestFormula r φ = ψ}

/-- The elementary diagram and every request, in the disjointly named language. -/
def simultaneousTheory (L : Language.{u, v}) (M : Type w) [L.Structure M] :
    L[[Names L M]].Theory :=
  (L.lhomWithConstantsMap (Sum.inl : M → Names L M)).onTheory (L.elementaryDiagram M) ∪
    Formula.equivSentence '' requestFormulas L M

/-- Each finite fragment is modeled on the original carrier with all old names fixed. -/
theorem finite_simultaneous_realization
    (Δ : Finset (L[[Names L M]].Sentence))
    (hΔ : (↑Δ : L[[Names L M]].Theory) ⊆ simultaneousTheory L M) :
    ∃ a : Request L M → M,
      @Theory.Model _ M (Diagrams.namedExpansion (Sum.elim id a))
        (↑Δ : L[[Names L M]].Theory) := by
  classical
  let s := Δ.filter fun γ => γ ∈ Formula.equivSentence '' requestFormulas L M
  have origins (γ : s) : ∃ r : Request L M,
      ∃ φ ∈ formulas r.2, Formula.equivSentence (requestFormula r φ) = γ.val := by
    obtain ⟨ψ, ⟨r, φ, hφ, rfl⟩, hγ⟩ := (Finset.mem_filter.mp γ.property).2
    exact ⟨r, φ, hφ, hγ⟩
  choose r φ hφ hγ using origins
  let q₀ (r₀ : Request L M) :
      Finset (L[[(↑r₀.1 : Set M)]].Formula (Fin 1)) :=
    s.attach.biUnion fun γ => if h : r γ = r₀ then {h ▸ φ γ} else ∅
  have hq₀ (r₀ : Request L M) : (↑(q₀ r₀) : Set (L[[(↑r₀.1 : Set M)]].Formula (Fin 1))) ⊆ formulas r₀.2 := by
    intro η hη
    obtain ⟨γ, _, hη⟩ := Finset.mem_biUnion.mp hη
    by_cases h : r γ = r₀
    · simp only [dite_eq_left h, Finset.mem_singleton] at hη
      subst r₀
      subst η
      exact hφ γ
    · simp only [dite_eq_right h, Finset.notMem_empty] at hη
  have hsolve (r₀ : Request L M) : ∃ b : Fin 1 → M, Realizes (↑(q₀ r₀) : Set (L[[(↑r₀.1 : Set M)]].Formula (Fin 1))) b :=
    (partial_iff_finitelyRealized_completeTheory _).mp (partial_formulas r₀.2)
      (q₀ r₀) (hq₀ r₀)
  choose b hb using hsolve
  let a : Request L M → M := fun r₀ => b r₀ 0
  let : L[[Names L M]].Structure M := Diagrams.namedExpansion (Sum.elim id a)
  let : (L.lhomWithConstants (Names L M)).IsExpansionOn M :=
    Diagrams.namedExpansion_isExpansion (Sum.elim id a)
  let k := L.lhomWithConstantsMap (Sum.inl : M → Names L M)
  let : k.IsExpansionOn M := by
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
  refine ⟨a, ⟨fun γ hmem => ?_⟩⟩
  rcases hΔ hmem with hdiag | hreq
  · obtain ⟨δ, hδ, rfl⟩ := hdiag
    exact (LHom.realize_onSentence M k δ).mpr hδ
  · let γ' : s := ⟨γ, Finset.mem_filter.mpr ⟨hmem, hreq⟩⟩
    have hφmem : φ γ' ∈ q₀ (r γ') := by
      apply Finset.mem_biUnion.mpr
      refine ⟨γ', Finset.mem_attach _ _, ?_⟩
      simp
    have hreal := hb (r γ') (φ γ') hφmem
    have hv : (fun _ : Fin 1 => a (r γ')) = b (r γ') := by
      funext i
      exact congrArg (b (r γ')) (Subsingleton.elim 0 i)
    have hnamed := (requestFormula_realize (ElementaryEmbedding.refl L M) a
      (r γ') (φ γ')).mpr (by
        rw [hv]
        convert (parameter_type_transport (ElementaryEmbedding.refl L M)
          (↑(r γ').1 : Set M) (b (r γ')) (φ γ')).mp hreal using 1
        rfl)
    have hsent := (Formula.realize_equivSentence M (requestFormula (r γ') (φ γ'))).mpr hnamed
    rw [hγ γ'] at hsent
    exact hsent

/-- Compactness is applied to the actual simultaneous theory. -/
theorem simultaneousTheory_satisfiable :
    (simultaneousTheory L M).IsSatisfiable := by
  apply Theory.isSatisfiable_iff_isFinitelySatisfiable.mpr
  intro Δ hΔ
  obtain ⟨a, ha⟩ := finite_simultaneous_realization Δ hΔ
  let : L[[Names L M]].Structure M := Diagrams.namedExpansion (Sum.elim id a)
  let : M ⊨ (↑Δ : L[[Names L M]].Theory) := ha
  exact Theory.Model.isSatisfiable M

/-- A compactness model's old names define this specified elementary map. -/
noncomputable def canonicalEmbedding
    (N : (simultaneousTheory L M).ModelType.{_, _, z}) :
    letI : L.Structure N := (L.lhomWithConstants (Names L M)).reduct N
    M ↪ₑ[L] N := by
  let : L.Structure N := (L.lhomWithConstants (Names L M)).reduct N
  let k := L.lhomWithConstantsMap (Sum.inl : M → Names L M)
  let : L[[M]].Structure N := k.reduct N
  let : (L.lhomWithConstants M).IsExpansionOn N := ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  have hdiag : N ⊨ L.elementaryDiagram M := by
    apply (LHom.onTheory_model k (L.elementaryDiagram M)).mp
    exact N.is_model.mono Set.subset_union_left
  let := hdiag
  exact ElementaryEmbedding.ofModelsElementaryDiagram L M N

omit hM in
/-- The retained map sends each old point to the interpretation of its own old name. -/
theorem canonicalEmbedding_apply [Nonempty M]
    (N : (simultaneousTheory L M).ModelType.{_, _, z}) (m : M) :
    canonicalEmbedding N m = (L.con (Sum.inl m : Names L M) : N) := by
  rfl

/-- Each fresh request name, rather than an unspecified alternative point, answers its type. -/
theorem canonical_request_answer
    (N : (simultaneousTheory L M).ModelType.{_, _, z}) (r : Request L M) :
    letI : L.Structure N := (L.lhomWithConstants (Names L M)).reduct N
    RealizesThrough (canonicalEmbedding N) r.2
      (fun _ => (L.con (Sum.inr r : Names L M) : N)) := by
  let : L.Structure N := (L.lhomWithConstants (Names L M)).reduct N
  let : (L.lhomWithConstants (Names L M)).IsExpansionOn N :=
    LHom.isExpansionOn_reduct _ _
  intro φ hφ
  have hn : N ⊨ Formula.equivSentence (requestFormula r φ) :=
    N.is_model.realize_of_mem _ (Or.inr ⟨requestFormula r φ, ⟨r, φ, hφ, rfl⟩, rfl⟩)
  have hr := (Formula.realize_equivSentence N (requestFormula r φ)).mp hn
  apply (requestFormula_realize (canonicalEmbedding N)
    (fun s => (L.con (Sum.inr s : Names L M) : N)) r φ).mp
  convert hr using 1
  funext x
  cases x <;> rfl

/-- One extension answers every type over the original finite parameter sets at once. -/
theorem one_pass_extension :
    ∃ (N : Type (max u v w)) (_ : L.Structure N) (_ : Nonempty N),
      ∃ f : M ↪ₑ[L] N, RealizesAllOver f := by
  let N := (simultaneousTheory_satisfiable (L := L) (M := M)).some
  let : L.Structure N := (L.lhomWithConstants (Names L M)).reduct N
  refine ⟨N, inferInstance, inferInstance, canonicalEmbedding N, ?_⟩
  intro A q
  exact ⟨fun _ => (L.con (Sum.inr (⟨A, q⟩ : Request L M) : Names L M) : N),
    canonical_request_answer N ⟨A, q⟩⟩

end Lemmatheca.ModelTheory.SaturatedExtensions
