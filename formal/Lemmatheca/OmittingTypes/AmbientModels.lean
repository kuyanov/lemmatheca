import Lemmatheca.OmittingTypes.OmittingTypes

/-! An ambient extension can realize a type although the specified named carrier omits it. -/
namespace Lemmatheca.ModelTheory.OmittingTypes

open FirstOrder FirstOrder.Language
open Lemmatheca.ModelTheory.Types

universe u v w w'
variable {L : Language.{u, v}} {T : L.Theory} {k : ℕ}

/-- Completeness of the background theory makes each finite part realizable in every model. -/
theorem complete_type_finitely_realized (hT : T.IsComplete) (p : T.CompleteType (Fin k))
    {M : Type w} [L.Structure M] [Nonempty M] [M ⊨ T] :
    FinitelyRealized M (formulas p) := by
  intro Γ hΓ
  obtain ⟨N, a, ha⟩ := T.exists_modelType_is_realized_in p
  have hreal : Realizes (formulas p) a := (realizes_complete_iff p a).mpr ha.symm
  let θ := Formula.iInf fun φ : Γ => φ.val
  have hN : N ⊨ IsolatedTypes.existentialSentence θ :=
    (IsolatedTypes.existentialSentence_realize θ).mpr
      ⟨a, Formula.realize_iInf.mpr (fun φ => hreal φ.val (hΓ φ.property))⟩
  have hTθ : T ⊨ᵇ IsolatedTypes.existentialSentence θ :=
    (hT.realize_sentence_iff _ N).mp hN
  obtain ⟨b, hb⟩ := (IsolatedTypes.existentialSentence_realize θ).mp
    (hTθ.realize_sentence M)
  exact ⟨b, fun φ hφ => Formula.realize_iInf.mp hb ⟨φ, hφ⟩⟩

/-- A model of all the named requests has an expanded-language elementary extension realizing p. -/
theorem ambient_extension_realizes (hT : T.IsComplete) (p : T.CompleteType (Fin k))
    (U : L[[ℕ]].Theory) (hUT : (L.lhomWithConstants ℕ).onTheory T ⊆ U)
    {M : Type w} [L[[ℕ]].Structure M] [Nonempty M] [M ⊨ U] :
    ∃ N : Type (max u v w), ∃ _ : L[[ℕ]].Structure N, ∃ _ : Nonempty N,
      ∃ _e : M ↪ₑ[L[[ℕ]]] N, N ⊨ U ∧
        letI : L.Structure N := (L.lhomWithConstants ℕ).reduct N
        ∃ x : Fin k → N, Realizes (formulas p) x := by
  classical
  let : L.Structure M := (L.lhomWithConstants ℕ).reduct M
  let : (L.lhomWithConstants ℕ).IsExpansionOn M := LHom.isExpansionOn_reduct _ _
  let : M ⊨ T := (LHom.onTheory_model _ _).mp
    ((inferInstance : M ⊨ U).mono hUT)
  let lift (φ : L.Formula (Fin k)) : L[[ℕ]].Formula (M ⊕ Fin k) :=
    (L.lhomWithConstants ℕ).onFormula (Formula.relabel Sum.inr φ)
  let P : Set (L[[ℕ]].Formula (M ⊕ Fin k)) := lift '' formulas p
  have finite (Γ : Finset (L[[ℕ]].Formula (M ⊕ Fin k)))
      (hΓ : (↑Γ : Set (L[[ℕ]].Formula (M ⊕ Fin k))) ⊆ P) :
      ∃ x : Fin k → M, Realizes (↑Γ : Set (L[[ℕ]].Formula (M ⊕ Fin k))) (Sum.elim id x) := by
    have pre (ψ : Γ) : ∃ φ, φ ∈ formulas p ∧ lift φ = ψ.val := hΓ ψ.property
    choose f hf hfeq using pre
    let Δ := Γ.attach.image f
    have hΔ : (↑Δ : Set (L.Formula (Fin k))) ⊆ formulas p := by
      intro φ hφ
      obtain ⟨ψ, _, rfl⟩ := Finset.mem_image.mp hφ
      exact hf ψ
    obtain ⟨x, hx⟩ := complete_type_finitely_realized (M := M) hT p Δ hΔ
    refine ⟨x, fun ψ hψ => ?_⟩
    have heq := hfeq ⟨ψ, hψ⟩
    change lift (f ⟨ψ, hψ⟩) = ψ at heq
    rw [← heq]
    simp only [lift, LHom.realize_onFormula, Formula.realize_relabel,
      Function.comp_def, Sum.elim_inr]
    exact hx _ (Finset.mem_image.mpr ⟨⟨ψ, hψ⟩, Finset.mem_attach _ _, rfl⟩)
  obtain ⟨N, hN, hne, e, x, hx⟩ := exists_elementary_realization P finite
  let := hN
  let := hne
  refine ⟨N, hN, hne, e, (e.theory_model_iff U).mp (inferInstance : M ⊨ U), ?_⟩
  let : L.Structure N := (L.lhomWithConstants ℕ).reduct N
  let : (L.lhomWithConstants ℕ).IsExpansionOn N := LHom.isExpansionOn_reduct _ _
  refine ⟨x, fun φ hφ => ?_⟩
  have h := hx (lift φ) ⟨φ, hφ, rfl⟩
  simpa only [lift, LHom.realize_onFormula, Formula.realize_relabel,
    Function.comp_def, Sum.elim_inr] using h

/-- An elementary map in the expanded language keeps exactly the old image of all new-name values. -/
theorem named_range_transport {M : Type w} {N : Type w'}
    [L[[ℕ]].Structure M] [L[[ℕ]].Structure N] (e : M ↪ₑ[L[[ℕ]]] N) :
    Set.range (fun c : ℕ => (L.con c : N)) =
      e '' Set.range (fun c : ℕ => (L.con c : M)) := by
  ext x
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨(L.con c : M), ⟨c, rfl⟩, e.map_constants (L.con c)⟩
  · rintro ⟨y, ⟨c, rfl⟩, rfl⟩
    exact ⟨c, (e.map_constants (L.con c)).symm⟩

/-- A realizing tuple in an ambient model of the avoidance clauses has an unnamed coordinate. -/
theorem realizer_has_unnamed_coordinate (p : T.CompleteType (Fin k))
    (U : Set (L.Formula ℕ))
    (havoid : ∀ t : Fin k → ℕ, ∃ φ ∈ formulas p, (Formula.relabel t φ).not ∈ U)
    {M : Type w} [L.Structure M] (a : ℕ → M) (ha : Realizes U a)
    (x : Fin k → M) (hx : Realizes (formulas p) x) :
    ∃ i, x i ∉ Set.range a := by
  classical
  by_contra h
  push Not at h
  choose t ht using h
  obtain ⟨φ, hφ, hnφ⟩ := havoid t
  have heq : a ∘ t = x := funext ht
  apply Formula.realize_not.mp (ha _ hnφ)
  simpa only [Formula.realize_relabel, heq] using hx φ hφ

end Lemmatheca.ModelTheory.OmittingTypes
