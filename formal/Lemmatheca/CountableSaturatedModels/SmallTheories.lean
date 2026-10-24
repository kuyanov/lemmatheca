import Lemmatheca.SaturatedExtensions.Requests
import Lemmatheca.CountableCategoricity.Categoricity

/-! Countable type spaces and faithful finite-parameter coordinates. -/
namespace Lemmatheca.ModelTheory.CountableSaturatedModels

open FirstOrder FirstOrder.Language
open Types

variable {L : Language.{0, 0}} {T : L.Theory}

/-- Countably many actual complete types in every finite free-variable context. -/
def Small (T : L.Theory) : Prop := ∀ n, Countable (T.CompleteType (Fin n))

variable {M : Type} [L.Structure M] [Nonempty M] [M ⊨ T]

/-- Put the object variables first and the enumerated parameter coordinates last. -/
def liftParameterFormula {A : Set M} {m r : ℕ} (e : Fin m ≃ A)
    (φ : L[[A]].Formula (Fin r)) : L.Formula (Fin (r + m)) :=
  Formula.relabel (Sum.elim (fun a => Fin.natAdd r (e.symm a)) (Fin.castAdd m))
    (BoundedFormula.constantsVarsEquiv φ)

omit [Nonempty M] in
theorem liftParameterFormula_realize {N : Type} [L.Structure N] {A : Set M} {m r : ℕ}
    (e : Fin m ≃ A) (φ : L[[A]].Formula (Fin r)) (f : M ↪ₑ[L] N) (b : Fin r → N) :
    (liftParameterFormula e φ).Realize (Fin.append b (fun i => f (e i))) ↔
      @Formula.Realize _ (f.toEmbedding.withConstants A) _ _ φ b := by
  rw [liftParameterFormula, Formula.realize_relabel]
  have hv : Fin.append b (fun i => f (e i)) ∘
      Sum.elim (fun a => Fin.natAdd r (e.symm a)) (Fin.castAdd m) =
      Sum.elim (fun a : A => f a) b := by
    funext x
    cases x with
    | inl a => simp only [Function.comp_apply, Sum.elim_inl, Fin.append_right,
        e.apply_symm_apply]
    | inr i => simp only [Function.comp_apply, Sum.elim_inr, Fin.append_left]
  rw [hv]
  convert (BoundedFormula.realize_constantsVarsEquiv (M := f.toEmbedding.withConstants A)
    (φ := φ) (v := b) (xs := default)) using 1 <;> rfl

private structure ParameterRealization {A : Set M} {r : ℕ}
    (p : (L[[A]].completeTheory M).CompleteType (Fin r)) where
  model : T.ModelType.{0, 0, 0}
  embedding : M ↪ₑ[L] model
  tuple : Fin r → model
  realizes : @Realizes _ _ (embedding.toEmbedding.withConstants A) _ (formulas p) tuple

private theorem exists_parameterRealization {A : Set M} {r : ℕ}
    (p : (L[[A]].completeTheory M).CompleteType (Fin r)) :
    Nonempty (ParameterRealization (T := T) p) := by
  have hp := (partial_iff_finitelyRealized_completeTheory (M := M) (formulas p)).mp
    (partial_formulas p)
  obtain ⟨N, SN, hN, f, b, hb⟩ := (parameter_realization A (formulas p)).mp hp
  let := SN
  let := hN
  let : N ⊨ T := (f.theory_model_iff T).mp (inferInstance : M ⊨ T)
  exact ⟨⟨Theory.ModelType.of T N, f, b, hb⟩⟩

/-- Choose one elementary-extension realization and retain its specified named parameters. -/
noncomputable def parameterLift {A : Set M} {m r : ℕ} (e : Fin m ≃ A)
    (p : (L[[A]].completeTheory M).CompleteType (Fin r)) : T.CompleteType (Fin (r + m)) :=
  let R := Classical.choice (exists_parameterRealization (T := T) p)
  T.typeOf (Fin.append R.tuple (fun i => R.embedding (e i)))

theorem parameterLift_membership {A : Set M} {m r : ℕ} (e : Fin m ≃ A)
    (p : (L[[A]].completeTheory M).CompleteType (Fin r))
    (φ : L[[A]].Formula (Fin r)) :
    φ ∈ formulas p ↔ liftParameterFormula e φ ∈ formulas (parameterLift (T := T) e p) := by
  let R := Classical.choice (exists_parameterRealization (T := T) p)
  change φ ∈ formulas p ↔ Formula.equivSentence (liftParameterFormula e φ) ∈
    T.typeOf (Fin.append R.tuple (fun i => R.embedding (e i)))
  rw [Theory.CompleteType.formula_mem_typeOf, liftParameterFormula_realize]
  constructor
  · exact R.realizes φ
  · intro hφ
    by_contra hn
    have hnot : φ.not ∈ formulas p := (p.not_mem_iff _).mpr hn
    exact Formula.realize_not.mp (R.realizes _ hnot) hφ

theorem parameterLift_injective {A : Set M} {m r : ℕ} (e : Fin m ≃ A) :
    Function.Injective (parameterLift (T := T) (r := r) e) := by
  intro p q h
  apply SetLike.ext
  intro γ
  change γ ∈ p.toTheory ↔ γ ∈ q.toTheory
  let φ := Formula.equivSentence.symm γ
  have hc := (parameterLift_membership e p φ).trans
    ((by rw [h] : liftParameterFormula e φ ∈ formulas (parameterLift (T := T) e p) ↔
      liftParameterFormula e φ ∈ formulas (parameterLift (T := T) e q)).trans
      (parameterLift_membership e q φ).symm)
  simpa only [φ, formulas, Set.mem_preimage, Equiv.apply_symm_apply] using hc

theorem countable_parameter_types (h : Small T) (A : Set M) (hA : A.Finite) (r : ℕ) :
    Countable ((L[[A]].completeTheory M).CompleteType (Fin r)) := by
  classical
  let := hA.fintype
  let e := (Fintype.equivFin A).symm
  let := h (r + Fintype.card A)
  exact (parameterLift_injective (T := T) (r := r) e).countable

theorem countable_requests [Countable M] (h : Small T) : Countable (Request L M) := by
  let : ∀ A : Finset M,
      Countable ((L[[ (↑A : Set M) ]].completeTheory M).CompleteType (Fin 1)) :=
    fun A => countable_parameter_types (M := M) (T := T) h (↑A : Set M) A.finite_toSet 1
  infer_instance

theorem request_enumeration [Countable M] (h : Small T) :
    ∃ R : ℕ → Request L M, Function.Surjective R := by
  classical
  let := countable_requests (M := M) h
  let p := (L[[ (↑(∅ : Finset M) : Set M) ]].completeTheory M).typeOf
    (fun _ : Fin 1 => Classical.choice (inferInstance : Nonempty M))
  let : Nonempty (Request L M) := ⟨⟨∅, p⟩⟩
  exact exists_surjective_nat _


end Lemmatheca.ModelTheory.CountableSaturatedModels
