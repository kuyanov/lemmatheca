import Lemmatheca.SaturatedModels.Saturation
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

/-- A request uses an actual finite parameter subset of the fixed base model. -/
abbrev Request (L : Language.{0, 0}) (M : Type) [L.Structure M] :=
  Σ A : Finset M, (L[[ (↑A : Set M) ]].completeTheory M).CompleteType (Fin 1)

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

/-- A type's parameter symbols retain the image assigned by this particular elementary map. -/
def RealizesThrough {N : Type} [L.Structure N] (f : M ↪ₑ[L] N)
    {A : Set M} {r : ℕ} (p : (L[[A]].completeTheory M).CompleteType (Fin r))
    (b : Fin r → N) : Prop :=
  @Realizes _ _ (f.toEmbedding.withConstants A) _ (formulas p) b

omit [Nonempty M] in
/-- Composition preserves both the realizing tuple and the specified original parameter values. -/
theorem realizesThrough_map {N P : Type} [L.Structure N] [L.Structure P]
    (f : M ↪ₑ[L] N) (g : N ↪ₑ[L] P) {A : Set M} {r : ℕ}
    (p : (L[[A]].completeTheory M).CompleteType (Fin r)) (b : Fin r → N)
    (hp : RealizesThrough f p b) : RealizesThrough (g.comp f) p (g ∘ b)  := by
  intro φ hφ
  have hN : (parameterFormula A φ).Realize (Sum.elim f b) :=
    (parameterFormula_realize f A φ b).mpr (hp φ hφ)
  apply (parameterFormula_realize (g.comp f) A φ (g ∘ b)).mp
  have hP := (g.map_formula (parameterFormula A φ) (Sum.elim f b)).mpr hN
  convert hP using 1
  funext x
  cases x <;> rfl

private noncomputable def renameParameters {A B : Type} {r : ℕ} (e : A ≃ B) :
    L[[A]].Formula (Fin r) ≃ L[[B]].Formula (Fin r) :=
  BoundedFormula.constantsVarsEquiv.trans
    ((BoundedFormula.relabelEquiv (e.sumCongr (Equiv.refl (Fin r)))).trans
      BoundedFormula.constantsVarsEquiv.symm)

private theorem renameParameters_realize {A B : Type} {r : ℕ} (e : A ≃ B)
    {P : Type} [L.Structure P] (v : B → P) (φ : L[[A]].Formula (Fin r)) (b : Fin r → P) :
    @Formula.Realize _ P (Diagrams.namedExpansion v) _ (renameParameters e φ) b ↔
      @Formula.Realize _ P (Diagrams.namedExpansion (v ∘ e)) _ φ b := by
  let : L[[B]].Structure P := Diagrams.namedExpansion v
  let : L[[A]].Structure P := Diagrams.namedExpansion (v ∘ e)
  have hB := BoundedFormula.realize_constantsVarsEquiv
    (M := P) (φ := renameParameters e φ) (v := b) (xs := default)
  have hA := BoundedFormula.realize_constantsVarsEquiv
    (M := P) (φ := φ) (v := b) (xs := default)
  simp only [renameParameters, Equiv.trans_apply, Equiv.apply_symm_apply] at hB
  apply hB.symm.trans
  refine Iff.trans ?_ hA
  change ((BoundedFormula.relabelEquiv (e.sumCongr (Equiv.refl (Fin r))))
      (BoundedFormula.constantsVarsEquiv φ)).Realize (Sum.elim v b) default ↔
    (BoundedFormula.constantsVarsEquiv φ).Realize (Sum.elim (v ∘ e) b) default
  rw [BoundedFormula.realize_relabelEquiv]
  have hv : (Sum.elim v b) ∘ (e.sumCongr (Equiv.refl (Fin r))) =
      Sum.elim (v ∘ e) b := by
    funext x
    cases x <;> rfl
  rw [hv]

omit [Nonempty M] in
/-- Pull a finite parameter set and its actual complete type back through this elementary map. -/
theorem finite_type_pullback {N : Type} [L.Structure N] [Nonempty N]
    (f : M ↪ₑ[L] N) (A : Finset N) (hA : (↑A : Set N) ⊆ Set.range f) {r : ℕ}
    (p : (L[[ (↑A : Set N) ]].completeTheory N).CompleteType (Fin r)) :
    ∃ B : Finset M, f '' (↑B : Set M) = (↑A : Set N) ∧
      ∃ q : (L[[ (↑B : Set M) ]].completeTheory M).CompleteType (Fin r),
        ∀ b : Fin r → N, RealizesThrough f q b ↔ Realizes (formulas p) b  := by
  classical
  let B := A.preimage f f.injective.injOn
  have hBA : f '' (↑B : Set M) = (↑A : Set N) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact Finset.mem_preimage.mp hy
    · intro hx
      obtain ⟨y, rfl⟩ := hA hx
      exact ⟨y, Finset.mem_preimage.mpr hx, rfl⟩
  let k : (↑B : Set M) → (↑A : Set N) :=
    fun x => ⟨f x, Finset.mem_preimage.mp x.property⟩
  have hk : Function.Bijective k := by
    constructor
    · intro x y h
      exact Subtype.ext (f.injective (congrArg Subtype.val h))
    · intro x
      have hx : (x : N) ∈ f '' (↑B : Set M) := by rw [hBA]; exact x.property
      obtain ⟨y, hy, hxy⟩ := hx
      exact ⟨⟨y, hy⟩, Subtype.ext hxy⟩
  let e := Equiv.ofBijective k hk
  have hp := (partial_iff_finitelyRealized_completeTheory (M := N) (formulas p)).mp
    (partial_formulas p)
  obtain ⟨P, SP, hP, g, d, hd⟩ := (parameter_realization (↑A : Set N) (formulas p)).mp hp
  let := SP
  let := hP
  let P' := (g.comp f).toEmbedding.withConstants (↑B : Set M)
  let : Nonempty P' := by change Nonempty P; exact hP
  let : P' ⊨ L[[ (↑B : Set M) ]].completeTheory M :=
    (((g.comp f).liftWithConstants (↑B : Set M)).theory_model_iff _).mp inferInstance
  let d' : Fin r → P' := d
  let q := (L[[ (↑B : Set M) ]].completeTheory M).typeOf (M := P') d'
  have hdmem (φ : L[[ (↑A : Set N) ]].Formula (Fin r)) :
      φ ∈ formulas p ↔ @Formula.Realize _ (g.toEmbedding.withConstants (↑A : Set N)) _ _ φ d := by
    constructor
    · exact hd φ
    · intro hφ
      by_contra hn
      have hnot : φ.not ∈ formulas p := (p.not_mem_iff _).mpr hn
      exact Formula.realize_not.mp (hd _ hnot) hφ
  have heP (φ : L[[ (↑B : Set M) ]].Formula (Fin r)) :
      @Formula.Realize _ P' _ _ φ d' ↔
        @Formula.Realize _ (g.toEmbedding.withConstants (↑A : Set N)) _ _
          (renameParameters e φ) d := by
    exact (renameParameters_realize e (fun x : (↑A : Set N) => g x) φ d).symm
  have heN (φ : L[[ (↑B : Set M) ]].Formula (Fin r)) (b : Fin r → N) :
      @Formula.Realize _ (f.toEmbedding.withConstants (↑B : Set M)) _ _ φ b ↔
        (renameParameters e φ).Realize b := by
    exact (renameParameters_realize e (Subtype.val : (↑A : Set N) → N) φ b).symm
  have hmem (φ : L[[ (↑B : Set M) ]].Formula (Fin r)) :
      φ ∈ formulas q ↔ renameParameters e φ ∈ formulas p := by
    change Formula.equivSentence φ ∈
      (L[[ (↑B : Set M) ]].completeTheory M).typeOf (M := P') d' ↔ _
    exact Theory.CompleteType.formula_mem_typeOf.trans ((heP φ).trans (hdmem _).symm)
  refine ⟨B, hBA, q, fun b => ?_⟩
  constructor
  · intro hq φ hφ
    let ψ := (renameParameters (L := L) (r := r) e).symm φ
    have hψ : ψ ∈ formulas q := (hmem ψ).mpr (by
      simpa only [ψ, Equiv.apply_symm_apply] using hφ)
    have h := (heN ψ b).mp (hq ψ hψ)
    simpa only [ψ, Equiv.apply_symm_apply] using h
  · intro hp φ hφ
    exact (heN φ b).mpr (hp _ ((hmem φ).mp hφ))

end Lemmatheca.ModelTheory.CountableSaturatedModels
