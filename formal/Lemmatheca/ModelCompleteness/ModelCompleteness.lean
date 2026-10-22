import Lemmatheca.PreservationConverses.Preservation
import Lemmatheca.InductiveTheories.ExistentialReflection
import Lemmatheca.QuantifierElimination.QuantifierEliminationShared

/-! Model completeness and Robinson's existential-closure criterion, in the shared syntax. -/
namespace Lemmatheca.ModelTheory.ModelCompleteness

open FirstOrder FirstOrder.Language
open Lemmatheca.ModelTheory.Preservation
open Lemmatheca.ModelTheory.QuantifierElimination

universe u v w
variable {L : Language.{u, v}}

/-- Every supplied embedding of nonempty models is elementary, with the same function. -/
def ModelComplete (T : L.Theory) : Prop :=
  ∀ (M N : Theory.ModelType.{u, v, max u v w} T) (f : M ↪[L] N),
    ∃ e : M ↪ₑ[L] N, (e : M → N) = (f : M → N)

/-- An individual model has the witness-reflection property in every model extension. -/
def ExistentiallyClosedModel (T : L.Theory)
    (M : Theory.ModelType.{u, v, max u v w} T) : Prop :=
  ∀ (N : Theory.ModelType.{u, v, max u v w} T) (f : M ↪[L] N),
    ExistentiallyClosedEmbedding f

/-- Every nonempty model is existentially closed among models of the same theory. -/
def AllModelsExistentiallyClosed (T : L.Theory) : Prop :=
  ∀ M : Theory.ModelType.{u, v, max u v w} T, ExistentiallyClosedModel T M

/-- Factoring through the image gives the literal-inclusion formulation. -/
theorem modelComplete_iff_inclusions (T : L.Theory) :
    ModelComplete.{u, v, w} T ↔
      ∀ (N : Theory.ModelType.{u, v, max u v w} T) (S : L.Substructure N),
        Nonempty S → S ⊨ T →
          ∃ e : S ↪ₑ[L] N, (e : S → N) = Subtype.val := by
  constructor
  · intro h N S hne hS
    let := hne
    let := hS
    exact h (Theory.ModelType.of T S) N S.subtype
  · intro h M N f
    let e := f.equivRange
    have hne : Nonempty f.toHom.range := Nonempty.map e inferInstance
    let := hne
    have hS : f.toHom.range ⊨ T := StrongHomClass.theory_model e
    obtain ⟨j, hj⟩ := h N f.toHom.range hne hS
    refine ⟨j.comp e.toElementaryEmbedding, ?_⟩
    funext a
    change j (e a) = f a
    rw [hj]
    rfl

/-- Existential closure has the same literal-inclusion meaning as in the entry. -/
theorem allClosed_iff_inclusions (T : L.Theory) :
    AllModelsExistentiallyClosed.{u, v, w} T ↔
      ∀ (n : ℕ) (φ : L.Formula (Fin n)), φ.IsExistential →
        DownwardInclusionPreserved.{u, v, w} T φ := by
  constructor
  · intro h n φ hφ
    apply (downward_preserved_iff_inclusions T φ).mp
    intro M N f a ha
    exact h M N f n φ hφ a ha
  · intro h M N f n φ hφ a ha
    exact (downward_preserved_iff_inclusions T φ).mpr (h n φ hφ) M N f a ha

/-- Quantifier elimination is sufficient, using the actual theory and shared formulas. -/
theorem qe_implies_modelComplete {T : L.Theory} (hT : HasQuantifierElimination T) :
    ModelComplete.{u, v, w} T := by
  intro M N f
  refine ⟨{ toFun := f, map_formula' := ?_ }, rfl⟩
  intro n φ a
  obtain ⟨ψ, hψ, he⟩ := hT n (Shared.pack φ)
  have hM : φ.Realize a ↔ ψ.Realize Empty.elim a :=
    (Shared.pack_realize φ a).symm.trans (he.realize_bd_iff (M := M))
  have hN : φ.Realize (f ∘ a) ↔ ψ.Realize Empty.elim (f ∘ a) :=
    (Shared.pack_realize φ (f ∘ a)).symm.trans (he.realize_bd_iff (M := N))
  have hψf : ψ.Realize Empty.elim (f ∘ a) ↔ ψ.Realize Empty.elim a := by
    have hv : f ∘ (Empty.elim : Empty → M) = (Empty.elim : Empty → N) :=
      Subsingleton.elim _ _
    simpa only [hv] using (hψ.realize_embedding f (v := Empty.elim) (xs := a))
  exact hN.trans (hψf.trans hM.symm)

/-- Elementary embeddings reflect existential formulas in particular. -/
theorem modelComplete_implies_closed {T : L.Theory} (hT : ModelComplete.{u, v, w} T) :
    AllModelsExistentiallyClosed.{u, v, w} T := by
  intro M N f n φ _hφ a ha
  obtain ⟨e, he⟩ := hT M N f
  have h := e.map_formula φ a
  rw [he] at h
  exact h.mp ha

/-- Relative downward preservation supplies universal equivalents for existential formulas. -/
theorem existential_equivalent_universal_of_closed {T : L.Theory}
    (hT : AllModelsExistentiallyClosed.{u, v, w} T) {n : ℕ}
    (φ : L.Formula (Fin n)) (hφ : φ.IsExistential) :
    ∃ ψ : L.Formula (Fin n), ψ.IsUniversal ∧ φ ⇔[T] ψ := by
  apply (downward_preserved_iff_universal φ).mp
  intro M N f a ha
  exact hT M N f n φ hφ a ha

private theorem universal_relabel {α β : Type*} {m k : ℕ}
    {φ : L.BoundedFormula α k} (h : φ.IsUniversal) (f : α → β ⊕ Fin m) :
    (φ.relabel f).IsUniversal := by
  induction h with
  | of_isQF h => exact (h.relabel f).isUniversal
  | all _ ih => simpa only [BoundedFormula.relabel_all] using ih.all

private theorem existential_relabel {α β : Type*} {m k : ℕ}
    {φ : L.BoundedFormula α k} (h : φ.IsExistential) (f : α → β ⊕ Fin m) :
    (φ.relabel f).IsExistential := by
  induction h with
  | of_isQF h => exact (h.relabel f).isExistential
  | ex _ ih => simpa only [BoundedFormula.relabel_ex] using ih.ex

private theorem qf_toFormula {α : Type*} {k : ℕ} {φ : L.BoundedFormula α k}
    (h : φ.IsQF) : φ.toFormula.IsQF := by
  induction h with
  | falsum => exact BoundedFormula.isQF_bot
  | of_isAtomic h =>
    cases h with
    | equal t s => exact (BoundedFormula.IsAtomic.equal _ _).isQF
    | rel R ts => exact (BoundedFormula.IsAtomic.rel _ _).isQF
  | imp _ _ ihφ ihψ => exact ihφ.imp ihψ

private theorem universal_toFormula {α : Type*} {k : ℕ}
    {φ : L.BoundedFormula α k} (h : φ.IsUniversal) : φ.toFormula.IsUniversal := by
  induction h with
  | of_isQF h => exact (qf_toFormula h).isUniversal
  | all _ ih => exact (universal_relabel ih _).all

private theorem existential_toFormula {α : Type*} {k : ℕ}
    {φ : L.BoundedFormula α k} (h : φ.IsExistential) : φ.toFormula.IsExistential := by
  induction h with
  | of_isQF h => exact (qf_toFormula h).isExistential
  | ex _ ih =>
    exact (existential_relabel ih _).ex

/-- The existing scoped variables become the finite free-variable context. -/
private def unpack {k : ℕ} (φ : L.BoundedFormula Empty k) : L.Formula (Fin k) :=
  φ.toFormula.relabel (Sum.elim Empty.elim id)

private theorem unpack_realize {M : Type*} [L.Structure M] {k : ℕ}
    (φ : L.BoundedFormula Empty k) (a : Fin k → M) :
    (unpack φ).Realize a ↔ φ.Realize Empty.elim a := by
  rw [unpack, Formula.realize_relabel, BoundedFormula.realize_toFormula]
  have hv : (a ∘ Sum.elim Empty.elim id) ∘ Sum.inl = (Empty.elim : Empty → M) :=
    Subsingleton.elim _ _
  rw [hv]
  rfl

private theorem unpack_existential {k : ℕ} {φ : L.BoundedFormula Empty k}
    (h : φ.IsExistential) : (unpack φ).IsExistential :=
  existential_relabel (existential_toFormula h) _

private theorem unpack_universal {k : ℕ} {φ : L.BoundedFormula Empty k}
    (h : φ.IsUniversal) : (unpack φ).IsUniversal :=
  universal_relabel (universal_toFormula h) _

private theorem existential_to_universal_bounded {T : L.Theory}
    (hT : AllModelsExistentiallyClosed.{u, v, w} T) {k : ℕ}
    (φ : L.BoundedFormula Empty k) (hφ : φ.IsExistential) :
    ∃ ψ : L.BoundedFormula Empty k, ψ.IsUniversal ∧ φ ⇔[T] ψ := by
  obtain ⟨ψ, hψ, he⟩ :=
    existential_equivalent_universal_of_closed hT (unpack φ) (unpack_existential hφ)
  refine ⟨Shared.pack ψ, universal_relabel hψ Sum.inr, ?_⟩
  intro M v a
  have hv : v = Empty.elim := Subsingleton.elim _ _
  subst v
  rw [BoundedFormula.realize_iff]
  exact (unpack_realize φ a).symm.trans
    (he.realize_iff.trans (Shared.pack_realize ψ a).symm)

private theorem universal_to_existential_bounded {T : L.Theory}
    (hT : AllModelsExistentiallyClosed.{u, v, w} T) {k : ℕ}
    (φ : L.BoundedFormula Empty k) (hφ : φ.IsUniversal) :
    ∃ ψ : L.BoundedFormula Empty k, ψ.IsExistential ∧ φ ⇔[T] ψ := by
  obtain ⟨β, hβ, hβe⟩ := exists_existential_not hφ
  obtain ⟨γ, hγ, hγe⟩ := existential_to_universal_bounded hT β hβ
  obtain ⟨δ, hδ, hδe⟩ := exists_existential_not hγ
  refine ⟨δ, hδ, ?_⟩
  intro M a xs
  have h₁ := hβe M a xs
  have h₂ := hγe.realize_bd_iff (M := M) (v := a) (xs := xs)
  have h₃ := hδe M a xs
  rw [BoundedFormula.realize_iff]
  tauto

private theorem bounded_normal_forms {T : L.Theory}
    (hT : AllModelsExistentiallyClosed.{u, v, w} T) {k : ℕ}
    (φ : L.BoundedFormula Empty k) :
    (∃ ψ : L.BoundedFormula Empty k, ψ.IsExistential ∧ φ ⇔[T] ψ) ∧
      ∃ χ : L.BoundedFormula Empty k, χ.IsUniversal ∧ φ ⇔[T] χ := by
  refine BoundedFormula.induction_on_all_ex (P := fun {m} θ =>
    (∃ ψ : L.BoundedFormula Empty m, ψ.IsExistential ∧ θ ⇔[T] ψ) ∧
      ∃ χ : L.BoundedFormula Empty m, χ.IsUniversal ∧ θ ⇔[T] χ) φ ?_ ?_ ?_ ?_
  · intro m ψ hψ
    exact ⟨⟨ψ, hψ.isExistential, .refl _⟩, ⟨ψ, hψ.isUniversal, .refl _⟩⟩
  · intro m ψ h
    obtain ⟨χ, hχ, heχ⟩ := h.2
    obtain ⟨θ, hθ, heθ⟩ := universal_to_existential_bounded hT χ.all hχ.all
    exact ⟨⟨θ, hθ, heχ.all.trans heθ⟩, ⟨χ.all, hχ.all, heχ.all⟩⟩
  · intro m ψ h
    obtain ⟨χ, hχ, heχ⟩ := h.1
    obtain ⟨θ, hθ, heθ⟩ := existential_to_universal_bounded hT χ.ex hχ.ex
    exact ⟨⟨χ.ex, hχ.ex, heχ.ex⟩, ⟨θ, hθ, heχ.ex.trans heθ⟩⟩
  · intro m ψ χ he
    have ht : ψ ⇔[T] χ := fun M a xs => he.realize_boundedFormula M
    constructor
    · rintro ⟨⟨β, hβ, heβ⟩, ⟨γ, hγ, heγ⟩⟩
      exact ⟨⟨β, hβ, ht.symm.trans heβ⟩, ⟨γ, hγ, ht.symm.trans heγ⟩⟩
    · rintro ⟨⟨β, hβ, heβ⟩, ⟨γ, hγ, heγ⟩⟩
      exact ⟨⟨β, hβ, ht.trans heβ⟩, ⟨γ, hγ, ht.trans heγ⟩⟩

/-- Prenex-prefix induction yields both normal forms for every formula. -/
theorem normal_forms_of_closed {T : L.Theory}
    (hT : AllModelsExistentiallyClosed.{u, v, w} T) (n : ℕ) (φ : L.Formula (Fin n)) :
    (∃ ψ : L.Formula (Fin n), ψ.IsExistential ∧ φ ⇔[T] ψ) ∧
      ∃ χ : L.Formula (Fin n), χ.IsUniversal ∧ φ ⇔[T] χ := by
  obtain ⟨⟨ψ, hψ, heψ⟩, ⟨χ, hχ, heχ⟩⟩ := bounded_normal_forms hT (Shared.pack φ)
  constructor
  · refine ⟨unpack ψ, unpack_existential hψ, ?_⟩
    apply Theory.models_formula_iff.mpr
    intro M a
    rw [Formula.realize_iff]
    exact (Shared.pack_realize φ a).symm.trans
      (heψ.realize_bd_iff.trans (unpack_realize ψ a).symm)
  · refine ⟨unpack χ, unpack_universal hχ, ?_⟩
    apply Theory.models_formula_iff.mpr
    intro M a
    rw [Formula.realize_iff]
    exact (Shared.pack_realize φ a).symm.trans
      (heχ.realize_bd_iff.trans (unpack_realize χ a).symm)

private theorem modelComplete_of_two_normal_forms {T : L.Theory}
    (hE : ∀ (n : ℕ) (φ : L.Formula (Fin n)),
      ∃ ψ : L.Formula (Fin n), ψ.IsExistential ∧ φ ⇔[T] ψ)
    (hU : ∀ (n : ℕ) (φ : L.Formula (Fin n)),
      ∃ ψ : L.Formula (Fin n), ψ.IsUniversal ∧ φ ⇔[T] ψ) :
    ModelComplete.{u, v, w} T := by
  intro M N f
  refine ⟨{ toFun := f, map_formula' := ?_ }, rfl⟩
  intro n φ a
  obtain ⟨ψ, hψ, heψ⟩ := hE n φ
  have hup := extensionPreserved_of_equivalent hψ heψ
  have hdown := (downward_preserved_iff_universal φ).mpr (hU n φ)
  exact ⟨hdown M N f a, hup M N f a⟩

private theorem universal_equivalents_of_existential {T : L.Theory}
    (hE : ∀ (n : ℕ) (φ : L.Formula (Fin n)),
      ∃ ψ : L.Formula (Fin n), ψ.IsExistential ∧ φ ⇔[T] ψ)
    (n : ℕ) (φ : L.Formula (Fin n)) :
    ∃ ψ : L.Formula (Fin n), ψ.IsUniversal ∧ φ ⇔[T] ψ := by
  obtain ⟨ψ, hψ, heψ⟩ := hE n φ.not
  obtain ⟨χ, hχ, heχ⟩ := existential_negation_universal hψ
  refine ⟨χ, hχ, ?_⟩
  apply Theory.models_formula_iff.mpr
  intro M a
  have h₁ := heψ.realize_iff (M := M) (v := a)
  have h₂ := Formula.realize_iff.mp (heχ.realize_formula M (v := a))
  simp only [Formula.realize_not] at h₁ h₂
  rw [Formula.realize_iff]
  tauto

private theorem existential_equivalents_of_universal {T : L.Theory}
    (hU : ∀ (n : ℕ) (φ : L.Formula (Fin n)),
      ∃ ψ : L.Formula (Fin n), ψ.IsUniversal ∧ φ ⇔[T] ψ)
    (n : ℕ) (φ : L.Formula (Fin n)) :
    ∃ ψ : L.Formula (Fin n), ψ.IsExistential ∧ φ ⇔[T] ψ := by
  obtain ⟨ψ, hψ, heψ⟩ := hU n φ.not
  obtain ⟨χ, hχ, heχ⟩ := universal_negation_existential hψ
  refine ⟨χ, hχ, ?_⟩
  apply Theory.models_formula_iff.mpr
  intro M a
  have h₁ := heψ.realize_iff (M := M) (v := a)
  have h₂ := Formula.realize_iff.mp (heχ.realize_formula M (v := a))
  simp only [Formula.realize_not] at h₁ h₂
  rw [Formula.realize_iff]
  tauto

/-- Robinson's test in its witness-reflection form. -/
theorem modelComplete_iff_allClosed (T : L.Theory) :
    ModelComplete.{u, v, w} T ↔ AllModelsExistentiallyClosed.{u, v, w} T := by
  constructor
  · exact modelComplete_implies_closed
  · intro h
    exact modelComplete_of_two_normal_forms
      (fun n φ => (normal_forms_of_closed h n φ).1)
      (fun n φ => (normal_forms_of_closed h n φ).2)

/-- The existential equivalent uses the same language and finite free-variable context. -/
theorem modelComplete_iff_existential (T : L.Theory) :
    ModelComplete.{u, v, w} T ↔
      ∀ (n : ℕ) (φ : L.Formula (Fin n)),
        ∃ ψ : L.Formula (Fin n), ψ.IsExistential ∧ φ ⇔[T] ψ := by
  constructor
  · intro h n φ
    exact (normal_forms_of_closed (modelComplete_implies_closed h) n φ).1
  · intro hE
    exact modelComplete_of_two_normal_forms hE (universal_equivalents_of_existential hE)

/-- The dual universal criterion, with the same contexts and background theory. -/
theorem modelComplete_iff_universal (T : L.Theory) :
    ModelComplete.{u, v, w} T ↔
      ∀ (n : ℕ) (φ : L.Formula (Fin n)),
        ∃ ψ : L.Formula (Fin n), ψ.IsUniversal ∧ φ ⇔[T] ψ := by
  constructor
  · intro h n φ
    exact (normal_forms_of_closed (modelComplete_implies_closed h) n φ).2
  · intro hU
    exact modelComplete_of_two_normal_forms (existential_equivalents_of_universal hU) hU

/-- The infinite-equality example is an instance of the shared-syntax criterion. -/
theorem infinite_equality_modelComplete :
    ModelComplete.{0, 0, w} Language.empty.infiniteTheory := by
  exact qe_implies_modelComplete Shared.equality_hasQuantifierElimination

/-- The strict-order example uses exactly the already axiomatized dense-order theory. -/
theorem strictDlo_modelComplete : ModelComplete.{0, 0, w}
    Lemmatheca.ModelTheory.QuantifierElimination.Shared.strictDloTheory := by
  exact qe_implies_modelComplete Shared.strictDlo_hasQuantifierElimination

/-- A useful finite case: embeddings between nonempty singleton models are isomorphisms. -/
theorem modelComplete_of_subsingleton_models {T : L.Theory}
    (hT : ∀ M : Theory.ModelType.{u, v, max u v w} T, Subsingleton M) :
    ModelComplete.{u, v, w} T := by
  classical
  intro M N f
  let := hT M
  let := hT N
  have hf : Function.Surjective f := fun b =>
    ⟨Classical.choice (inferInstance : Nonempty M), Subsingleton.elim _ _⟩
  let e : M ≃[L] N :=
    { toEquiv := Equiv.ofBijective f ⟨f.injective, hf⟩
      map_fun' := f.map_fun
      map_rel' := f.map_rel }
  exact ⟨e.toElementaryEmbedding, rfl⟩

end Lemmatheca.ModelTheory.ModelCompleteness
