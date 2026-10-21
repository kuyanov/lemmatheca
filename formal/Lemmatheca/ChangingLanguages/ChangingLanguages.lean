import Lemmatheca.HenkinCompleteness.HenkinCompleteness
import Mathlib.ModelTheory.Satisfiability

/-! Symbol translations in the shared first-order syntax and natural deduction.
Finite symbol support reduces arbitrary-language completeness to the existing
countable-language theorem, after independent semantic compactness. -/
namespace Lemmatheca.MathematicalLogic.ChangingLanguages
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic.FirstOrderProofs

universe u v u' v' w w'
variable {L : Language.{u, v}} {K : Language.{u', v'}}
variable {α : Type w} {β : Type w'}
noncomputable section
local instance {δ : Type*} : DecidableEq δ := Classical.decEq _

@[simp] theorem map_term_relabel (j : L →ᴸ K) (t : L.Term α) (f : α → β) :
    j.onTerm (t.relabel f) = (j.onTerm t).relabel f := by
  induction t with
  | var x => rfl
  | func F ts ih => simp [Term.relabel, ih]

@[simp] theorem map_term_subst (j : L →ᴸ K) (t : L.Term α) (σ : α → L.Term β) :
    j.onTerm (t.subst σ) = (j.onTerm t).subst (fun x => j.onTerm (σ x)) := by
  induction t with
  | var x => rfl
  | func F ts ih => simp [Term.subst, ih]

@[simp] theorem map_formula_relabel (j : L →ᴸ K) {n m : ℕ}
    (A : L.BoundedFormula α n) (f : α → β ⊕ Fin m) :
    j.onBoundedFormula (A.relabel f) = (j.onBoundedFormula A).relabel f := by
  induction A with
  | falsum => rfl
  | equal s t => simp [BoundedFormula.relabel, BoundedFormula.mapTermRel, Term.bdEqual]
  | rel R ts => simp [BoundedFormula.relabel, BoundedFormula.mapTermRel,
      Relations.boundedFormula, Function.comp_def]
  | imp A B ihA ihB =>
      change (j.onBoundedFormula (A.relabel f)).imp (j.onBoundedFormula (B.relabel f)) = _
      rw [ihA, ihB]
      rfl
  | all A ih =>
      simp only [BoundedFormula.relabel_all, LHom.onBoundedFormula, ih]

@[simp] theorem map_formula_subst (j : L →ᴸ K) {n : ℕ}
    (A : L.BoundedFormula α n) (σ : α → L.Term β) :
    j.onBoundedFormula (A.subst σ) =
      (j.onBoundedFormula A).subst (fun x => j.onTerm (σ x)) := by
  induction A with
  | falsum => rfl
  | equal s t =>
      simp only [BoundedFormula.subst, BoundedFormula.mapTermRel, LHom.onBoundedFormula,
        Term.bdEqual, map_term_subst]
      congr 1 <;> (congr 1; funext x; cases x <;> simp [Function.comp_def])
  | rel R ts =>
      simp only [BoundedFormula.subst, BoundedFormula.mapTermRel, LHom.onBoundedFormula,
        Relations.boundedFormula]
      congr 1
      funext i
      dsimp only [Function.comp_def]
      rw [map_term_subst]
      congr 1
      funext x
      cases x <;> simp
  | imp A B ihA ihB =>
      change (j.onBoundedFormula (A.subst σ)).imp (j.onBoundedFormula (B.subst σ)) = _
      rw [ihA, ihB]
      rfl
  | all A ih =>
      change (j.onBoundedFormula (A.subst σ)).all = _
      rw [ih]
      rfl

@[simp] theorem map_toFormula (j : L →ᴸ K) {n : ℕ} (A : L.BoundedFormula α n) :
    j.onFormula A.toFormula = (j.onBoundedFormula A).toFormula := by
  induction A with
  | falsum => rfl
  | equal s t => simp [LHom.onFormula, BoundedFormula.toFormula, Term.equal, Term.bdEqual]
  | rel R ts => simp [LHom.onFormula, BoundedFormula.toFormula, Relations.formula,
      Relations.boundedFormula, Function.comp_def]
  | imp A B ihA ihB => simp only [LHom.onBoundedFormula, BoundedFormula.toFormula,
      LHom.onFormula] at ihA ihB ⊢; rw [ihA, ihB]
  | all A ih =>
      simp only [LHom.onBoundedFormula, BoundedFormula.toFormula, LHom.onFormula] at ih ⊢
      rw [map_formula_relabel, ih]

@[simp] theorem map_instantiate (j : L →ᴸ K)
    (A : L.BoundedFormula α 1) (t : L.Term α) :
    j.onFormula (instantiate A t) = instantiate (j.onBoundedFormula A) (j.onTerm t) := by
  simp only [instantiate, LHom.onFormula, map_formula_subst]
  rw [← LHom.onFormula, map_toFormula]
  congr 1
  funext x
  cases x <;> rfl

/-- Translation of the primitive proof tree, including protected eigenparameters. -/
@[simp] private theorem map_inf (j : L →ᴸ K) (A B : L.Formula α) :
    j.onFormula (A ⊓ B) = j.onFormula A ⊓ j.onFormula B := rfl

@[simp] private theorem map_sup (j : L →ᴸ K) (A B : L.Formula α) :
    j.onFormula (A ⊔ B) = j.onFormula A ⊔ j.onFormula B := rfl

@[simp] private theorem map_not (j : L →ᴸ K) (A : L.Formula α) :
    j.onFormula A.not = (j.onFormula A).not := rfl

@[simp] private theorem map_imp (j : L →ᴸ K) (A B : L.Formula α) :
    j.onFormula (A.imp B) = (j.onFormula A).imp (j.onFormula B) := rfl

@[simp] private theorem map_bot (j : L →ᴸ K) :
    j.onFormula (⊥ : L.Formula α) = ⊥ := rfl

@[simp] private theorem map_all (j : L →ᴸ K) (A : L.BoundedFormula α 1) :
    j.onFormula A.all = (j.onBoundedFormula A).all := rfl

@[simp] private theorem map_ex (j : L →ᴸ K) (A : L.BoundedFormula α 1) :
    j.onFormula A.ex = (j.onBoundedFormula A).ex := rfl

@[simp] private theorem map_equal (j : L →ᴸ K) (s t : L.Term α) :
    j.onFormula (s.equal t) = (j.onTerm s).equal (j.onTerm t) := by
  simp [LHom.onFormula, Term.equal, Term.bdEqual]

@[simp] private theorem map_name_relabel (j : L →ᴸ K) (A : L.Formula α) (f : α → β) :
    j.onFormula (A.relabel f) = (j.onFormula A).relabel f := map_formula_relabel j A _

@[simp] private theorem map_liftContext (j : L →ᴸ K) (Γ : Finset (L.Formula α)) :
    (liftContext Γ).image j.onFormula = liftContext (Γ.image j.onFormula) := by
  simp only [liftContext, Finset.image_image]
  congr 1
  funext A
  exact map_name_relabel j A Sum.inl

theorem coreProof_map (j : L →ᴸ K) {Γ : Finset (L.Formula α)} {A : L.Formula α}
    (h : CoreProof L Γ A) :
    CoreProof K (Γ.image j.onFormula) (j.onFormula A) := by
  induction h with
  | assumption hA => exact .assumption (Finset.mem_image.mpr ⟨_, hA, rfl⟩)
  | conjIntro _ _ ihA ihB => simpa only [map_inf] using CoreProof.conjIntro ihA ihB
  | conjElimLeft _ ih => exact .conjElimLeft (by simpa only [map_inf] using ih)
  | conjElimRight _ ih => exact .conjElimRight (by simpa only [map_inf] using ih)
  | disjIntroLeft _ ih => simpa only [map_sup] using CoreProof.disjIntroLeft ih
  | disjIntroRight _ ih => simpa only [map_sup] using CoreProof.disjIntroRight ih
  | disjElim _ _ _ ihAB ihA ihB =>
      exact .disjElim (by simpa only [map_sup] using ihAB)
        (by simpa only [Finset.image_insert] using ihA)
        (by simpa only [Finset.image_insert] using ihB)
  | impIntro _ ih =>
      rw [map_imp]
      exact .impIntro (by simpa only [Finset.image_insert] using ih)
  | impElim _ _ ihAB ihA => exact .impElim (by simpa only [map_imp] using ihAB) ihA
  | negIntro _ ih =>
      rw [map_not]
      exact .negIntro (by simpa only [Finset.image_insert, map_bot] using ih)
  | negElim _ _ ihA ihnA =>
      rw [map_bot]
      exact .negElim ihA (by simpa only [map_not] using ihnA)
  | falsumElim _ ih => exact .falsumElim (by simpa only [map_bot] using ih)
  | classicalContradiction _ ih =>
      exact .classicalContradiction (by simpa only [Finset.image_insert, map_not, map_bot] using ih)
  | allElim t _ ih =>
      rw [map_instantiate]
      exact .allElim (j.onTerm t) (by simpa only [map_all] using ih)
  | exIntro t _ ih =>
      rw [map_ex]
      exact .exIntro (j.onTerm t) (by simpa only [map_instantiate] using ih)
  | allIntro _ ih =>
      rw [map_all]
      exact .allIntro (by simpa only [map_liftContext, map_toFormula] using ih)
  | exElim _ _ ihEx ihB =>
      exact .exElim (by simpa only [map_ex] using ihEx)
        (by simpa only [Finset.image_insert, map_toFormula, map_liftContext,
          map_name_relabel] using ihB)
  | equalIntro t => simpa only [map_equal] using CoreProof.equalIntro (j.onTerm t)
  | equalElim A s t _ _ ihEq ihA =>
      rw [map_instantiate]
      exact .equalElim (j.onBoundedFormula A) (j.onTerm s) (j.onTerm t)
        (by simpa only [map_equal] using ihEq)
        (by simpa only [map_instantiate] using ihA)

/-- The original reserve of auxiliary names is kept by symbol translation. -/
theorem proof_map (j : L →ᴸ K) {Γ : Finset (L.Formula α)} {A : L.Formula α}
    (h : Proof L Γ A) :
    Proof K (Γ.image j.onFormula) (j.onFormula A) := by
  have hp := coreProof_map j h
  simpa only [Proof, Finset.image_image, Function.comp_def, map_name_relabel] using hp

theorem derives_map (j : L →ᴸ K) {T : L.Theory} {A : L.Sentence}
    (h : Derives T A) : Derives (j.onTheory T) (j.onSentence A) := by
  obtain ⟨Γ, hΓ, hp⟩ := h
  refine ⟨Γ.image j.onSentence, ?_, proof_map j hp⟩
  intro B hB
  obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp hB
  exact ⟨C, hΓ hC, rfl⟩

local instance : DecidableEq L.Symbols := Classical.decEq _

/-- Function and relation symbols carry different tags, and their arities. -/
def termSymbols : L.Term α → Finset L.Symbols
  | .var _ => ∅
  | .func f ts => insert (.inl ⟨_, f⟩) (Finset.univ.biUnion (fun i => termSymbols (ts i)))

/-- Quantification adds no nonlogical symbol. -/
def formulaSymbols : {n : ℕ} → L.BoundedFormula α n → Finset L.Symbols
  | _, .falsum => ∅
  | _, .equal s t => termSymbols s ∪ termSymbols t
  | _, .rel R ts => insert (.inr ⟨_, R⟩) (Finset.univ.biUnion (fun i => termSymbols (ts i)))
  | _, .imp A B => formulaSymbols A ∪ formulaSymbols B
  | _, .all A => formulaSymbols A

/-- The sublanguage of a finite set of tagged symbols. -/
def supportedLanguage (S : Finset L.Symbols) : Language.{u, v} where
  Functions n := {f : L.Functions n // Sum.inl ⟨n, f⟩ ∈ S}
  Relations n := {R : L.Relations n // Sum.inr ⟨n, R⟩ ∈ S}

/-- Inclusion forgets the membership certificates. -/
def supportInclusion (S : Finset L.Symbols) : supportedLanguage S →ᴸ L where
  onFunction := fun {_} => Subtype.val
  onRelation := fun {_} => Subtype.val

theorem supportInclusion_injective (S : Finset L.Symbols) :
    (supportInclusion S).Injective := by
  constructor <;> intro _ _ _ h <;> exact Subtype.ext h

instance supportedLanguage_finite (S : Finset L.Symbols) :
    Finite (supportedLanguage S).Symbols := by
  let e : (supportedLanguage S).Symbols ≃ S := {
    toFun := fun x => match x with
      | .inl ⟨n, ⟨f, h⟩⟩ => ⟨.inl ⟨n, f⟩, h⟩
      | .inr ⟨n, ⟨R, h⟩⟩ => ⟨.inr ⟨n, R⟩, h⟩
    invFun := fun x => match x with
      | ⟨.inl ⟨n, f⟩, h⟩ => .inl ⟨n, ⟨f, h⟩⟩
      | ⟨.inr ⟨n, R⟩, h⟩ => .inr ⟨n, ⟨R, h⟩⟩
    left_inv := by rintro (⟨_, ⟨_, _⟩⟩ | ⟨_, ⟨_, _⟩⟩) <;> rfl
    right_inv := by rintro ⟨(⟨_, _⟩ | ⟨_, _⟩), _⟩ <;> rfl }
  exact Finite.of_equiv S e.symm

instance supportedLanguage_countable (S : Finset L.Symbols) :
    Countable (supportedLanguage S).Symbols := by infer_instance

/-- Restriction is defined for each expression together with its support bound. -/
def restrictTerm (S : Finset L.Symbols) :
    (t : L.Term α) → termSymbols t ⊆ S → (supportedLanguage S).Term α
  | .var x, _ => .var x
  | .func f ts, h => .func ⟨f, h (by simp [termSymbols])⟩ (fun i =>
      restrictTerm S (ts i) (fun _ hx => h (by simp only [termSymbols,
        Finset.mem_insert, Finset.mem_biUnion, Finset.mem_univ, true_and]; exact .inr ⟨i, hx⟩)))

def restrictFormula (S : Finset L.Symbols) :
    {n : ℕ} → (A : L.BoundedFormula α n) → formulaSymbols A ⊆ S →
      (supportedLanguage S).BoundedFormula α n
  | _, .falsum, _ => .falsum
  | _, .equal s t, h => .equal
      (restrictTerm S s (fun _ hx => h (Finset.mem_union_left _ hx)))
      (restrictTerm S t (fun _ hx => h (Finset.mem_union_right _ hx)))
  | _, .rel R ts, h => .rel ⟨R, h (by simp [formulaSymbols])⟩ (fun i =>
      restrictTerm S (ts i) (fun _ hx => h (by simp only [formulaSymbols,
        Finset.mem_insert, Finset.mem_biUnion, Finset.mem_univ, true_and]; exact .inr ⟨i, hx⟩)))
  | _, .imp A B, h => .imp
      (restrictFormula S A (fun _ hx => h (Finset.mem_union_left _ hx)))
      (restrictFormula S B (fun _ hx => h (Finset.mem_union_right _ hx)))
  | _, .all A, h => .all (restrictFormula S A h)

@[simp] theorem include_restrictTerm (S : Finset L.Symbols) (t : L.Term α)
    (h : termSymbols t ⊆ S) :
    (supportInclusion S).onTerm (restrictTerm S t h) = t := by
  induction t with
  | var x => rfl
  | func f ts ih =>
      simp only [restrictTerm, LHom.onTerm, supportInclusion]
      congr 1
      funext i
      exact ih i _

@[simp] theorem include_restrictFormula (S : Finset L.Symbols) {n : ℕ}
    (A : L.BoundedFormula α n) (h : formulaSymbols A ⊆ S) :
    (supportInclusion S).onBoundedFormula (restrictFormula S A h) = A := by
  induction A with
  | falsum => rfl
  | equal s t => simp [restrictFormula, Term.bdEqual]
  | rel R ts =>
      change BoundedFormula.rel R (fun i => (supportInclusion S).onTerm
        (restrictTerm S (ts i) _)) = BoundedFormula.rel R ts
      congr 1
      funext i
      exact include_restrictTerm S (ts i) _
  | imp A B ihA ihB =>
      change ((supportInclusion S).onBoundedFormula (restrictFormula S A _)).imp
        ((supportInclusion S).onBoundedFormula (restrictFormula S B _)) = A.imp B
      rw [ihA, ihB]
  | all A ih =>
      change formulaSymbols A ⊆ S at h
      change ((supportInclusion S).onBoundedFormula (restrictFormula S A _)).all = A.all
      rw [ih]

/-- A whole finite collection and conclusion factor through the same finite language. -/
theorem finite_language_factorization (Γ : Finset L.Sentence) (A : L.Sentence) :
    ∃ (S : Finset L.Symbols) (Γ₀ : Finset (supportedLanguage S).Sentence)
      (A₀ : (supportedLanguage S).Sentence),
      S = Γ.biUnion formulaSymbols ∪ formulaSymbols A ∧
      Γ₀.image (supportInclusion S).onSentence = Γ ∧
      (supportInclusion S).onSentence A₀ = A := by
  classical
  let S := Γ.biUnion formulaSymbols ∪ formulaSymbols A
  have hΓ (B : L.Sentence) (hB : B ∈ Γ) : formulaSymbols B ⊆ S := by
    intro x hx
    exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨B, hB, hx⟩)
  have hA : formulaSymbols A ⊆ S := Finset.subset_union_right
  let Γ₀ := Γ.attach.image (fun B => restrictFormula S B.val (hΓ B.val B.property))
  refine ⟨S, Γ₀, restrictFormula S A hA, rfl, ?_, include_restrictFormula S A hA⟩
  ext B
  constructor
  · intro hB
    obtain ⟨C, hC, hCB⟩ := Finset.mem_image.mp hB
    obtain ⟨⟨D, hD⟩, _, rfl⟩ := Finset.mem_image.mp hC
    have hDB : D = B := (include_restrictFormula S D _).symm.trans hCB
    exact hDB ▸ hD
  · intro hB
    exact Finset.mem_image.mpr ⟨restrictFormula S B (hΓ B hB),
      Finset.mem_image.mpr ⟨⟨B, hB⟩, Finset.mem_attach _ _, rfl⟩,
      include_restrictFormula S B _⟩

/-- Models can be expanded across an injective symbol map. -/
theorem consequence_inclusion_iff (j : L →ᴸ K) (hj : j.Injective)
    {T : L.Theory} {A : L.Sentence} :
    j.onTheory T ⊨ᵇ j.onSentence A ↔ T ⊨ᵇ A := by
  classical
  rw [Theory.models_iff_not_satisfiable, Theory.models_iff_not_satisfiable]
  have he : j.onTheory (T ∪ {A.not}) = j.onTheory T ∪ {(j.onSentence A).not} := by
    simp only [LHom.onTheory, Set.image_union, Set.image_singleton]
    rfl
  rw [← he, Theory.isSatisfiable_onTheory_iff hj]

/-- No countability assumption is made on the original signature. -/
theorem deductive_completeness {T : L.Theory} {A : L.Sentence}
    (h : T ⊨ᵇ A) : Derives T A := by
  classical
  obtain ⟨Γ, hΓ, hsem⟩ := Theory.models_iff_finset_models.mp h
  obtain ⟨S, Γ₀, A₀, _, hΓ₀, hA₀⟩ := finite_language_factorization Γ A
  let i := supportInclusion S
  have himage : i.onTheory (↑Γ₀) = (↑Γ : L.Theory) := by
    rw [← hΓ₀, Finset.coe_image]
    rfl
  have hsem₀ : (↑Γ₀ : (supportedLanguage S).Theory) ⊨ᵇ A₀ := by
    apply (consequence_inclusion_iff i (supportInclusion_injective S)).mp
    rw [himage, hA₀]
    exact hsem
  have hp₀ := Lemmatheca.MathematicalLogic.HenkinCompleteness.deductive_completeness hsem₀
  have hp := derives_map i hp₀
  rw [himage, hA₀] at hp
  exact derives_mono hp hΓ

theorem consequence_iff_derives {T : L.Theory} {A : L.Sentence} :
    T ⊨ᵇ A ↔ Derives T A := by
  constructor
  · exact deductive_completeness
  · intro h
    apply Theory.models_sentence_iff.mpr
    intro M
    exact derives_sound h (default : Empty → M)
      (fun B hB => Theory.realize_sentence_of_mem T hB)

theorem consequence_finite_support {T : L.Theory} {A : L.Sentence}
    (h : T ⊨ᵇ A) :
    ∃ Γ : Finset L.Sentence, (↑Γ : L.Theory) ⊆ T ∧ Derives (↑Γ) A := by
  exact derives_finite_support (deductive_completeness h)

theorem derives_inclusion_iff (j : L →ᴸ K) (hj : j.Injective)
    {T : L.Theory} {A : L.Sentence} :
    Derives (j.onTheory T) (j.onSentence A) ↔ Derives T A := by
  rw [← consequence_iff_derives, ← consequence_iff_derives, consequence_inclusion_iff j hj]

theorem consistent_inclusion_iff (j : L →ᴸ K) (hj : j.Injective) (T : L.Theory) :
    Consistent (j.onTheory T) ↔ Consistent T := by
  exact not_congr (derives_inclusion_iff j hj (A := ⊥))

end
end Lemmatheca.MathematicalLogic.ChangingLanguages
