import Lemmatheca.CraigInterpolation.CraigInterpolation

/-! Robinson joint consistency for arbitrary symbol sets. Finite fragments are
used in the proof; the signatures in the conclusion are not assumed finite. -/
namespace Lemmatheca.MathematicalLogic.CraigInterpolation
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic.FirstOrderProofs
open Lemmatheca.MathematicalLogic.ChangingLanguages
open Lemmatheca.MathematicalLogic.JointConsistency
universe u v w
variable {L : Language.{u, v}}
noncomputable section
local instance arbitraryJointDecidableEq {α : Type*} : DecidableEq α := Classical.decEq _
local instance arbitraryJointSymbolDecidableEq : DecidableEq L.Symbols := Classical.decEq _

/-- The sublanguage on an arbitrary set of tagged symbols. -/
def languageOn (S : Set L.Symbols) : Language.{u, v} where
  Functions n := {f : L.Functions n // Sum.inl ⟨n, f⟩ ∈ S}
  Relations n := {R : L.Relations n // Sum.inr ⟨n, R⟩ ∈ S}

def languageOnInclusion (S : Set L.Symbols) : languageOn S →ᴸ L where
  onFunction := fun {_} => Subtype.val
  onRelation := fun {_} => Subtype.val

def languageOnMap {S T : Set L.Symbols} (h : S ⊆ T) :
    languageOn S →ᴸ languageOn T where
  onFunction := fun {_} f => ⟨f.1, h f.2⟩
  onRelation := fun {_} R => ⟨R.1, h R.2⟩

abbrev commonSetLeft (S T : Set L.Symbols) :
    languageOn (S ∩ T) →ᴸ languageOn S := languageOnMap Set.inter_subset_left
abbrev commonSetRight (S T : Set L.Symbols) :
    languageOn (S ∩ T) →ᴸ languageOn T := languageOnMap Set.inter_subset_right

theorem languageOnInclusion_injective (S : Set L.Symbols) :
    (languageOnInclusion S).Injective := by
  constructor <;> intro _ _ _ h <;> exact Subtype.ext h

/-- Syntax restriction only needs a bound on the finitely many occurring symbols. -/
def restrictTermOn (S : Set L.Symbols) {α : Type w} :
    (t : L.Term α) → (∀ x ∈ termSymbols t, x ∈ S) → (languageOn S).Term α
  | .var x, _ => .var x
  | .func f ts, h => .func ⟨f, h _ (by simp [termSymbols])⟩ (fun i =>
      restrictTermOn S (ts i) (fun x hx => h x (by
        simp only [termSymbols, Finset.mem_insert, Finset.mem_biUnion,
          Finset.mem_univ, true_and]
        exact Or.inr ⟨i, hx⟩)))

def restrictFormulaOn (S : Set L.Symbols) {α : Type w} :
    {n : ℕ} → (A : L.BoundedFormula α n) →
      (∀ x ∈ formulaSymbols A, x ∈ S) → (languageOn S).BoundedFormula α n
  | _, .falsum, _ => .falsum
  | _, .equal s t, h => .equal
      (restrictTermOn S s (fun x hx => h x (Finset.mem_union_left _ hx)))
      (restrictTermOn S t (fun x hx => h x (Finset.mem_union_right _ hx)))
  | _, .rel R ts, h => .rel ⟨R, h _ (by simp [formulaSymbols])⟩ (fun i =>
      restrictTermOn S (ts i) (fun x hx => h x (by
        simp only [formulaSymbols, Finset.mem_insert, Finset.mem_biUnion,
          Finset.mem_univ, true_and]
        exact Or.inr ⟨i, hx⟩)))
  | _, .imp A B, h => .imp
      (restrictFormulaOn S A (fun x hx => h x (Finset.mem_union_left _ hx)))
      (restrictFormulaOn S B (fun x hx => h x (Finset.mem_union_right _ hx)))
  | _, .all A, h => .all (restrictFormulaOn S A h)

private theorem include_restrictTermOn (S : Set L.Symbols) {α : Type w}
    (t : L.Term α) (h : ∀ x ∈ termSymbols t, x ∈ S) :
    (languageOnInclusion S).onTerm (restrictTermOn S t h) = t := by
  induction t with
  | var x => rfl
  | func f ts ih =>
    simp only [restrictTermOn, LHom.onTerm, languageOnInclusion]
    congr 1
    funext i
    exact ih i _

private theorem included_term_symbols_set (S : Set L.Symbols) {α : Type w}
    (t : (languageOn S).Term α) :
    ∀ x ∈ termSymbols ((languageOnInclusion S).onTerm t), x ∈ S := by
  induction t with
  | var a => simp [LHom.onTerm, termSymbols]
  | func f ts ih =>
    intro x hx
    simp only [LHom.onTerm, termSymbols, Finset.mem_insert,
      Finset.mem_biUnion, Finset.mem_univ, true_and] at hx
    rcases hx with rfl | ⟨i, hi⟩
    · exact f.property
    · exact ih i x hi

theorem include_restrictFormulaOn (S : Set L.Symbols) {α : Type w} {n : ℕ}
    (A : L.BoundedFormula α n) (h : ∀ x ∈ formulaSymbols A, x ∈ S) :
    (languageOnInclusion S).onBoundedFormula (restrictFormulaOn S A h) = A := by
  induction A with
  | falsum => rfl
  | equal a b => simp [restrictFormulaOn, Term.bdEqual, include_restrictTermOn]
  | rel R ts =>
    change BoundedFormula.rel R (fun i => (languageOnInclusion S).onTerm
      (restrictTermOn S (ts i) _)) = BoundedFormula.rel R ts
    congr 1
    funext i
    exact include_restrictTermOn S (ts i) _
  | imp A B ihA ihB =>
    change ((languageOnInclusion S).onBoundedFormula (restrictFormulaOn S A _)).imp
      ((languageOnInclusion S).onBoundedFormula (restrictFormulaOn S B _)) = A.imp B
    rw [ihA, ihB]
  | all A ih => exact congrArg BoundedFormula.all (ih h)

theorem included_formula_symbols_set (S : Set L.Symbols) {α : Type w} {n : ℕ}
    (A : (languageOn S).BoundedFormula α n) :
    ∀ x ∈ formulaSymbols ((languageOnInclusion S).onBoundedFormula A), x ∈ S := by
  induction A with
  | falsum => simp [LHom.onBoundedFormula, formulaSymbols]
  | equal a b =>
    intro x hx
    simp only [LHom.onBoundedFormula, Term.bdEqual, formulaSymbols,
      Finset.mem_union] at hx
    exact hx.elim (included_term_symbols_set S a x) (included_term_symbols_set S b x)
  | rel R ts =>
    intro x hx
    simp only [LHom.onBoundedFormula, Relations.boundedFormula, formulaSymbols,
      Finset.mem_insert, Finset.mem_biUnion, Finset.mem_univ, true_and] at hx
    rcases hx with rfl | ⟨i, hi⟩
    · exact R.property
    · exact included_term_symbols_set S (ts i) x hi
  | imp A B ihA ihB =>
    intro x hx
    simp only [LHom.onBoundedFormula, formulaSymbols, Finset.mem_union] at hx
    exact hx.elim (ihA x) (ihB x)
  | all A ih => exact ih

theorem inseparable_iff_semantic {L₀ L₁ L₂ : Language.{u, v}}
    (j₁ : L₀ →ᴸ L₁) (j₂ : L₀ →ᴸ L₂)
    (T₁ : L₁.Theory) (T₂ : L₂.Theory) :
    Inseparable j₁ j₂ T₁ T₂ ↔
      ¬ ∃ η : L₀.Sentence,
        T₁ ⊨ᵇ j₁.onSentence η ∧ T₂ ⊨ᵇ (j₂.onSentence η).not := by
  simp only [Inseparable, consequence_iff_derives]

private theorem onSentence_not {L₁ L₂ : Language.{u, v}} (j : L₁ →ᴸ L₂)
    (A : L₁.Sentence) : j.onSentence A.not = (j.onSentence A).not := rfl

private theorem commonSetLeft_image (S T : Set L.Symbols)
    (η : (languageOn (S ∩ T)).Sentence) :
    (languageOnInclusion S).onSentence ((commonSetLeft S T).onSentence η) =
      (languageOnInclusion (S ∩ T)).onSentence η :=
  (congrFun (LHom.comp_onBoundedFormula (languageOnInclusion S)
    (commonSetLeft S T)) η).symm

private theorem commonSetRight_image (S T : Set L.Symbols)
    (η : (languageOn (S ∩ T)).Sentence) :
    (languageOnInclusion T).onSentence ((commonSetRight S T).onSentence η) =
      (languageOnInclusion (S ∩ T)).onSentence η :=
  (congrFun (LHom.comp_onBoundedFormula (languageOnInclusion T)
    (commonSetRight S T)) η).symm

private def conjunction (Γ : Finset L.Sentence) : L.Sentence :=
  Γ.toList.foldr (· ⊓ ·) ⊤

private theorem realize_conjunction (Γ : Finset L.Sentence)
    (M : Type*) [L.Structure M] :
    M ⊨ conjunction Γ ↔ ∀ A ∈ Γ, M ⊨ A := by
  simp only [conjunction, Sentence.Realize, Formula.Realize,
    BoundedFormula.realize_foldr_inf, Finset.mem_toList]

private theorem conjunction_models {T : L.Theory} (Γ : Finset L.Sentence)
    (hΓ : (↑Γ : L.Theory) ⊆ T) : T ⊨ᵇ conjunction Γ := by
  apply Theory.models_sentence_iff.mpr
  intro M
  apply (realize_conjunction Γ M).mpr
  intro A hA
  exact Theory.realize_sentence_of_mem T (hΓ hA)

private theorem conjunction_symbols {S : Set L.Symbols} (Γ : Finset L.Sentence)
    (hΓ : ∀ A ∈ Γ, ∀ x ∈ formulaSymbols A, x ∈ S) :
    ∀ x ∈ formulaSymbols (conjunction Γ), x ∈ S := by
  have hl : ∀ A ∈ Γ.toList, ∀ x ∈ formulaSymbols A, x ∈ S := by simpa using hΓ
  unfold conjunction
  generalize Γ.toList = l at hl ⊢
  induction l with
  | nil => simp [List.foldr_nil, Top.top, BoundedFormula.not, formulaSymbols]
  | cons A l ih =>
    intro x hx
    have hx' : x ∈ formulaSymbols A ∪ formulaSymbols (l.foldr (· ⊓ ·) ⊤) := by
      simpa only [List.foldr_cons, Min.min, BoundedFormula.not, formulaSymbols,
        Finset.union_empty] using hx
    rcases Finset.mem_union.mp hx' with hA | hlx
    · exact hl A List.mem_cons_self x hA
    · exact ih (fun B hB => hl B (List.mem_cons_of_mem _ hB)) x hlx

/-- The exact common signature is the arbitrary intersection, not a finite surrogate. -/
theorem arbitrary_joint_model_iff (S T : Set L.Symbols)
    (T₁ : (languageOn S).Theory) (T₂ : (languageOn T).Theory) :
    ((languageOnInclusion S).onTheory T₁ ∪
      (languageOnInclusion T).onTheory T₂).IsSatisfiable ↔
      Inseparable (commonSetLeft S T) (commonSetRight S T) T₁ T₂ := by
  classical
  constructor
  · intro hsat
    apply (inseparable_iff_semantic (commonSetLeft S T) (commonSetRight S T) T₁ T₂).mpr
    rintro ⟨η, hη₁, hη₂⟩
    let M := hsat.some
    have hM₁ : M ⊨ (languageOnInclusion S).onTheory T₁ :=
      (Theory.model_union_iff.mp M.is_model).1
    have hM₂ : M ⊨ (languageOnInclusion T).onTheory T₂ :=
      (Theory.model_union_iff.mp M.is_model).2
    have hc : M ⊨ (languageOnInclusion (S ∩ T)).onSentence η := by
      have h := (consequence_inclusion_iff (languageOnInclusion S)
        (languageOnInclusion_injective S)).mpr hη₁
      simpa only [commonSetLeft_image] using h.realize_sentence M
    have hnc : M ⊨ ((languageOnInclusion (S ∩ T)).onSentence η).not := by
      have h := (consequence_inclusion_iff (languageOnInclusion T)
        (languageOnInclusion_injective T)).mpr hη₂
      simpa only [onSentence_not, commonSetRight_image] using h.realize_sentence M
    exact (Sentence.realize_not M).mp hnc hc
  · intro hi
    apply Theory.isSatisfiable_iff_isFinitelySatisfiable.mpr
    intro Γ hΓ
    by_contra hnΓ
    let A := (languageOnInclusion S).onTheory T₁
    let B := (languageOnInclusion T).onTheory T₂
    let Γ₁ := Γ.filter (fun φ => φ ∈ A)
    let Γ₂ := Γ.filter (fun φ => φ ∈ B)
    have hΓ₁ : (↑Γ₁ : L.Theory) ⊆ A := by
      intro φ hφ
      exact (Finset.mem_filter.mp hφ).2
    have hΓ₂ : (↑Γ₂ : L.Theory) ⊆ B := by
      intro φ hφ
      exact (Finset.mem_filter.mp hφ).2
    let φ := conjunction Γ₁
    let ψ := conjunction Γ₂
    have hφψ : ({φ} : L.Theory) ⊨ᵇ ψ.not := by
      apply Theory.models_sentence_iff.mpr
      intro M
      apply (Sentence.realize_not M).mpr
      intro hψ
      have hφ : M ⊨ φ := Theory.realize_sentence_of_mem ({φ} : L.Theory) (by simp)
      have hMΓ : M ⊨ (↑Γ : L.Theory) := by
        constructor
        intro χ hχ
        rcases hΓ hχ with hχA | hχB
        · exact (realize_conjunction Γ₁ M).mp hφ χ
            (Finset.mem_filter.mpr ⟨hχ, hχA⟩)
        · exact (realize_conjunction Γ₂ M).mp hψ χ
            (Finset.mem_filter.mpr ⟨hχ, hχB⟩)
      exact hnΓ (Theory.Model.isSatisfiable M)
    have hsentence : ∃ θ : L.Sentence, SentenceInterpolant φ ψ.not θ := by
      obtain ⟨η, hη⟩ := sentence_interpolation φ ψ.not hφψ
      exact ⟨_, hη⟩
    obtain ⟨θ, hfirst, hsecond, hsymbols⟩ := hsentence
    have hφS : ∀ x ∈ formulaSymbols φ, x ∈ S := by
      apply conjunction_symbols Γ₁
      intro χ hχ
      obtain ⟨χ₀, _, rfl⟩ := hΓ₁ hχ
      exact included_formula_symbols_set S χ₀
    have hψT : ∀ x ∈ formulaSymbols ψ, x ∈ T := by
      apply conjunction_symbols Γ₂
      intro χ hχ
      obtain ⟨χ₀, _, rfl⟩ := hΓ₂ hχ
      exact included_formula_symbols_set T χ₀
    have hθ : ∀ x ∈ formulaSymbols θ, x ∈ S ∩ T := by
      intro x hx
      have hboth : x ∈ formulaSymbols φ ∧ x ∈ formulaSymbols ψ.not := by
        simpa only [Finset.mem_inter] using hsymbols hx
      exact ⟨hφS x hboth.1, hψT x (by
        simpa only [BoundedFormula.not, formulaSymbols, Finset.union_empty] using hboth.2)⟩
    let τ := restrictFormulaOn (S ∩ T) θ hθ
    have hcomp₁ : (languageOnInclusion S).onSentence
        ((commonSetLeft S T).onSentence τ) = θ := by
      rw [commonSetLeft_image]
      exact include_restrictFormulaOn (S ∩ T) θ hθ
    have hcomp₂ : (languageOnInclusion T).onSentence
        ((commonSetRight S T).onSentence τ).not = θ.not := by
      rw [onSentence_not, commonSetRight_image]
      exact congrArg BoundedFormula.not (include_restrictFormulaOn (S ∩ T) θ hθ)
    have hAθ : A ⊨ᵇ θ := by
      apply Theory.models_of_models_theory (T' := ({φ} : L.Theory)) _ hfirst
      intro χ hχ
      rw [Set.mem_singleton_iff.mp hχ]
      exact conjunction_models Γ₁ hΓ₁
    have hBnotθ : B ⊨ᵇ θ.not := by
      apply Theory.models_sentence_iff.mpr
      intro M
      apply (Sentence.realize_not M).mpr
      intro hθM
      have hMθ : M ⊨ ({θ} : L.Theory) := Theory.model_singleton_iff.mpr hθM
      exact (Sentence.realize_not M).mp (hsecond.realize_sentence M)
        ((conjunction_models Γ₂ hΓ₂).realize_sentence M)
    apply hi
    refine ⟨τ, ?_, ?_⟩
    · apply consequence_iff_derives.mp
      apply (consequence_inclusion_iff (languageOnInclusion S)
        (languageOnInclusion_injective S)).mp
      rwa [hcomp₁]
    · apply consequence_iff_derives.mp
      apply (consequence_inclusion_iff (languageOnInclusion T)
        (languageOnInclusion_injective T)).mp
      rwa [hcomp₂]

theorem joint_model_of_complete_common_theory (S T : Set L.Symbols)
    (T₀ : (languageOn (S ∩ T)).Theory)
    (T₁ : (languageOn S).Theory) (T₂ : (languageOn T).Theory)
    (h₀ : T₀.IsComplete) (h₁ : T₁.IsSatisfiable) (h₂ : T₂.IsSatisfiable)
    (h₀₁ : (commonSetLeft S T).onTheory T₀ ⊆ T₁)
    (h₀₂ : (commonSetRight S T).onTheory T₀ ⊆ T₂) :
    ((languageOnInclusion S).onTheory T₁ ∪
      (languageOnInclusion T).onTheory T₂).IsSatisfiable := by
  classical
  apply (arbitrary_joint_model_iff S T T₁ T₂).mpr
  apply (inseparable_iff_semantic (commonSetLeft S T) (commonSetRight S T) T₁ T₂).mpr
  rintro ⟨η, hη₁, hη₂⟩
  rcases h₀.2 η with hpos | hneg
  · have hp : T₂ ⊨ᵇ (commonSetRight S T).onSentence η :=
      consequence_iff_derives.mpr
        (derives_mono (derives_map (commonSetRight S T) (deductive_completeness hpos)) h₀₂)
    let M := h₂.some
    exact (Sentence.realize_not M).mp (hη₂.realize_sentence M) (hp.realize_sentence M)
  · have hn : T₁ ⊨ᵇ ((commonSetLeft S T).onSentence η).not := by
      have h := derives_mono
        (derives_map (commonSetLeft S T) (deductive_completeness hneg)) h₀₁
      exact consequence_iff_derives.mpr (by simpa only [onSentence_not] using h)
    let M := h₁.some
    exact (Sentence.realize_not M).mp (hn.realize_sentence M) (hη₁.realize_sentence M)

end
end Lemmatheca.MathematicalLogic.CraigInterpolation
