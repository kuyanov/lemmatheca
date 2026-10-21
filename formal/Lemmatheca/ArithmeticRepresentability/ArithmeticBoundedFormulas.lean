import Lemmatheca.ArithmeticRepresentability.ArithmeticRepresentabilityClosure
import Lemmatheca.ArithmeticRepresentability.ArithmeticFormulaSubstitution

open Lemmatheca.MathematicalLogic Lemmatheca.ModelTheory

/-! The full bounded arithmetic grammar, including literal strict bounded
quantifiers. The older `DeltaZero` grammar is its inclusive-bound compilation
core; strict quantification is not silently identified with that syntax. -/
namespace Lemmatheca.ProofTheory.ArithmeticRepresentability
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic ArithmeticTheories FirstOrderProofs
noncomputable section
universe u

private theorem successor_nat (a : ℕ) : succValue ℕ a = a + 1 := rfl

def strictEx {α : Type*} (t : language.Term α)
    (φ : language.Formula (α ⊕ Unit)) : language.Formula α :=
  ((ltFormula (.var (.inr ())) (t.relabel Sum.inl)) ⊓ φ).iExs Unit

theorem realize_strictEx {α : Type*} {M : Type u} [language.Structure M]
    (v : α → M) (t : language.Term α) (φ : language.Formula (α ⊕ Unit)) :
    (strictEx t φ).Realize v ↔
      ∃ a : M, leValue M (succValue M a) (t.realize v) ∧ φ.Realize (extend v a) := by
  simp only [strictEx, Formula.realize_iExs, Formula.realize_inf, ltFormula,
    realize_leFormula, realize_succTerm, Term.realize_var, Term.realize_relabel,
    Function.comp_def, Sum.elim_inl, Sum.elim_inr]
  constructor
  · rintro ⟨a, ha, hφ⟩
    refine ⟨a (), ha, ?_⟩
    convert hφ using 1
    funext i
    cases i <;> rfl
  · rintro ⟨a, ha, hφ⟩
    exact ⟨fun _ => a, ha, hφ⟩

/-- Bounded formulas in the shared arithmetic syntax. Both strict and inclusive
quantifiers retain their literal ordinary first-order expansions. -/
inductive BoundedArithmetic : {α : Type} → language.Formula α → Prop
  | core {α} {φ : language.Formula α} : DeltaZero φ → BoundedArithmetic φ
  | imp {α} {φ ψ : language.Formula α} :
      BoundedArithmetic φ → BoundedArithmetic ψ → BoundedArithmetic (φ.imp ψ)
  | all {α} (t : language.Term α) {φ : language.Formula (α ⊕ Unit)} :
      BoundedArithmetic φ → BoundedArithmetic (boundedAll t φ)
  | ex {α} (t : language.Term α) {φ : language.Formula (α ⊕ Unit)} :
      BoundedArithmetic φ → BoundedArithmetic (boundedEx t φ)
  | strictAll {α} (t : language.Term α) {φ : language.Formula (α ⊕ Unit)} :
      BoundedArithmetic φ → BoundedArithmetic (ArithmeticRepresentability.strictAll t φ)
  | strictEx {α} (t : language.Term α) {φ : language.Formula (α ⊕ Unit)} :
      BoundedArithmetic φ → BoundedArithmetic (ArithmeticRepresentability.strictEx t φ)

@[simp] theorem subst_strictAll {α β : Type*} (σ : α → language.Term β)
    (t : language.Term α) (φ : language.Formula (α ⊕ Unit)) :
    (strictAll t φ).subst σ = strictAll (t.subst σ) (φ.subst (underSubst σ)) := by
  unfold strictAll
  rw [subst_iAlls]
  congr 1
  simp only [formula_subst_imp, ltFormula, subst_leFormula, subst_succTerm,
    Term.subst, underSubst, Sum.elim_inr, term_subst_relabel, Sum.elim_inl,
    term_relabel_subst]

@[simp] theorem subst_strictEx {α β : Type*} (σ : α → language.Term β)
    (t : language.Term α) (φ : language.Formula (α ⊕ Unit)) :
    (strictEx t φ).subst σ = strictEx (t.subst σ) (φ.subst (underSubst σ)) := by
  unfold strictEx
  rw [subst_iExs]
  congr 1
  simp only [formula_subst_inf, ltFormula, subst_leFormula, subst_succTerm,
    Term.subst, underSubst, Sum.elim_inr, term_subst_relabel, Sum.elim_inl,
    term_relabel_subst]

/-- Substitution preserves the literal full bounded grammar, including strict bounds. -/
theorem BoundedArithmetic.subst {α β : Type} {φ : language.Formula α}
    (hφ : BoundedArithmetic φ) (σ : α → language.Term β) :
    BoundedArithmetic (φ.subst σ) := by
  induction hφ generalizing β with
  | core h => exact .core (h.subst σ)
  | imp _ _ ihφ ihψ => exact .imp (ihφ σ) (ihψ σ)
  | all t _ ih =>
      simpa only [subst_boundedAll] using BoundedArithmetic.all (t.subst σ) (ih (underSubst σ))
  | ex t _ ih =>
      simpa only [subst_boundedEx] using BoundedArithmetic.ex (t.subst σ) (ih (underSubst σ))
  | strictAll t _ ih =>
      simpa only [subst_strictAll] using BoundedArithmetic.strictAll (t.subst σ) (ih (underSubst σ))
  | strictEx t _ ih =>
      simpa only [subst_strictEx] using BoundedArithmetic.strictEx (t.subst σ) (ih (underSubst σ))

theorem BoundedArithmetic.relabel {α β : Type} {φ : language.Formula α}
    (hφ : BoundedArithmetic φ) (f : α → β) : BoundedArithmetic (φ.relabel f) := by
  rw [← formula_subst_vars]
  exact hφ.subst (fun x => .var (f x))

/-- Literal existential-prefix syntax with the full bounded grammar. -/
def BoundedSigmaOne {α : Type} (A : language.Formula α) : Prop :=
  ∃ k : ℕ, ∃ D : language.Formula (α ⊕ Fin k),
    BoundedArithmetic D ∧ A = D.iExs (Fin k)

/-- Standard finite cuts, rather than induction in Q, justify strict bounds too. -/
theorem boundedArithmetic_absolute {α : Type} {M : Type u} [language.Structure M] [M ⊨ Q]
    {φ : language.Formula α} (hφ : BoundedArithmetic φ) (v : α → ℕ) :
    φ.Realize (fun i => numeralValue M (v i)) ↔ φ.Realize v := by
  induction hφ with
  | core h => exact deltaZero_absolute h v
  | imp _ _ ihφ ihψ => simp only [Formula.realize_imp, ihφ, ihψ]
  | all t _ ih =>
    simp only [realize_boundedAll, term_numeral_value, leValue_nat]
    constructor
    · intro h a ha
      have hh := h (numeralValue M a) ((finite_bound _ _).mpr ⟨a, ha, rfl⟩)
      rw [extend_numerals] at hh
      exact (ih (extend v a)).mp hh
    · intro h a ha
      obtain ⟨m, hm, rfl⟩ := (finite_bound a _).mp ha
      rw [extend_numerals]
      exact (ih (extend v m)).mpr (h m hm)
  | ex t _ ih =>
    simp only [realize_boundedEx, term_numeral_value, leValue_nat]
    constructor
    · rintro ⟨a, ha, hh⟩
      obtain ⟨m, hm, rfl⟩ := (finite_bound a _).mp ha
      rw [extend_numerals] at hh
      exact ⟨m, hm, (ih (extend v m)).mp hh⟩
    · rintro ⟨a, ha, hh⟩
      refine ⟨numeralValue M a, (finite_bound _ _).mpr ⟨a, ha, rfl⟩, ?_⟩
      rw [extend_numerals]
      exact (ih (extend v a)).mpr hh
  | strictAll t _ ih =>
    simp only [realize_strictAll, term_numeral_value, leValue_nat, successor_nat]
    constructor
    · intro h a ha
      have hh := h (numeralValue M a) ((strict_finite_bound _ _).mpr ⟨a, by omega, rfl⟩)
      rw [extend_numerals] at hh
      exact (ih (extend v a)).mp hh
    · intro h a ha
      obtain ⟨m, hm, rfl⟩ := (strict_finite_bound a _).mp ha
      rw [extend_numerals]
      exact (ih (extend v m)).mpr (h m (by omega))
  | strictEx t _ ih =>
    simp only [realize_strictEx, term_numeral_value, leValue_nat, successor_nat]
    constructor
    · rintro ⟨a, ha, hh⟩
      obtain ⟨m, hm, rfl⟩ := (strict_finite_bound a _).mp ha
      rw [extend_numerals] at hh
      exact ⟨m, by omega, (ih (extend v m)).mp hh⟩
    · rintro ⟨a, ha, hh⟩
      refine ⟨numeralValue M a, (strict_finite_bound _ _).mpr ⟨a, by omega, rfl⟩, ?_⟩
      rw [extend_numerals]
      exact (ih (extend v a)).mpr hh

theorem boundedArithmetic_complete {α : Type} {φ : language.Formula α}
    (hφ : BoundedArithmetic φ) (v : α → ℕ) (h : φ.Realize v) :
    Derives Q (numeralInstance φ v) := by
  apply HenkinCompleteness.deductive_completeness
  apply Theory.models_sentence_iff.mpr
  intro M
  simp only [numeralInstance, Sentence.Realize, Formula.Realize, BoundedFormula.realize_subst]
  have hv : (fun i => (numeral (v i)).realize (default : Empty → M)) =
      fun i => numeralValue M (v i) := by
    funext i
    unfold numeralValue
    congr 1
    funext e
    exact e.elim
  rw [hv]
  exact (boundedArithmetic_absolute hφ v).mpr h

theorem boundedArithmetic_refute {α : Type} {φ : language.Formula α}
    (hφ : BoundedArithmetic φ) (v : α → ℕ) (h : ¬φ.Realize v) :
    Derives Q (numeralInstance φ v).not :=
  boundedArithmetic_complete (.imp hφ (.core .falsum)) v h

theorem boundedSigmaOne_complete {k : ℕ} {φ : language.Formula (Empty ⊕ Fin k)}
    (hφ : BoundedArithmetic φ) (h : ℕ ⊨ φ.iExs (Fin k)) :
    Derives Q (φ.iExs (Fin k)) := by
  obtain ⟨a, ha⟩ := Formula.realize_iExs.mp h
  apply HenkinCompleteness.deductive_completeness
  apply Theory.models_sentence_iff.mpr
  intro M
  apply Formula.realize_iExs.mpr
  refine ⟨fun i => numeralValue M (a i), ?_⟩
  have ha' : φ.Realize (Sum.elim Empty.elim a) := by
    convert ha using 1
    funext i
    cases i with
    | inl i => exact i.elim
    | inr i => rfl
  have habs := (boundedArithmetic_absolute (M := M) hφ (Sum.elim Empty.elim a)).mpr ha'
  convert habs using 1
  funext i
  cases i with
  | inl i => exact i.elim
  | inr i => rfl

end
end Lemmatheca.ProofTheory.ArithmeticRepresentability
