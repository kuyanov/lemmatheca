import Lemmatheca.ArithmeticTheories.ArithmeticTheories

open Lemmatheca.MathematicalLogic Lemmatheca.ModelTheory

/-! Numeralwise representation in the corpus's actual Robinson theory.
The finite-bound lemmas concern every model of `Q`, including nonstandard models.
-/
namespace Lemmatheca.ProofTheory.ArithmeticRepresentability

open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic
open ArithmeticTheories FirstOrderProofs

noncomputable section
universe u

def numeralTerm {α : Type*} (n : ℕ) : language.Term α :=
  (numeral n).relabel Empty.elim

def extend {α : Type*} {M : Type*} (v : α → M) (a : M) : α ⊕ Unit → M :=
  Sum.elim v (fun _ => a)

private theorem sum_elim_unit {α : Type*} {M : Type*} (v : α → M) (a : Unit → M) :
    Sum.elim v a = extend v (a ()) := by
  funext i
  cases i with
  | inl i => rfl
  | inr i => cases i; rfl

/-- The orientation follows the recursive second coordinate of addition in Q. -/
def leFormula {α : Type*} (s t : language.Term α) : language.Formula α :=
  ((addTerm (.var (.inr ())) (s.relabel Sum.inl)).equal
    (t.relabel Sum.inl)).iExs Unit

def ltFormula {α : Type*} (s t : language.Term α) : language.Formula α :=
  leFormula (succTerm s) t

def leValue (M : Type u) [language.Structure M] (a b : M) : Prop :=
  ∃ z, addValue M z a = b

theorem leValue_nat (a b : ℕ) : leValue ℕ a b ↔ a ≤ b := by
  change (∃ z, z + a = b) ↔ a ≤ b
  constructor
  · rintro ⟨z, rfl⟩
    omega
  · intro h
    exact ⟨b - a, Nat.sub_add_cancel h⟩

def boundedAll {α : Type*} (t : language.Term α)
    (φ : language.Formula (α ⊕ Unit)) : language.Formula α :=
  ((leFormula (.var (.inr ())) (t.relabel Sum.inl)).imp φ).iAlls Unit

def boundedEx {α : Type*} (t : language.Term α)
    (φ : language.Formula (α ⊕ Unit)) : language.Formula α :=
  ((leFormula (.var (.inr ())) (t.relabel Sum.inl)) ⊓ φ).iExs Unit

def graphAt {n : ℕ} {α : Type*} (φ : language.Formula (Fin n ⊕ Unit))
    (x : Fin n → language.Term α) (y : language.Term α) : language.Formula α :=
  φ.subst (Sum.elim x (fun _ => y))

def strictAll {α : Type*} (t : language.Term α)
    (φ : language.Formula (α ⊕ Unit)) : language.Formula α :=
  ((ltFormula (.var (.inr ())) (t.relabel Sum.inl)).imp φ).iAlls Unit

/-- Bounded arithmetic formulas, allowing the defined order abbreviation. -/
inductive DeltaZero : {α : Type} → language.Formula α → Prop
  | falsum {α} : DeltaZero (⊥ : language.Formula α)
  | equal {α} (s t : language.Term α) : DeltaZero (s.equal t)
  | le {α} (s t : language.Term α) : DeltaZero (leFormula s t)
  | imp {α} {φ ψ : language.Formula α} :
      DeltaZero φ → DeltaZero ψ → DeltaZero (φ.imp ψ)
  | all {α} (t : language.Term α) {φ : language.Formula (α ⊕ Unit)} :
      DeltaZero φ → DeltaZero (boundedAll t φ)
  | ex {α} (t : language.Term α) {φ : language.Formula (α ⊕ Unit)} :
      DeltaZero φ → DeltaZero (boundedEx t φ)

def numeralInstance {α : Type*} (φ : language.Formula α) (v : α → ℕ) :
    language.Sentence := φ.subst (fun i => numeral (v i))

def specializeInputs {n : ℕ} (φ : language.Formula (Fin n ⊕ Unit))
    (x : Fin n → ℕ) : language.Formula Unit :=
  φ.subst (Sum.elim (fun i => numeralTerm (x i)) Term.var)

def outputIdentity {n : ℕ} (φ : language.Formula (Fin n ⊕ Unit))
    (x : Fin n → ℕ) (b : ℕ) : language.Sentence :=
  (((specializeInputs φ x).iff ((Term.var ()).equal (numeralTerm b))).relabel
    (Sum.inr : Unit → Empty ⊕ Unit)).iAlls Unit

/-- A single formula proves the complete output identity at every numeral input. -/
def StronglyRepresents {n : ℕ} (f : (Fin n → ℕ) → ℕ)
    (φ : language.Formula (Fin n ⊕ Unit)) : Prop :=
  ∀ x, Derives Q (outputIdentity φ x (f x))

theorem realize_numeralTerm {α : Type*} {M : Type u} [language.Structure M]
    (v : α → M) (n : ℕ) : (numeralTerm n).realize v = numeralValue M n := by
  simp only [numeralTerm, Term.realize_relabel, numeralValue]
  congr 1
  funext i
  exact i.elim

theorem realize_leFormula {α : Type*} {M : Type u} [language.Structure M]
    (v : α → M) (s t : language.Term α) :
    (leFormula s t).Realize v ↔ leValue M (s.realize v) (t.realize v) := by
  simp only [leFormula, Formula.realize_iExs, Formula.realize_equal,
    realize_addTerm, Term.realize_var, Term.realize_relabel, Function.comp_def,
    Sum.elim_inl, Sum.elim_inr, leValue]
  exact ⟨fun ⟨z, hz⟩ => ⟨z (), hz⟩, fun ⟨z, hz⟩ => ⟨fun _ => z, hz⟩⟩

theorem realize_boundedAll {α : Type*} {M : Type u} [language.Structure M]
    (v : α → M) (t : language.Term α) (φ : language.Formula (α ⊕ Unit)) :
    (boundedAll t φ).Realize v ↔
      ∀ a : M, leValue M a (t.realize v) → φ.Realize (extend v a) := by
  simp only [boundedAll, Formula.realize_iAlls, Formula.realize_imp, realize_leFormula,
    Term.realize_var, Term.realize_relabel, Function.comp_def, Sum.elim_inl, Sum.elim_inr]
  constructor
  · intro h a ha
    exact h (fun _ => a) ha
  · intro h a ha
    rw [sum_elim_unit]
    exact h (a ()) ha

theorem realize_boundedEx {α : Type*} {M : Type u} [language.Structure M]
    (v : α → M) (t : language.Term α) (φ : language.Formula (α ⊕ Unit)) :
    (boundedEx t φ).Realize v ↔
      ∃ a : M, leValue M a (t.realize v) ∧ φ.Realize (extend v a) := by
  simp only [boundedEx, Formula.realize_iExs, Formula.realize_inf, realize_leFormula,
    Term.realize_var, Term.realize_relabel, Function.comp_def, Sum.elim_inl, Sum.elim_inr]
  constructor
  · rintro ⟨a, ha, hφ⟩
    rw [sum_elim_unit] at hφ
    exact ⟨a (), ha, hφ⟩
  · rintro ⟨a, ha, hφ⟩
    exact ⟨fun _ => a, ha, hφ⟩

theorem finite_bound {M : Type u} [language.Structure M] [M ⊨ Q]
    (a : M) (n : ℕ) :
    leValue M a (numeralValue M n) ↔ ∃ m ≤ n, a = numeralValue M m := by
  have hQ := (model_Q_iff M).mp ‹M ⊨ Q›
  constructor
  · induction n generalizing a with
    | zero =>
      rintro ⟨z, hz⟩
      by_cases ha : a = zeroValue M
      · exact ⟨0, le_rfl, by simpa only [numeral_value_zero] using ha⟩
      · obtain ⟨b, rfl⟩ := hQ.2.2.1 a ha
        rw [hQ.2.2.2.2.1] at hz
        exact (hQ.1 _ (by simpa only [numeral_value_zero] using hz)).elim
    | succ n ih =>
      rintro ⟨z, hz⟩
      by_cases ha : a = zeroValue M
      · exact ⟨0, Nat.zero_le _, by simpa only [numeral_value_zero] using ha⟩
      · obtain ⟨b, rfl⟩ := hQ.2.2.1 a ha
        rw [hQ.2.2.2.2.1, numeral_value_succ] at hz
        obtain ⟨m, hm, hb⟩ := ih b ⟨z, hQ.2.1 hz⟩
        exact ⟨m + 1, Nat.succ_le_succ hm, congrArg (succValue M) hb⟩
  · rintro ⟨m, hm, rfl⟩
    exact ⟨numeralValue M (n - m), by rw [numeral_add, Nat.sub_add_cancel hm]⟩

theorem numeral_cut {M : Type u} [language.Structure M] [M ⊨ Q]
    (a : M) (n : ℕ) :
    (∃ m ≤ n, a = numeralValue M m) ∨ leValue M (numeralValue M (n + 1)) a := by
  have hQ := (model_Q_iff M).mp ‹M ⊨ Q›
  induction n generalizing a with
  | zero =>
    by_cases ha : a = zeroValue M
    · exact Or.inl ⟨0, le_rfl, by simpa only [numeral_value_zero] using ha⟩
    · obtain ⟨b, rfl⟩ := hQ.2.2.1 a ha
      right
      refine ⟨b, ?_⟩
      rw [numeral_value_succ, numeral_value_zero, hQ.2.2.2.2.1, hQ.2.2.2.1]
  | succ n ih =>
    by_cases ha : a = zeroValue M
    · exact Or.inl ⟨0, Nat.zero_le _, by simpa only [numeral_value_zero] using ha⟩
    · obtain ⟨b, rfl⟩ := hQ.2.2.1 a ha
      rcases ih b with ⟨m, hm, hb⟩ | ⟨z, hz⟩
      · exact Or.inl ⟨m + 1, Nat.succ_le_succ hm, congrArg (succValue M) hb⟩
      · right
        exact ⟨z, by rw [numeral_value_succ, hQ.2.2.2.2.1, hz]⟩

theorem term_numeral_value {α : Type*} {M : Type u} [language.Structure M] [M ⊨ Q]
    (t : language.Term α) (v : α → ℕ) :
    t.realize (fun i => numeralValue M (v i)) = numeralValue M (t.realize v) := by
  obtain ⟨e, he⟩ := standard_embedding M
  have h := HomClass.realize_term e (t := t) (v := v)
  have hv : e ∘ v = fun i => numeralValue M (v i) := funext fun i => he (v i)
  rw [hv, he] at h
  exact h

theorem extend_numerals {α : Type*} {M : Type u} [language.Structure M]
    (v : α → ℕ) (a : ℕ) :
    extend (fun i => numeralValue M (v i)) (numeralValue M a) =
      fun i => numeralValue M (extend v a i) := by
  funext i
  cases i <;> rfl

theorem deltaZero_absolute {α : Type} {M : Type u} [language.Structure M] [M ⊨ Q]
    {φ : language.Formula α} (hφ : DeltaZero φ) (v : α → ℕ) :
    φ.Realize (fun i => numeralValue M (v i)) ↔ φ.Realize v := by
  induction hφ with
  | falsum => simp only [Formula.realize_bot]
  | equal s t =>
    simp only [Formula.realize_equal, term_numeral_value]
    exact (numeral_injective M).eq_iff
  | le s t =>
    simp only [realize_leFormula, term_numeral_value, finite_bound, leValue_nat]
    constructor
    · rintro ⟨m, hm, he⟩
      exact ((numeral_injective M) he).symm ▸ hm
    · intro h
      exact ⟨s.realize v, h, rfl⟩
  | imp _ _ ihφ ihψ =>
    simp only [Formula.realize_imp, ihφ, ihψ]
  | all t _ ih =>
    simp only [realize_boundedAll, term_numeral_value, leValue_nat]
    constructor
    · intro h a ha
      have hφ := h (numeralValue M a) ((finite_bound _ _).mpr ⟨a, ha, rfl⟩)
      rw [extend_numerals] at hφ
      exact (ih (extend v a)).mp hφ
    · intro h a ha
      obtain ⟨m, hm, rfl⟩ := (finite_bound a _).mp ha
      rw [extend_numerals]
      exact (ih (extend v m)).mpr (h m hm)
  | ex t _ ih =>
    simp only [realize_boundedEx, term_numeral_value, leValue_nat]
    constructor
    · rintro ⟨a, ha, hφ⟩
      obtain ⟨m, hm, rfl⟩ := (finite_bound a _).mp ha
      rw [extend_numerals] at hφ
      exact ⟨m, hm, (ih (extend v m)).mp hφ⟩
    · rintro ⟨a, ha, hφ⟩
      refine ⟨numeralValue M a, (finite_bound _ _).mpr ⟨a, ha, rfl⟩, ?_⟩
      rw [extend_numerals]
      exact (ih (extend v a)).mpr hφ

theorem deltaZero_complete {α : Type} {φ : language.Formula α}
    (hφ : DeltaZero φ) (v : α → ℕ) (h : φ.Realize v) :
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
  exact (deltaZero_absolute hφ v).mpr h

theorem deltaZero_refute {α : Type} {φ : language.Formula α}
    (hφ : DeltaZero φ) (v : α → ℕ) (h : ¬ φ.Realize v) :
    Derives Q (numeralInstance φ v).not := by
  have hp := deltaZero_complete (DeltaZero.imp hφ DeltaZero.falsum) v h
  exact hp

theorem sigmaOne_complete {k : ℕ} {φ : language.Formula (Empty ⊕ Fin k)}
    (hφ : DeltaZero φ) (h : ℕ ⊨ φ.iExs (Fin k)) : Derives Q (φ.iExs (Fin k)) := by
  obtain ⟨a, ha⟩ := (Formula.realize_iExs.mp h)
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
  have habs := (deltaZero_absolute (M := M) hφ (Sum.elim Empty.elim a)).mpr ha'
  convert habs using 1
  funext i
  cases i with
  | inl i => exact i.elim
  | inr i => rfl

theorem realize_specializeInputs {n : ℕ} {M : Type u} [language.Structure M]
    (φ : language.Formula (Fin n ⊕ Unit)) (x : Fin n → ℕ) (v : Unit → M) :
    (specializeInputs φ x).Realize v ↔
      φ.Realize (extend (fun i => numeralValue M (x i)) (v ())) := by
  have hv : (fun i => (Sum.elim (fun j => numeralTerm (x j)) Term.var i).realize v) =
      extend (fun i => numeralValue M (x i)) (v ()) := by
    funext i
    cases i with
    | inl i => exact realize_numeralTerm v (x i)
    | inr i => cases i; rfl
  simp only [specializeInputs, Formula.Realize, BoundedFormula.realize_subst, hv]

theorem realize_outputIdentity {n : ℕ} {M : Type u} [language.Structure M]
    (φ : language.Formula (Fin n ⊕ Unit)) (x : Fin n → ℕ) (b : ℕ) :
    M ⊨ outputIdentity φ x b ↔
      ∀ y : M, φ.Realize (extend (fun i => numeralValue M (x i)) y) ↔
        y = numeralValue M b := by
  simp only [outputIdentity, Sentence.Realize, Formula.realize_iAlls,
    Formula.realize_relabel, Function.comp_def, Sum.elim_inr, Formula.realize_iff,
    realize_specializeInputs, Formula.realize_equal, Term.realize_var, realize_numeralTerm]
  exact ⟨fun h y => h (fun _ => y), fun h a => h (a ())⟩

theorem stronglyRepresents_of_modelwise {n : ℕ} (f : (Fin n → ℕ) → ℕ)
    (φ : language.Formula (Fin n ⊕ Unit))
    (h : ∀ (M : Theory.ModelType.{0, 0, 0} Q) (x : Fin n → ℕ) (y : M),
      φ.Realize (extend (fun i => numeralValue M (x i)) y) ↔
        y = numeralValue M (f x)) : StronglyRepresents f φ := by
  intro x
  apply HenkinCompleteness.deductive_completeness
  apply Theory.models_sentence_iff.mpr
  intro M
  exact (realize_outputIdentity φ x (f x)).mpr (h M x)

theorem stronglyRepresents_modelwise {n : ℕ} {M : Type u} [language.Structure M]
    [Nonempty M] [M ⊨ Q] {f : (Fin n → ℕ) → ℕ}
    {φ : language.Formula (Fin n ⊕ Unit)} (h : StronglyRepresents f φ)
    (x : Fin n → ℕ) (y : M) :
    φ.Realize (extend (fun i => numeralValue M (x i)) y) ↔
      y = numeralValue M (f x) := by
  have hp : M ⊨ outputIdentity φ x (f x) :=
    derives_sound (h x) default (fun B hB => Theory.realize_sentence_of_mem Q hB)
  exact (realize_outputIdentity φ x (f x)).mp hp y

end
end Lemmatheca.ProofTheory.ArithmeticRepresentability
