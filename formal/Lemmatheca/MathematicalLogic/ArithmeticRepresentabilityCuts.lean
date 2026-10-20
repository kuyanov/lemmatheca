import Lemmatheca.MathematicalLogic.ArithmeticRepresentabilityBeta

/-! Closed Q derivations for the finite numeral cuts. The finite disjunctions
are actual formulas in the shared syntax, and the only induction is external
induction in the modelwise lemmas used before applying completeness. -/
namespace Lemmatheca.MathematicalLogic.ArithmeticRepresentability
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic ArithmeticTheories FirstOrderProofs
noncomputable section
universe u

/-- The disjunction of the first `k` numeral equalities; at `k = 0` it is false. -/
def numeralCases (k : ℕ) : language.Formula (Fin 1) :=
  Formula.iSup (fun i : Fin k => (Term.var (0 : Fin 1)).equal (numeralTerm i.val))

theorem realize_numeralCases {M : Type u} [language.Structure M]
    (k : ℕ) (v : Fin 1 → M) :
    (numeralCases k).Realize v ↔ ∃ m < k, v 0 = numeralValue M m := by
  simp only [numeralCases, Formula.realize_iSup, Formula.realize_equal,
    Term.realize_var, realize_numeralTerm]
  exact ⟨fun ⟨i, hi⟩ => ⟨i.val, i.isLt, hi⟩,
    fun ⟨m, hm, he⟩ => ⟨⟨m, hm⟩, he⟩⟩

def inclusiveCutSentence (n : ℕ) : language.Sentence :=
  close ((leFormula (.var 0) (numeralTerm n)).iff (numeralCases (n + 1)))

def strictCutSentence (n : ℕ) : language.Sentence :=
  close ((ltFormula (.var 0) (numeralTerm n)).iff (numeralCases n))

def numeralCutSentence (n : ℕ) : language.Sentence :=
  close ((numeralCases (n + 1)) ⊔ ltFormula (numeralTerm n) (.var 0))

/-- For each external numeral bound, Q proves its complete inclusive cut. -/
theorem finite_bound_derives (n : ℕ) : Derives Q (inclusiveCutSentence n) := by
  apply HenkinCompleteness.deductive_completeness
  apply Theory.models_sentence_iff.mpr
  intro M
  rw [inclusiveCutSentence, realize_close]
  intro v
  rw [Formula.realize_iff, realize_leFormula, Term.realize_var,
    realize_numeralTerm, realize_numeralCases, finite_bound]
  constructor
  · rintro ⟨m, hm, he⟩
    exact ⟨m, by omega, he⟩
  · rintro ⟨m, hm, he⟩
    exact ⟨m, by omega, he⟩

/-- This includes the empty cut below zero, as an actual closed Q theorem. -/
theorem strict_finite_bound_derives (n : ℕ) : Derives Q (strictCutSentence n) := by
  apply HenkinCompleteness.deductive_completeness
  apply Theory.models_sentence_iff.mpr
  intro M
  rw [strictCutSentence, realize_close]
  intro v
  rw [Formula.realize_iff, ltFormula, realize_leFormula, realize_succTerm,
    Term.realize_var, realize_numeralTerm, realize_numeralCases]
  exact strict_finite_bound (v 0) n

/-- Q also proves that an arbitrary element lies in the finite cut or strictly
above its endpoint, using the specified orientation of the order abbreviation. -/
theorem numeral_cut_derives (n : ℕ) : Derives Q (numeralCutSentence n) := by
  apply HenkinCompleteness.deductive_completeness
  apply Theory.models_sentence_iff.mpr
  intro M
  rw [numeralCutSentence, realize_close]
  intro v
  rw [Formula.realize_sup, realize_numeralCases, ltFormula, realize_leFormula,
    realize_succTerm, realize_numeralTerm, Term.realize_var]
  rcases numeral_cut (v 0) n with ⟨m, hm, he⟩ | h
  · exact Or.inl ⟨m, by omega, he⟩
  · exact Or.inr ((numeral_value_succ M n) ▸ h)

end
end Lemmatheca.MathematicalLogic.ArithmeticRepresentability
