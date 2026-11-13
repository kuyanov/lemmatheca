import Lemmatheca.GlivenkosPropositionalTheorem.Semantics
import Lemmatheca.PropositionalNegativeTranslation.Translation

namespace Lemmatheca.ProofTheory.Intuitionistic.Glivenko

open Lemmatheca.MathematicalLogic.Propositional
open PropFormula
open NegativeTranslation

/-- Stable theorem conclusions transfer without an additional classical rule. -/
theorem stable_theorem_iff (A : PropFormula ℕ) (hA : Stable A) :
    Lemmatheca.MathematicalLogic.Propositional.Derives ∅ A ↔ Derives ∅ A := by
  constructor
  · intro h
    exact .implElim hA ((glivenko A).mp h)
  · intro h
    apply (theorem_iff_tautology A).mpr
    intro b
    exact boolean_sound h b (by simp)

/-- An arbitrary antecedent is allowed when the implication's consequent is stable. -/
theorem stable_implication_transfer (A B : PropFormula ℕ) (hB : Stable B)
    (h : Lemmatheca.MathematicalLogic.Propositional.Derives ∅ (impl A B)) :
    Derives ∅ (impl A B) := by
  exact (stable_theorem_iff _ (stable_impl A hB)).mp h

/-- The two specified native formulas have closed intuitionistic implications in both directions. -/
theorem negative_double_negation (A : PropFormula ℕ) :
    Equivalent (negative A) (neg (neg A)) := by
  constructor
  · apply stable_implication_transfer _ _ (stable_neg (neg A))
    apply (theorem_iff_tautology _).mpr
    intro b
    simp [Satisfies, eval, negative_eval]
  · apply stable_implication_transfer _ _ (negative_stable A)
    apply (theorem_iff_tautology _).mpr
    intro b
    simp [Satisfies, eval, negative_eval]

theorem negative_introduction (A : PropFormula ℕ) :
    Derives ∅ (impl A (negative A)) := by
  apply Derives.implIntro
  exact .implElim ((negative_double_negation A).2.weaken (Set.empty_subset _))
    (.implElim ((double_negation_intro A).weaken (Set.empty_subset _))
      (.assumption (by simp)))

theorem negative_removal_iff_stable (A : PropFormula ℕ) :
    Derives ∅ (impl (negative A) A) ↔ Stable A := by
  constructor
  · intro h
    apply Derives.implIntro
    exact .implElim (h.weaken (Set.empty_subset _))
      (.implElim ((negative_double_negation A).2.weaken (Set.empty_subset _))
        (.assumption (by simp)))
  · intro h
    apply Derives.implIntro
    exact .implElim (h.weaken (Set.empty_subset _))
      (.implElim ((negative_double_negation A).1.weaken (Set.empty_subset _))
        (.assumption (by simp)))

theorem negative_fixed_iff_stable (A : PropFormula ℕ) :
    Equivalent A (negative A) ↔ Stable A := by
  constructor
  · intro h
    exact (negative_removal_iff_stable A).mp h.2
  · intro h
    exact ⟨negative_introduction A, (negative_removal_iff_stable A).mpr h⟩

/-- The actual sufficient grammar: arbitrary negations and antecedents, but no atom/disjunction case. -/
inductive Negative : PropFormula ℕ → Prop
  | falsum : Negative falsum
  | neg (A) : Negative (neg A)
  | conj {A B} : Negative A → Negative B → Negative (conj A B)
  | impl (A) {B} : Negative B → Negative (impl A B)

theorem negative_fragment_stable {A : PropFormula ℕ} (h : Negative A) : Stable A := by
  induction h with
  | falsum => exact stable_falsum
  | neg A => exact stable_neg A
  | conj _ _ ihA ihB => exact stable_conj ihA ihB
  | impl A _ ihB => exact stable_impl A ihB

theorem translation_in_negative_fragment (A : PropFormula ℕ) : Negative (negative A) := by
  induction A with
  | atom p => exact .neg (neg (atom p))
  | falsum => exact .falsum
  | neg A _ => exact .neg (negative A)
  | conj A B ihA ihB => exact .conj ihA ihB
  | disj A B _ _ => exact .neg (neg (disj (negative A) (negative B)))
  | impl A B _ ihB => exact .impl (negative A) ihB

theorem negative_fragment_fixed {A : PropFormula ℕ} (h : Negative A) :
    Equivalent A (negative A) := by
  exact (negative_fixed_iff_stable A).mpr (negative_fragment_stable h)

end Lemmatheca.ProofTheory.Intuitionistic.Glivenko
