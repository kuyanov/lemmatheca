import Lemmatheca.PropositionalFriedmanTranslation.Proofs
import Lemmatheca.IntuitionisticKripkeSemantics.Examples

namespace Lemmatheca.Entry.PropositionalFriedmanTranslation

open Lemmatheca.MathematicalLogic.Propositional
open PropFormula
open Lemmatheca.ProofTheory.Intuitionistic
open Lemmatheca.ProofTheory.Intuitionistic.FriedmanTranslation
open Lemmatheca.ProofTheory.Intuitionistic.Kripke
open Lemmatheca.Entry.IntuitionisticKripkeSemantics

universe u
variable {α : Type u}

private theorem disjunction_fold (p : α) :
    Lemmatheca.ProofTheory.Intuitionistic.Derives ∅
      (impl (disj (atom p) (atom p)) (atom p)) := by
  apply Lemmatheca.ProofTheory.Intuitionistic.Derives.implIntro
  exact .disjElim (A := atom p) (B := atom p) (.assumption (by simp)) (.assumption (by simp))
    (.assumption (by simp))

theorem translated_double_negation (p : α) :
    formula (atom p) (neg (neg (atom p))) =
      impl (impl (disj (atom p) (atom p)) (atom p)) (atom p) := by
  rfl

theorem translated_double_negation_equivalent (p : α) :
    NegativeTranslation.Equivalent (formula (atom p) (neg (neg (atom p)))) (atom p) := by
  change NegativeTranslation.Equivalent
    (impl (impl (disj (atom p) (atom p)) (atom p)) (atom p)) (atom p)
  constructor
  · apply Lemmatheca.ProofTheory.Intuitionistic.Derives.implIntro
    exact .implElim (.assumption (by simp))
      ((disjunction_fold p).weaken (Set.empty_subset _))
  · exact .implIntro (.implIntro (.assumption (by simp)))

theorem unchanged_premise_countermodel (p : α) :
    Countermodel (chainModel p) false {neg (neg (atom p))}
      (formula (atom p) (neg (neg (atom p)))) := by
  constructor
  · intro A hA
    obtain rfl := Set.mem_singleton_iff.mp hA
    exact (chain_values p).2.2
  · intro h
    have hfold : Forces (chainModel p) false (impl (disj (atom p) (atom p)) (atom p)) := by
      intro _ _ hp
      exact hp.elim id id
    exact (chain_values p).1 (h false le_rfl hfold)

theorem unchanged_premise_not_derivable (p : α) :
    ¬ Lemmatheca.ProofTheory.Intuitionistic.Derives {neg (neg (atom p))} (formula (atom p) (neg (neg (atom p)))) := by
  exact countermodel_not_derivable _ _ _ _ (unchanged_premise_countermodel p)

theorem chain_upper_values (p : α) :
    Forces (chainModel p) true (atom p) ∧
      ¬ Forces (chainModel p) true (neg (atom p)) ∧
      Forces (chainModel p) true (neg (neg (atom p))) := by
  refine ⟨⟨rfl, rfl⟩, ?_, ?_⟩
  · intro hn
    exact hn true le_rfl ⟨rfl, rfl⟩
  · intro z _ hn
    exact hn true (by cases z <;> decide) ⟨rfl, rfl⟩

/-- Literal falsum replacement, with atoms and every other constructor unchanged. -/
def bottomOnly (R : PropFormula α) : PropFormula α → PropFormula α
  | .atom p => .atom p
  | .falsum => R
  | .neg A => .neg (bottomOnly R A)
  | .conj A B => .conj (bottomOnly R A) (bottomOnly R B)
  | .disj A B => .disj (bottomOnly R A) (bottomOnly R B)
  | .impl A B => .impl (bottomOnly R A) (bottomOnly R B)

/-- The valuation forcing the chosen parameter atom and no other atom. -/
def separatingValuation [DecidableEq α] (q : α) : α → Bool := fun a => decide (a = q)

theorem bottom_only_explosion [DecidableEq α] (p q : α) (hpq : p ≠ q) :
    Lemmatheca.ProofTheory.Intuitionistic.Derives ∅ (impl falsum (atom p)) ∧
      bottomOnly (atom q) (impl falsum (atom p)) = impl (atom q) (atom p) ∧
      eval (separatingValuation q) (impl (atom q) (atom p)) = false ∧
      ¬ Lemmatheca.ProofTheory.Intuitionistic.Derives ∅ (bottomOnly (atom q) (impl falsum (atom p))) := by
  have hvalue : eval (separatingValuation q) (impl (atom q) (atom p)) = false := by
    simp [eval, separatingValuation, hpq]
  refine ⟨.implIntro (.falsumElim (.assumption (by simp))), rfl, hvalue, ?_⟩
  intro h
  have hs := boolean_sound h (separatingValuation q) (by simp)
  change eval (separatingValuation q) (impl (atom q) (atom p)) = true at hs
  rw [hvalue] at hs
  contradiction

theorem translated_explosion (R : PropFormula α) (p : α) :
    formula R (impl falsum (atom p)) = impl R (disj (atom p) R) ∧
      Lemmatheca.ProofTheory.Intuitionistic.Derives ∅ (formula R (impl falsum (atom p))) := by
  constructor
  · rfl
  · change Lemmatheca.ProofTheory.Intuitionistic.Derives ∅ (impl R (disj (atom p) R))
    exact .implIntro (.disjIntroRight (.assumption (by simp)))

/-- Replace the first named atom by the double negation of the second and fix all others. -/
def counterSubstitution [DecidableEq α] (p q : α) : α → PropFormula α :=
  fun a => if a = p then neg (neg (atom q)) else atom a

theorem substitution_formulas [DecidableEq α] (p q : α) (hpq : p ≠ q) :
    subst (counterSubstitution p q) (atom q) = atom q ∧
      subst (counterSubstitution p q) (formula (atom q) (atom p)) =
        disj (neg (neg (atom q))) (atom q) ∧
      formula (subst (counterSubstitution p q) (atom q))
          (subst (counterSubstitution p q) (atom p)) =
        impl (impl (disj (atom q) (atom q)) (atom q)) (atom q) := by
  simp [counterSubstitution, subst, formula, Ne.symm hpq]

theorem substitution_countermodel [DecidableEq α] (p q : α) (hpq : p ≠ q) :
    Countermodel (chainModel q) false
      {subst (counterSubstitution p q) (formula (atom q) (atom p))}
      (formula (subst (counterSubstitution p q) (atom q))
        (subst (counterSubstitution p q) (atom p))) := by
  obtain ⟨_, hleft, hright⟩ := substitution_formulas p q hpq
  rw [hleft, hright]
  constructor
  · intro A hA
    obtain rfl := Set.mem_singleton_iff.mp hA
    exact Or.inl (chain_values q).2.2
  · exact (unchanged_premise_countermodel q).2

theorem substitution_failure [DecidableEq α] (p q : α) (hpq : p ≠ q) :
    subst (counterSubstitution p q) (formula (atom q) (atom p)) ≠
        formula (subst (counterSubstitution p q) (atom q))
          (subst (counterSubstitution p q) (atom p)) ∧
      ¬ NegativeTranslation.Equivalent
        (subst (counterSubstitution p q) (formula (atom q) (atom p)))
        (formula (subst (counterSubstitution p q) (atom q))
          (subst (counterSubstitution p q) (atom p))) := by
  have hm := substitution_countermodel p q hpq
  have hl := hm.1 _ (Set.mem_singleton _)
  constructor
  · intro heq
    exact hm.2 (heq ▸ hl)
  · intro hequiv
    have hi := sound hequiv.1 (chainModel q) false (by simp [ForcesContext])
    exact hm.2 (hi false le_rfl hl)

theorem translated_negation_theorem (p : α) :
    formula (atom p) (neg (atom p)) = impl (disj (atom p) (atom p)) (atom p) ∧
      Lemmatheca.ProofTheory.Intuitionistic.Derives ∅ (formula (atom p) (neg (atom p))) := by
  exact ⟨rfl, disjunction_fold p⟩

theorem classical_comparison_countermodel (p : α) :
    Countermodel (chainModel p) false {formula (atom p) (neg (atom p))}
      (disj (neg (atom p)) (atom p)) := by
  constructor
  · intro A hA
    obtain rfl := Set.mem_singleton_iff.mp hA
    exact sound (translated_negation_theorem p).2 (chainModel p) false
      (by simp [ForcesContext])
  · rintro (hn | hp)
    · exact (chain_values p).2.1 hn
    · exact (chain_values p).1 hp

theorem classical_comparison_not_derivable (p : α) :
    ¬ Lemmatheca.ProofTheory.Intuitionistic.Derives ∅ (impl (formula (atom p) (neg (atom p)))
      (disj (neg (atom p)) (atom p))) := by
  intro h
  have hm := classical_comparison_countermodel p
  have hi := sound h (chainModel p) false (by simp [ForcesContext])
  exact hm.2 (hi false le_rfl (hm.1 _ (Set.mem_singleton _)))

theorem untranslated_negation_not_theorem (p : α) :
    ¬ Forces (chainModel p) true (neg (atom p)) ∧ ¬ Lemmatheca.ProofTheory.Intuitionistic.Derives ∅ (neg (atom p)) := by
  refine ⟨(chain_upper_values p).2.1, ?_⟩
  intro h
  exact (chain_upper_values p).2.1
    (sound h (chainModel p) true (by simp [ForcesContext]))

end Lemmatheca.Entry.PropositionalFriedmanTranslation
