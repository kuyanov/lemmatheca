import Lemmatheca.IntuitionisticPropositionalDeduction.Deduction

/-! The Gödel–Gentzen translation on the actual shared propositional syntax. -/
namespace Lemmatheca.ProofTheory.Intuitionistic.NegativeTranslation

open Lemmatheca.MathematicalLogic.Propositional
open PropFormula

universe u v
variable {α : Type u} {β : Type v}

/-- Atoms and disjunctions are double-negated; primitive negation is retained. -/
def negative : PropFormula α → PropFormula α
  | .atom p => .neg (.neg (.atom p))
  | .falsum => .falsum
  | .neg A => .neg (negative A)
  | .conj A B => .conj (negative A) (negative B)
  | .disj A B => .neg (.neg (.disj (negative A) (negative B)))
  | .impl A B => .impl (negative A) (negative B)

/-- The actual pointwise image of a possibly infinite allowed-premise set. -/
def context (Γ : Set (PropFormula α)) : Set (PropFormula α) := negative '' Γ

/-- Stability is provability of the specified native double-negation implication. -/
def Stable (A : PropFormula α) : Prop :=
  Derives ∅ (impl (neg (neg A)) A)

/-- Equivalence means the two actual closed intuitionistic implications. -/
def Equivalent (A B : PropFormula α) : Prop :=
  Derives ∅ (impl A B) ∧ Derives ∅ (impl B A)

theorem context_insert (Γ : Set (PropFormula α)) (A : PropFormula α) :
    context (insert A Γ) = insert (negative A) (context Γ) := by
  exact Set.image_insert_eq

private theorem use_stable {Γ : Set (PropFormula α)} {A : PropFormula α}
    (h : Stable A) (hn : Derives Γ (neg (neg A))) : Derives Γ A :=
  .implElim (h.weaken (Set.empty_subset _)) hn

theorem stable_falsum : Stable (falsum : PropFormula α) := by
  apply Derives.implIntro
  exact .negElim (A := neg falsum) (.negIntro (.assumption (by simp)))
    (.assumption (by simp))

theorem stable_neg (A : PropFormula α) : Stable (neg A) := by
  exact triple_negation_elim A

theorem stable_conj {A B : PropFormula α} (hA : Stable A) (hB : Stable B) :
    Stable (conj A B) := by
  apply Derives.implIntro
  apply Derives.conjIntro
  · apply use_stable hA
    apply Derives.negIntro
    exact .negElim (A := neg (conj A B))
      (.negIntro (.negElim (A := A)
        (.conjElimLeft (B := B) (.assumption (by simp))) (.assumption (by simp))))
      (.assumption (by simp))
  · apply use_stable hB
    apply Derives.negIntro
    exact .negElim (A := neg (conj A B))
      (.negIntro (.negElim (A := B)
        (.conjElimRight (A := A) (.assumption (by simp))) (.assumption (by simp))))
      (.assumption (by simp))

theorem stable_impl (A : PropFormula α) {B : PropFormula α} (hB : Stable B) :
    Stable (impl A B) := by
  apply Derives.implIntro
  apply Derives.implIntro
  apply use_stable hB
  apply Derives.negIntro
  exact .negElim (A := neg (impl A B))
    (.negIntro (.negElim (A := B)
      (.implElim (A := A) (.assumption (by simp)) (.assumption (by simp)))
      (.assumption (by simp))))
    (.assumption (by simp))

theorem negative_stable (A : PropFormula α) : Stable (negative A) := by
  induction A with
  | atom p => exact stable_neg (neg (atom p))
  | falsum => exact stable_falsum
  | neg A _ => exact stable_neg (negative A)
  | conj A B ihA ihB => exact stable_conj ihA ihB
  | disj A B _ _ => exact stable_neg (neg (disj (negative A) (negative B)))
  | impl A _ _ ihB => exact stable_impl (negative A) ihB

theorem negative_eval (b : α → Bool) (A : PropFormula α) :
    eval b (negative A) = eval b A := by
  induction A <;> simp_all [negative, eval]

theorem negative_atoms [DecidableEq α] (A : PropFormula α) :
    atoms (negative A) = atoms A := by
  induction A <;> simp_all [negative, atoms]

theorem negative_classical_equivalence [DecidableEq α] (A : PropFormula α) :
    Lemmatheca.MathematicalLogic.Propositional.Derives ∅
      (biconditional A (negative A)) := by
  apply (theorem_iff_tautology _).mpr
  intro b
  simp [Satisfies, biconditional, eval, negative_eval]

end Lemmatheca.ProofTheory.Intuitionistic.NegativeTranslation
