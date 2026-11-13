import Lemmatheca.PropositionalNegativeTranslation.Translation

namespace Lemmatheca.ProofTheory.Intuitionistic.NegativeTranslation

open Lemmatheca.MathematicalLogic.Propositional
open PropFormula

universe u v
variable {α : Type u} {β : Type v}

private theorem apply_closed {Γ : Set (PropFormula α)} {A B : PropFormula α}
    (h : Derives ∅ (impl A B)) (hA : Derives Γ A) : Derives Γ B :=
  .implElim (h.weaken (Set.empty_subset _)) hA

theorem equivalent_neg {A B : PropFormula α} (h : Equivalent A B) :
    Equivalent (neg A) (neg B) := by
  constructor
  · apply Derives.implIntro
    apply Derives.negIntro
    exact .negElim (apply_closed h.2 (.assumption (by simp))) (.assumption (by simp))
  · apply Derives.implIntro
    apply Derives.negIntro
    exact .negElim (apply_closed h.1 (.assumption (by simp))) (.assumption (by simp))

theorem equivalent_conj {A A' B B' : PropFormula α}
    (hA : Equivalent A A') (hB : Equivalent B B') :
    Equivalent (conj A B) (conj A' B') := by
  constructor
  · apply Derives.implIntro
    exact .conjIntro
      (apply_closed hA.1 (.conjElimLeft (B := B) (.assumption (by simp))))
      (apply_closed hB.1 (.conjElimRight (A := A) (.assumption (by simp))))
  · apply Derives.implIntro
    exact .conjIntro
      (apply_closed hA.2 (.conjElimLeft (B := B') (.assumption (by simp))))
      (apply_closed hB.2 (.conjElimRight (A := A') (.assumption (by simp))))

theorem equivalent_disj {A A' B B' : PropFormula α}
    (hA : Equivalent A A') (hB : Equivalent B B') :
    Equivalent (disj A B) (disj A' B') := by
  constructor
  · apply Derives.implIntro
    apply Derives.disjElim (A := A) (B := B) (.assumption (by simp))
    · exact .disjIntroLeft (apply_closed hA.1 (.assumption (by simp)))
    · exact .disjIntroRight (apply_closed hB.1 (.assumption (by simp)))
  · apply Derives.implIntro
    apply Derives.disjElim (A := A') (B := B') (.assumption (by simp))
    · exact .disjIntroLeft (apply_closed hA.2 (.assumption (by simp)))
    · exact .disjIntroRight (apply_closed hB.2 (.assumption (by simp)))

theorem equivalent_impl {A A' B B' : PropFormula α}
    (hA : Equivalent A A') (hB : Equivalent B B') :
    Equivalent (impl A B) (impl A' B') := by
  constructor
  · apply Derives.implIntro
    apply Derives.implIntro
    exact apply_closed hB.1
      (.implElim (.assumption (by simp)) (apply_closed hA.2 (.assumption (by simp))))
  · apply Derives.implIntro
    apply Derives.implIntro
    exact apply_closed hB.2
      (.implElim (.assumption (by simp)) (apply_closed hA.1 (.assumption (by simp))))

theorem negative_substitution (σ : α → PropFormula β) (A : PropFormula α) :
    Equivalent (negative (subst σ A))
      (subst (fun p => negative (σ p)) (negative A)) := by
  induction A with
  | atom p => exact ⟨double_negation_intro (negative (σ p)), negative_stable (σ p)⟩
  | falsum => exact ⟨identity falsum, identity falsum⟩
  | neg A ih => exact equivalent_neg ih
  | conj A B ihA ihB => exact equivalent_conj ihA ihB
  | disj A B ihA ihB => exact equivalent_neg (equivalent_neg (equivalent_disj ihA ihB))
  | impl A B ihA ihB => exact equivalent_impl ihA ihB

theorem negative_rename (f : α → β) (A : PropFormula α) :
    negative (subst (fun p => atom (f p)) A) =
      subst (fun p => atom (f p)) (negative A) := by
  induction A <;> simp_all [negative, subst]

end Lemmatheca.ProofTheory.Intuitionistic.NegativeTranslation
