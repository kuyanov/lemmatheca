import Lemmatheca.IntuitionisticPropositionalDeduction.Deduction

/-! A finite-set, single-conclusion LJ presentation on the shared native syntax.
Weakening and split-context cut are primitive. Primitive negation has explicit
left and right rules, so it is not silently identified with an implication. -/

namespace Lemmatheca.ProofTheory.Intuitionistic.SequentCalculus

open Lemmatheca.MathematicalLogic.Propositional
open PropFormula

universe u

/-- A finite antecedent and exactly one shared formula as succedent. -/
abbrev Judgement (α : Type u) := Finset (PropFormula α) × PropFormula α

variable {α : Type u} [DecidableEq α]

/-- Finite single-conclusion sequent derivations with the stated primitive cut. -/
inductive Derives : Finset (PropFormula α) → PropFormula α → Prop
  | identity {Γ A} : A ∈ Γ → Derives Γ A
  | falsumLeft {Γ C} : falsum ∈ Γ → Derives Γ C
  | weakening {Γ Δ A} : Derives Γ A → Γ ⊆ Δ → Derives Δ A
  | conjLeft {Γ A B C} : Derives (insert A (insert B Γ)) C →
      Derives (insert (conj A B) Γ) C
  | conjRight {Γ A B} : Derives Γ A → Derives Γ B → Derives Γ (conj A B)
  | disjLeft {Γ A B C} : Derives (insert A Γ) C → Derives (insert B Γ) C →
      Derives (insert (disj A B) Γ) C
  | disjRightLeft {Γ A B} : Derives Γ A → Derives Γ (disj A B)
  | disjRightRight {Γ A B} : Derives Γ B → Derives Γ (disj A B)
  | implLeft {Γ Δ A B C} : Derives Γ A → Derives (insert B Δ) C →
      Derives (insert (impl A B) (Γ ∪ Δ)) C
  | implRight {Γ A B} : Derives (insert A Γ) B → Derives Γ (impl A B)
  | negLeft {Γ A C} : Derives Γ A → Derives (insert (neg A) Γ) C
  | negRight {Γ A} : Derives (insert A Γ) falsum → Derives Γ (neg A)
  | cut {Γ Δ A C} : Derives Γ A → Derives (insert A Δ) C → Derives (Γ ∪ Δ) C

end Lemmatheca.ProofTheory.Intuitionistic.SequentCalculus
