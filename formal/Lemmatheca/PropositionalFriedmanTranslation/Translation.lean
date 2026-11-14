import Lemmatheca.PropositionalNegativeTranslation.Substitution
import Lemmatheca.IntuitionisticPropositionalCutElimination.Translations

/-! The parameter translation on the shared native propositional syntax. -/
namespace Lemmatheca.ProofTheory.Intuitionistic.FriedmanTranslation

open Lemmatheca.MathematicalLogic.Propositional
open PropFormula

universe u v
variable {α : Type u} {β : Type v}

/-- The parameter is inserted as a whole formula, including at native negation. -/
def formula (R : PropFormula α) : PropFormula α → PropFormula α
  | .atom p => .disj (.atom p) R
  | .falsum => R
  | .neg A => .impl (formula R A) R
  | .conj A B => .conj (formula R A) (formula R B)
  | .disj A B => .disj (formula R A) (formula R B)
  | .impl A B => .impl (formula R A) (formula R B)

/-- Image of a possibly infinite set of allowed premises. -/
def context (R : PropFormula α) (Γ : Set (PropFormula α)) : Set (PropFormula α) :=
  formula R '' Γ

/-- Image of the actual finite antecedent used by a supplied sequent tree. -/
def finiteContext [DecidableEq α] (R : PropFormula α) (Γ : Finset (PropFormula α)) :
    Finset (PropFormula α) := Γ.image (formula R)

theorem context_insert (R A : PropFormula α) (Γ : Set (PropFormula α)) :
    context R (insert A Γ) = insert (formula R A) (context R Γ) := by
  exact Set.image_insert_eq

theorem context_finite (R : PropFormula α) {Γ : Set (PropFormula α)}
    (hΓ : Γ.Finite) : (context R Γ).Finite := by
  exact hΓ.image (formula R)

theorem finiteContext_insert [DecidableEq α] (R A : PropFormula α)
    (Γ : Finset (PropFormula α)) :
    finiteContext R (insert A Γ) = insert (formula R A) (finiteContext R Γ) := by
  exact Finset.image_insert _ _ _

theorem coe_finiteContext [DecidableEq α] (R : PropFormula α)
    (Γ : Finset (PropFormula α)) :
    (finiteContext R Γ : Set (PropFormula α)) = context R (Γ : Set (PropFormula α)) := by
  exact Finset.coe_image

theorem mem_finiteContext [DecidableEq α] (R : PropFormula α)
    {Γ : Finset (PropFormula α)} {A : PropFormula α} (hA : A ∈ Γ) :
    formula R A ∈ finiteContext R Γ := by
  exact Finset.mem_image_of_mem _ hA

private theorem apply_closed {Γ : Set (PropFormula α)} {A B : PropFormula α}
    (h : Derives ∅ (impl A B)) (hA : Derives Γ A) : Derives Γ B :=
  .implElim (h.weaken (Set.empty_subset _)) hA

theorem bottom_equivalent (A : PropFormula α) :
    NegativeTranslation.Equivalent (formula falsum A) A := by
  induction A with
  | atom p =>
      change NegativeTranslation.Equivalent (disj (atom p) falsum) (atom p)
      constructor
      · apply Derives.implIntro
        apply Derives.disjElim (A := atom p) (B := falsum) (.assumption (by simp))
        · exact .assumption (by simp)
        · exact .falsumElim (.assumption (by simp))
      · exact .implIntro (.disjIntroLeft (.assumption (by simp)))
  | falsum => exact ⟨identity falsum, identity falsum⟩
  | neg A ih =>
      change NegativeTranslation.Equivalent (impl (formula falsum A) falsum) (neg A)
      constructor
      · apply Derives.implIntro
        apply Derives.negIntro
        exact .implElim (.assumption (by simp))
          (apply_closed ih.2 (.assumption (by simp)))
      · apply Derives.implIntro
        apply Derives.implIntro
        exact .negElim (apply_closed ih.1 (.assumption (by simp)))
          (.assumption (by simp))
  | conj A B ihA ihB => exact NegativeTranslation.equivalent_conj ihA ihB
  | disj A B ihA ihB => exact NegativeTranslation.equivalent_disj ihA ihB
  | impl A B ihA ihB => exact NegativeTranslation.equivalent_impl ihA ihB

theorem rename (ρ : α → β) (R A : PropFormula α) :
    subst (fun p => atom (ρ p)) (formula R A) =
      formula (subst (fun p => atom (ρ p)) R) (subst (fun p => atom (ρ p)) A) := by
  induction A <;> simp_all [formula, subst]

theorem eval_formula (v : α → Bool) (R A : PropFormula α) :
    eval v (formula R A) = (eval v A || eval v R) := by
  induction A with
  | atom p => rfl
  | falsum => simp [formula, eval]
  | neg A ih =>
      simp only [formula, eval, ih]
      cases eval v A <;> cases eval v R <;> rfl
  | conj A B ihA ihB =>
      simp only [formula, eval, ihA, ihB]
      cases eval v A <;> cases eval v B <;> cases eval v R <;> rfl
  | disj A B ihA ihB =>
      simp only [formula, eval, ihA, ihB]
      cases eval v A <;> cases eval v B <;> cases eval v R <;> rfl
  | impl A B ihA ihB =>
      simp only [formula, eval, ihA, ihB]
      cases eval v A <;> cases eval v B <;> cases eval v R <;> rfl

theorem classical_equivalent [DecidableEq α] (R A : PropFormula α) :
    Lemmatheca.MathematicalLogic.Propositional.Derives ∅
      (biconditional (formula R A) (disj A R)) := by
  apply (theorem_iff_tautology _).mpr
  intro v
  cases hA : eval v A <;> cases hR : eval v R <;>
    simp [Satisfies, biconditional, eval, eval_formula, hA, hR]

end Lemmatheca.ProofTheory.Intuitionistic.FriedmanTranslation
