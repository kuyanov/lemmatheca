import Lemmatheca.MinimalPropositionalLogic.Models
import Lemmatheca.IntuitionisticPropositionalDeduction.Classical

namespace Lemmatheca.Entry.MinimalPropositionalLogic
open Lemmatheca.MathematicalLogic.Propositional
open PropFormula
open Lemmatheca.ProofTheory
open Minimal.Kripke
universe u
variable {α : Type u}

/-- A singleton frame with independently specified atomic and falsum values. -/
def singletonModel (v : α → Prop) (e : Prop) : Model α (Fin 1) where
  valuation := fun _ => v
  persistent := fun _ _ h => h
  abnormal := fun _ => e
  abnormal_persistent := fun _ h => h

theorem explosion_countermodels (q : α) :
    Countermodel (singletonModel (fun _ : α => False) True) 0 {falsum} (atom q) ∧
    Countermodel (singletonModel (fun _ : α => False) True) 0 ∅ (impl falsum (atom q)) := by
  simp [Countermodel, ForcesContext, Forces, singletonModel]


theorem explosion_not_derivable (q : α) :
    ¬ Minimal.Derives {falsum} (atom q) ∧
      ¬ Minimal.Derives ∅ (impl falsum (atom q)) := by
  exact ⟨countermodel_not_derivable _ _ _ _ (explosion_countermodels q).1,
    countermodel_not_derivable _ _ _ _ (explosion_countermodels q).2⟩


theorem syllogism_countermodels (p q : α) (hpq : p ≠ q) :
    Countermodel (singletonModel (fun r => r = p) True) 0
      {disj (atom p) (atom q), neg (atom p)} (atom q) ∧
    Countermodel (singletonModel (fun r => r = p) True) 0
      {atom p, neg (atom p)} (atom q) := by
  simp [Countermodel, ForcesContext, Forces, singletonModel, Ne.symm hpq]


theorem syllogism_not_derivable (p q : α) (hpq : p ≠ q) :
    ¬ Minimal.Derives {disj (atom p) (atom q), neg (atom p)} (atom q) ∧
      ¬ Minimal.Derives {atom p, neg (atom p)} (atom q) := by
  exact ⟨countermodel_not_derivable _ _ _ _ (syllogism_countermodels p q hpq).1,
    countermodel_not_derivable _ _ _ _ (syllogism_countermodels p q hpq).2⟩


theorem excluded_middle_countermodel (q : α) :
    Countermodel (singletonModel (fun _ : α => False) True) 0
      Intuitionistic.excludedMiddleSchema (impl falsum (atom q)) := by
  constructor
  · intro A hA
    rcases hA with ⟨B, rfl⟩
    exact Or.inr (by intro z hz hB; trivial)
  · intro h
    exact h 0 le_rfl trivial


theorem excluded_middle_without_explosion (q : α) :
    ¬ Minimal.Derives Intuitionistic.excludedMiddleSchema (impl falsum (atom q)) := by
  exact countermodel_not_derivable _ _ _ _ (excluded_middle_countermodel q)


theorem normal_singleton_countermodel :
    Countermodel (singletonModel (fun _ : α => False) False) 0 ∅ falsum := by
  simp [Countermodel, ForcesContext, Forces, singletonModel]


end Lemmatheca.Entry.MinimalPropositionalLogic
