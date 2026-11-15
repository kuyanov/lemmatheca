import Lemmatheca.IntuitionisticPropositionalG4ip.Conversions
import Mathlib.Data.Finset.Basic

namespace Lemmatheca.ProofTheory.Intuitionistic.G4ip.Search
open Lemmatheca.MathematicalLogic.Propositional
open PropFormula
universe u
variable {α : Type u} [DecidableEq α]

/-- Ordered presentations; the human core domain is selected by ReducedGoal. -/
abbrev PresentedGoal (α : Type u) := List (PropFormula α) × PropFormula α

def underlying (g : PresentedGoal α) : G4ip.Goal α := (g.1.toFinset, g.2)

def ReducedGoal (g : PresentedGoal α) : Prop :=
  (∀ A ∈ g.1, NegationFree A) ∧ NegationFree g.2

abbrev Certificate (g : PresentedGoal α) := G4ip.Proof g.1.toFinset g.2

def problemWeight (g : PresentedGoal α) : ℕ := goalWeight (underlying g)

/-- Delete all occurrences, preserving the order of every retained formula. -/
def removePrincipal (F : PropFormula α) (H : List (PropFormula α)) : List (PropFormula α) :=
  H.filter (fun A => decide (A ≠ F))

theorem removePrincipal_toFinset (F : PropFormula α) (H : List (PropFormula α)) :
    (removePrincipal F H).toFinset = remainder H.toFinset F := by
  ext A
  simp [removePrincipal, remainder, and_comm]

theorem reducedGoal_iff (g : PresentedGoal α) :
    ReducedGoal g ↔ ReducedContext g.1.toFinset ∧ NegationFree g.2 := by
  simp only [ReducedGoal, ReducedContext, List.mem_toFinset]

/-- An actual certificate at each position of the explicitly ordered goal list. -/
def Certificates : List (PresentedGoal α) → Type u
  | [] => PUnit
  | g :: gs => Certificate g × Certificates gs

end Lemmatheca.ProofTheory.Intuitionistic.G4ip.Search
