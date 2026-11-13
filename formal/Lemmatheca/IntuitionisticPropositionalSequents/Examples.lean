import Lemmatheca.IntuitionisticPropositionalSequents.Translations

namespace Lemmatheca.Entry.IntuitionisticPropositionalSequents

open Lemmatheca.MathematicalLogic.Propositional
open PropFormula
open Lemmatheca.ProofTheory.Intuitionistic.SequentCalculus

universe u
variable {α : Type u} [DecidableEq α]

/-- The two identity leaves select the respective factors, also when they coincide. -/
theorem conjunction_proof (A B : PropFormula α) :
    Lemmatheca.ProofTheory.Intuitionistic.SequentCalculus.Derives ∅
      (impl A (impl B (conj A B))) := by
  apply Derives.implRight
  apply Derives.implRight
  exact Derives.conjRight (.identity (by simp)) (.identity (by simp))

/-- The atom and its native negation are two syntactically distinct conclusions. -/
theorem two_conclusions_card (p : α) :
    ({atom p, neg (atom p)} : Finset (PropFormula α)).card = 2 := by
  simp

end Lemmatheca.Entry.IntuitionisticPropositionalSequents
