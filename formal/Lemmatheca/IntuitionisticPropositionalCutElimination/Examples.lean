import Lemmatheca.IntuitionisticPropositionalCutElimination.Subformulas

namespace Lemmatheca.Entry.IntuitionisticPropositionalCutElimination

open Lemmatheca.MathematicalLogic.Propositional
open PropFormula
open Lemmatheca.ProofTheory.Intuitionistic.CutFree

universe u
variable {α : Type u} [DecidableEq α]

def modusPonens (A B : PropFormula α) : Proof {A, impl A B} B :=
  .implLeft (A := A) (B := B) (by simp)
    (Proof.identity A (by simp)) (Proof.identity B (by simp))

end Lemmatheca.Entry.IntuitionisticPropositionalCutElimination
