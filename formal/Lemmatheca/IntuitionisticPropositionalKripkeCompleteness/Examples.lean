import Lemmatheca.IntuitionisticPropositionalKripkeCompleteness.CanonicalModel
import Lemmatheca.IntuitionisticKripkeSemantics.Examples

namespace Lemmatheca.Entry.IntuitionisticPropositionalKripkeCompleteness

open Lemmatheca.MathematicalLogic.Propositional
open PropFormula
open Lemmatheca.ProofTheory.Intuitionistic

/-- The exact lower-world truth set from the existing two-world model. -/
def undecidedTheory : Set Canonical.Formula := Canonical.truthTheory (IntuitionisticKripkeSemantics.chainModel (0 : ℕ)) false

theorem prime_not_complete : Canonical.IsPrime undecidedTheory ∧ atom 0 ∉ undecidedTheory ∧
    neg (atom 0) ∉ undecidedTheory ∧ disj (atom 0) (neg (atom 0)) ∉ undecidedTheory := by
  refine ⟨Canonical.truthTheory_prime _ _, ?_, ?_, ?_⟩
  · exact (IntuitionisticKripkeSemantics.chain_values (0 : ℕ)).1
  · exact (IntuitionisticKripkeSemantics.chain_values (0 : ℕ)).2.1
  · exact IntuitionisticKripkeSemantics.chain_not_excluded_middle (0 : ℕ)

end Lemmatheca.Entry.IntuitionisticPropositionalKripkeCompleteness
