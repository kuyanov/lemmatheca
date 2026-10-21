import Lemmatheca.PaProofCheckers.ArithmeticProofPredicatesLogic
import Lemmatheca.PaComputations.PAComputations

open Lemmatheca.MathematicalLogic Lemmatheca.ModelTheory Lemmatheca.ComputabilityTheory

/-! The exact finite initial-segment sentences used by the arithmetic proof
builders, kept below the combined proof-predicate construction. -/
namespace Lemmatheca.ProofTheory.ArithmeticProofPredicates
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic ArithmeticTheories ArithmeticRepresentability PAComputations
noncomputable section

def initialSegmentDisjunction : ℕ → language.Formula Unit
  | 0 => (Term.var ()).equal zeroTerm
  | n + 1 => initialSegmentDisjunction n ⊔ (Term.var ()).equal (numeralTerm (n + 1))

def initialSegmentSentence (n : ℕ) : language.Sentence :=
  allClose ((leFormula (.var ()) (numeralTerm n)).imp (initialSegmentDisjunction n))

end
end Lemmatheca.ProofTheory.ArithmeticProofPredicates
