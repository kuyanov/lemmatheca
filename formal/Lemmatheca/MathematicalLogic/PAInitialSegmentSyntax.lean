import Lemmatheca.MathematicalLogic.ArithmeticProofPredicatesLogic
import Lemmatheca.MathematicalLogic.PAComputations

/-! The exact finite initial-segment sentences used by the arithmetic proof
builders, kept below the combined proof-predicate construction. -/
namespace Lemmatheca.MathematicalLogic.ArithmeticProofPredicates
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic ArithmeticTheories ArithmeticRepresentability PAComputations
noncomputable section

def initialSegmentDisjunction : ℕ → language.Formula Unit
  | 0 => (Term.var ()).equal zeroTerm
  | n + 1 => initialSegmentDisjunction n ⊔ (Term.var ()).equal (numeralTerm (n + 1))

def initialSegmentSentence (n : ℕ) : language.Sentence :=
  allClose ((leFormula (.var ()) (numeralTerm n)).imp (initialSegmentDisjunction n))

end
end Lemmatheca.MathematicalLogic.ArithmeticProofPredicates
