import Lemmatheca.PaProofCheckers.PAProofRulePrograms
import Lemmatheca.PaListsAndSyntax.PAFixedSyntaxPrograms

open Lemmatheca.MathematicalLogic Lemmatheca.ModelTheory Lemmatheca.ComputabilityTheory

/-! Numeral substitution in genuine finite PA proof certificates. -/
namespace Lemmatheca.ProofTheory.PAComputations.ProofPrograms.CheckerPrograms.NumericalProofs
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic ArithmeticTheories ArithmeticRepresentability FirstOrderProofs
open SyntaxPrograms
noncomputable section

def num {r : ℕ} (a : Program r) : Program r := unary ProofPrograms.numeral a

/-- Extract the actual universal body from the accepted certificate's root. -/
def specializeOne {r : ℕ} (p t : Program r) : Program r :=
  let root := binary listEntry p (constant 0)
  let conclusion := unary (argument 1) root
  let body := unary (argument 0) conclusion
  ternary forallEliminationCertificate p body t

end
end Lemmatheca.ProofTheory.PAComputations.ProofPrograms.CheckerPrograms.NumericalProofs
