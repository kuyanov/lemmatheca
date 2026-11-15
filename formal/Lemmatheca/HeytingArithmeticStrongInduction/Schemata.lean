import Lemmatheca.HeytingArithmeticStrongInduction.Certificates
import Lemmatheca.HeytingArithmeticOrder.Closure

namespace Lemmatheca.ProofTheory.HeytingArithmetic.StrongInduction
open _root_.FirstOrder _root_.FirstOrder.Language
open Lemmatheca.ProofTheory.FirstOrder.BoundedFormula

/-- Close precisely the displayed strong-induction implication in parameter order. -/
def strongSchema {k} (A : Formula (Fin k ⊕ Unit)) : Sentence :=
  close (.impl (completePremise A) (allUnit A))

/-- The decision premise is retained when the least-number rule is closed. -/
def decidableLeastSchema {k} (A : Formula (Fin k ⊕ Unit)) : Sentence :=
  close (.impl (predicateDecision A) (.impl (exUnit A) (minimumExists A)))

noncomputable section
local instance hasiSchemataEq {δ : Type*} : DecidableEq (Formula δ) := Classical.decEq _

def strongSchemaProof {k} (A : Formula (Fin k ⊕ Unit)) :
    Certificate false (∅ : Context Empty) (strongSchema A) := by
  unfold strongSchema
  apply _root_.Lemmatheca.ProofTheory.HeytingArithmetic.Order.closeCertificate
  apply TheoryCertificate.impIntro
  exact strongInduction A (TheoryCertificate.assumption (by simp))

def decidableLeastSchemaProof {k} (A : Formula (Fin k ⊕ Unit)) :
    Certificate false (∅ : Context Empty) (decidableLeastSchema A) := by
  unfold decidableLeastSchema
  apply _root_.Lemmatheca.ProofTheory.HeytingArithmetic.Order.closeCertificate
  apply TheoryCertificate.impIntro
  apply TheoryCertificate.impIntro
  exact leastWitness A (TheoryCertificate.assumption (by simp))
    (TheoryCertificate.assumption (by simp))

end
end Lemmatheca.ProofTheory.HeytingArithmetic.StrongInduction
