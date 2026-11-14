import Lemmatheca.HeytingArithmeticMultiplication.Certificates

namespace Lemmatheca.ProofTheory.HeytingArithmetic.Multiplication
open _root_.FirstOrder _root_.FirstOrder.Language
open Lemmatheca.ProofTheory.FirstOrder.BoundedFormula
open Lemmatheca.MathematicalLogic.FirstOrderProofs
universe u
variable {α : Type u}
noncomputable section
local instance haMultiplicationInstancesEq {β : Type*} : DecidableEq (Formula β) := Classical.decEq _
variable {Γ : Context α}

def zeroLeft (s : LA.Term α) : Certificate false Γ (termEqual (mulTerm zeroTerm s) zeroTerm) := by
  simpa [zeroLeftBody, termEqual_subst_poly, mul_subst, zero_subst, Term.subst] using
    Addition.instantiateClosed zeroLeftBody zeroLeftProof ![s] Γ

def oneLeft (s : LA.Term α) : Certificate false Γ (termEqual (mulTerm (succTerm zeroTerm) s) s) := by
  simpa [oneLeftBody, termEqual_subst_poly, mul_subst, succ_subst, zero_subst, Term.subst] using
    Addition.instantiateClosed oneLeftBody oneLeftProof ![s] Γ

def successorLeft (s t : LA.Term α) : Certificate false Γ
    (termEqual (mulTerm (succTerm s) t) (addTerm (mulTerm s t) t)) := by
  simpa [successorLeftBody, termEqual_subst_poly, mul_subst, add_subst, succ_subst, Term.subst] using
    Addition.instantiateClosed successorLeftBody successorLeftProof ![s,t] Γ

def commutative (s t : LA.Term α) : Certificate false Γ (termEqual (mulTerm s t) (mulTerm t s)) := by
  simpa [commutativityBody, termEqual_subst_poly, mul_subst, Term.subst] using
    Addition.instantiateClosed commutativityBody commutativityProof ![s,t] Γ

def distributeLeft (s t u : LA.Term α) : Certificate false Γ
    (termEqual (mulTerm s (addTerm t u)) (addTerm (mulTerm s t) (mulTerm s u))) := by
  simpa [leftDistributivityBody, termEqual_subst_poly, mul_subst, add_subst, Term.subst] using
    Addition.instantiateClosed leftDistributivityBody leftDistributivityProof ![s,t,u] Γ

def distributeRight (s t u : LA.Term α) : Certificate false Γ
    (termEqual (mulTerm (addTerm s t) u) (addTerm (mulTerm s u) (mulTerm t u))) := by
  simpa [rightDistributivityBody, termEqual_subst_poly, mul_subst, add_subst, Term.subst] using
    Addition.instantiateClosed rightDistributivityBody rightDistributivityProof ![s,t,u] Γ

def associative (s t u : LA.Term α) : Certificate false Γ
    (termEqual (mulTerm (mulTerm s t) u) (mulTerm s (mulTerm t u))) := by
  simpa [associativityBody, termEqual_subst_poly, mul_subst, Term.subst] using
    Addition.instantiateClosed associativityBody associativityProof ![s,t,u] Γ

/-- The supplied equality tree is the second input of the actual transitivity operation. -/
def expandLeftSum (s t u v : LA.Term α)
    (p : Certificate false Γ (termEqual (mulTerm (addTerm s t) u) v)) :
    Certificate false Γ (termEqual (addTerm (mulTerm s u) (mulTerm t u)) v) :=
  TheoryCertificate.equalTransitivity
    (TheoryCertificate.equalSymmetry (distributeRight s t u)) p

end
end Lemmatheca.ProofTheory.HeytingArithmetic.Multiplication
