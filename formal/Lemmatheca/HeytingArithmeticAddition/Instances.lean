import Lemmatheca.HeytingArithmeticAddition.Certificates

namespace Lemmatheca.ProofTheory.HeytingArithmetic.Addition
open _root_.FirstOrder _root_.FirstOrder.Language
open Lemmatheca.ProofTheory.FirstOrder.BoundedFormula
open Lemmatheca.MathematicalLogic.FirstOrderProofs
universe u
variable {α : Type u}
noncomputable section
local instance haAdditionInstancesEq {β : Type*} : DecidableEq (Formula β) := Classical.decEq _


variable {Γ : Context α}

def zeroLeft (s : LA.Term α) : Certificate false Γ (termEqual (addTerm zeroTerm s) s) := by
  simpa [zeroLeftBody, termEqual_subst_poly, add_subst, zero_subst, Term.subst] using
    instantiateClosed zeroLeftBody zeroLeftProof ![s] Γ

def successorLeft (s t : LA.Term α) :
    Certificate false Γ (termEqual (addTerm (succTerm s) t) (succTerm (addTerm s t))) := by
  simpa [successorLeftBody, termEqual_subst_poly, add_subst, succ_subst, Term.subst] using
    instantiateClosed successorLeftBody successorLeftProof ![s,t] Γ

def associative (s t u : LA.Term α) :
    Certificate false Γ (termEqual (addTerm (addTerm s t) u) (addTerm s (addTerm t u))) := by
  simpa [associativityBody, termEqual_subst_poly, add_subst, Term.subst] using
    instantiateClosed associativityBody associativityProof ![s,t,u] Γ

def commutative (s t : LA.Term α) :
    Certificate false Γ (termEqual (addTerm s t) (addTerm t s)) := by
  simpa [commutativityBody, termEqual_subst_poly, add_subst, Term.subst] using
    instantiateClosed commutativityBody commutativityProof ![s,t] Γ

def exchange (s t u : LA.Term α) :
    Certificate false Γ (termEqual (addTerm (addTerm s t) u) (addTerm (addTerm s u) t)) := by
  simpa [exchangeBody, termEqual_subst_poly, add_subst, Term.subst] using
    instantiateClosed exchangeBody exchangeProof ![s,t,u] Γ

def cancelLeftImplication (s t u : LA.Term α) :
    Certificate false Γ (.impl (termEqual (addTerm s t) (addTerm s u)) (termEqual t u)) := by
  simpa [cancelLeftBody, subst_impl, termEqual_subst_poly, add_subst, Term.subst] using
    instantiateClosed cancelLeftBody cancelLeftProof ![s,t,u] Γ

def cancelRightImplication (s t u : LA.Term α) :
    Certificate false Γ (.impl (termEqual (addTerm t s) (addTerm u s)) (termEqual t u)) := by
  simpa [cancelRightBody, subst_impl, termEqual_subst_poly, add_subst, Term.subst] using
    instantiateClosed cancelRightBody cancelRightProof ![s,t,u] Γ

/-- The provided equality tree is consumed by the actual implication-elimination operation. -/
def cancelLeft (s t u : LA.Term α)
    (p : Certificate false Γ (termEqual (addTerm s t) (addTerm s u))) :
    Certificate false Γ (termEqual t u) :=
  TheoryCertificate.impElim (cancelLeftImplication s t u) p

def cancelRight (s t u : LA.Term α)
    (p : Certificate false Γ (termEqual (addTerm t s) (addTerm u s))) :
    Certificate false Γ (termEqual t u) :=
  TheoryCertificate.impElim (cancelRightImplication s t u) p

end
end Lemmatheca.ProofTheory.HeytingArithmetic.Addition
