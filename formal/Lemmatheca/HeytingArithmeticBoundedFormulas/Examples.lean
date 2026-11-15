import Lemmatheca.HeytingArithmeticBoundedFormulas.Decisions

namespace Lemmatheca.Entry.HeytingArithmeticBoundedFormulas
open _root_.FirstOrder _root_.FirstOrder.Language
open Lemmatheca.ProofTheory.FirstOrder.BoundedFormula
open Lemmatheca.ProofTheory.HeytingArithmetic
open Lemmatheca.ProofTheory.HeytingArithmetic.Order
open Lemmatheca.ProofTheory.HeytingArithmetic.StrongInduction
open Lemmatheca.ProofTheory.HeytingArithmetic.Bounded

/-- The old tags are a and x; only the newest tag is y. -/
def parityBody : Expr ((Fin 1 ⊕ Unit) ⊕ Unit) :=
  .disj
    (.equal (.var (.inl (.inr ()))) (addTerm (.var (.inr ())) (.var (.inr ()))))
    (.equal (.var (.inl (.inr ()))) (succTerm (addTerm (.var (.inr ())) (.var (.inr ())))))

def nestedBody : Expr (Fin 1 ⊕ Unit) :=
  .exLE (.var (.inr ())) parityBody

def nested : Expr (Fin 1) :=
  .allLT (.var 0) nestedBody

theorem nested_expansion :
    nested.expand = history
      (inclusiveExists
        (.disj
          (termEqual (.var (.inl (.inr ()))) (addTerm (.var (.inr ())) (.var (.inr ()))))
          (termEqual (.var (.inl (.inr ())))
            (succTerm (addTerm (.var (.inr ())) (.var (.inr ()))))))
        (.var (.inr ())))
      (.var 0) := by
  rfl

noncomputable section
local instance habfExamplesEq {δ : Type} : DecidableEq (Formula δ) := Classical.decEq _

def nestedDecision :
    Certificate false (∅ : Context (Fin 1)) (.disj nested.expand (.neg nested.expand)) := by
  exact decision nested

def nestedStability :
    Certificate false (∅ : Context (Fin 1)) (.impl (.neg (.neg nested.expand)) nested.expand) := by
  exact stability nested

def nestedZero :
    Certificate false (∅ : Context (Fin 1)) (nested.subst (fun _ => zeroTerm)).expand := by
  exact historyZero _

def nestedSuccessor {β : Type} (a : LA.Term β) :
    Certificate false (∅ : Context β)
      (iffFormula (nested.subst (fun _ => succTerm a)).expand
        (.conj (nested.subst (fun _ => a)).expand
          (inclusiveExists
            (.disj
              (termEqual (a.relabel Sum.inl)
                (addTerm (.var (.inr ())) (.var (.inr ()))))
              (termEqual (a.relabel Sum.inl)
                (succTerm (addTerm (.var (.inr ())) (.var (.inr ()))))))
            a))) := by
  let A : Formula (β ⊕ Unit) :=
    inclusiveExists
      (.disj
        (termEqual (.var (.inl (.inr ()))) (addTerm (.var (.inr ())) (.var (.inr ()))))
        (termEqual (.var (.inl (.inr ())))
          (succTerm (addTerm (.var (.inr ())) (.var (.inr ()))))))
      (.var (.inr ()))
  have h := historySuccessor (Γ := (∅ : Context β)) A a
  simpa [nested, nestedBody, parityBody, Expr.subst, Expr.expand, unitSubst,
    atTerm, A, inclusiveExists, exUnit_subst, subst_conj, subst_disj,
    termEqual_subst_poly, Term.subst,
    Lemmatheca.MathematicalLogic.FirstOrderProofs.term_subst_relabel] using h

end
end Lemmatheca.Entry.HeytingArithmeticBoundedFormulas
