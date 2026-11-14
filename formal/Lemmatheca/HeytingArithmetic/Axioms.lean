import Lemmatheca.HeytingArithmetic.Syntax

/-! The native seven-axiom presentation and genuinely full induction schema. -/
namespace Lemmatheca.ProofTheory.HeytingArithmetic
open _root_.FirstOrder _root_.FirstOrder.Language
noncomputable section

private def x : LA.Term (Fin 1) := .var 0
private def x₂ : LA.Term (Fin 2) := .var 0
private def y₂ : LA.Term (Fin 2) := .var 1

def qSuccNeZero : Sentence := close (.neg (termEqual (succTerm x) zeroTerm))
def qSuccInjective : Sentence :=
  close (.impl (termEqual (succTerm x₂) (succTerm y₂)) (termEqual x₂ y₂))
def qPredecessor : Sentence :=
  close (.impl (.neg (termEqual x zeroTerm))
    (exUnit (termEqual (.var (.inl (0 : Fin 1))) (succTerm (.var (.inr ()))))))
def qAddZero : Sentence := close (termEqual (addTerm x zeroTerm) x)
def qAddSucc : Sentence :=
  close (termEqual (addTerm x₂ (succTerm y₂)) (succTerm (addTerm x₂ y₂)))
def qMulZero : Sentence := close (termEqual (mulTerm x zeroTerm) zeroTerm)
def qMulSucc : Sentence :=
  close (termEqual (mulTerm x₂ (succTerm y₂)) (addTerm (mulTerm x₂ y₂) x₂))

def basic : Set Sentence :=
  {qSuccNeZero, qSuccInjective, qPredecessor, qAddZero, qAddSucc, qMulZero, qMulSucc}

def basicSix : Set Sentence :=
  {qSuccNeZero, qSuccInjective, qAddZero, qAddSucc, qMulZero, qMulSucc}

/-- Substitute zero for the distinguished induction variable. -/
def base {k} (A : Formula (Fin k ⊕ Unit)) : Formula (Fin k) :=
  A.subst (Sum.elim Term.var (fun _ => zeroTerm))

/-- Advance just that variable, retaining every fixed finite parameter. -/
def next {k} (A : Formula (Fin k ⊕ Unit)) : Formula (Fin k ⊕ Unit) :=
  A.subst (Sum.elim (fun i => .var (.inl i)) (fun _ => succTerm (.var (.inr ()))))

/-- Every native full body is permitted, including primitive disjunction/exists. -/
def inductionAxiom {k} (A : Formula (Fin k ⊕ Unit)) : Sentence :=
  close (.impl (.conj (base A) (allUnit (.impl A (next A)))) (allUnit A))

def inductionTheory : Set Sentence :=
  {θ | ∃ k : ℕ, ∃ A : Formula (Fin k ⊕ Unit), θ = inductionAxiom A}

def theory : Set Sentence := basic ∪ inductionTheory
def sixTheory : Set Sentence := basicSix ∪ inductionTheory

/-- An explicit full closed formula for zero-or-successor alternatives. -/
def zeroOrSuccessor : Sentence :=
  close (.disj (termEqual x zeroTerm)
    (exUnit (termEqual (.var (.inl (0 : Fin 1))) (succTerm (.var (.inr ()))))))

def zeroEqualityDecision : Sentence :=
  close (.disj (termEqual zeroTerm x) (.neg (termEqual zeroTerm x)))

def equalityDecision : Sentence :=
  close (.disj (termEqual x₂ y₂) (.neg (termEqual x₂ y₂)))

end
end Lemmatheca.ProofTheory.HeytingArithmetic
