import Lemmatheca.HeytingArithmetic.Equality

namespace Lemmatheca.ProofTheory.HeytingArithmetic.Addition
open _root_.FirstOrder _root_.FirstOrder.Language
noncomputable section

/-- The displayed left-zero equation over one ordered original parameter. -/
def zeroLeftBody : Formula (Fin 1) :=
  termEqual (addTerm zeroTerm (.var 0)) (.var 0)

def successorLeftBody : Formula (Fin 2) :=
  termEqual (addTerm (succTerm (.var 0)) (.var 1))
    (succTerm (addTerm (.var 0) (.var 1)))

def associativityBody : Formula (Fin 3) :=
  termEqual (addTerm (addTerm (.var 0) (.var 1)) (.var 2))
    (addTerm (.var 0) (addTerm (.var 1) (.var 2)))

def commutativityBody : Formula (Fin 2) :=
  termEqual (addTerm (.var 0) (.var 1)) (addTerm (.var 1) (.var 0))

def exchangeBody : Formula (Fin 3) :=
  termEqual (addTerm (addTerm (.var 0) (.var 1)) (.var 2))
    (addTerm (addTerm (.var 0) (.var 2)) (.var 1))

def cancelLeftBody : Formula (Fin 3) :=
  .impl (termEqual (addTerm (.var 0) (.var 1)) (addTerm (.var 0) (.var 2)))
    (termEqual (.var 1) (.var 2))

def cancelRightBody : Formula (Fin 3) :=
  .impl (termEqual (addTerm (.var 1) (.var 0)) (addTerm (.var 2) (.var 0)))
    (termEqual (.var 1) (.var 2))

def zeroLeftSentence : Sentence := close zeroLeftBody
def successorLeftSentence : Sentence := close successorLeftBody
def associativitySentence : Sentence := close associativityBody
def commutativitySentence : Sentence := close commutativityBody
def exchangeSentence : Sentence := close exchangeBody
def cancelLeftSentence : Sentence := close cancelLeftBody
def cancelRightSentence : Sentence := close cancelRightBody

open Lemmatheca.ProofTheory.FirstOrder.BoundedFormula
universe u
local instance haAdditionStatementsEq {β : Type*} : DecidableEq (Formula β) := Classical.decEq _

/-- The supplied closed certificate is literally renamed, instantiated and weakened. -/
def instantiateClosed {α : Type u} {k} (D : Formula (Fin k))
    (p : Certificate false (∅ : Context Empty) (close D))
    (ts : Fin k → LA.Term α) (Γ : Context α) : Certificate false Γ (D.subst ts) := by
  have q : Certificate false (∅ : Context α)
      ((close D).rename (Empty.elim : Empty → α)) := by
    simpa only [Finset.image_empty] using
      p.universeRename (Empty.elim : Empty → α)
  exact (TheoryCertificate.closeElim D ts q).weaken (Finset.empty_subset _)


end
end Lemmatheca.ProofTheory.HeytingArithmetic.Addition
