import Lemmatheca.HeytingArithmeticAddition.Statements

namespace Lemmatheca.ProofTheory.HeytingArithmetic.Multiplication
open _root_.FirstOrder _root_.FirstOrder.Language
noncomputable section

def zeroLeftBody : Formula (Fin 1) :=
  termEqual (mulTerm zeroTerm (.var 0)) zeroTerm

def oneLeftBody : Formula (Fin 1) :=
  termEqual (mulTerm (succTerm zeroTerm) (.var 0)) (.var 0)

def successorLeftBody : Formula (Fin 2) :=
  termEqual (mulTerm (succTerm (.var 0)) (.var 1))
    (addTerm (mulTerm (.var 0) (.var 1)) (.var 1))

def commutativityBody : Formula (Fin 2) :=
  termEqual (mulTerm (.var 0) (.var 1)) (mulTerm (.var 1) (.var 0))

def leftDistributivityBody : Formula (Fin 3) :=
  termEqual (mulTerm (.var 0) (addTerm (.var 1) (.var 2)))
    (addTerm (mulTerm (.var 0) (.var 1)) (mulTerm (.var 0) (.var 2)))

def rightDistributivityBody : Formula (Fin 3) :=
  termEqual (mulTerm (addTerm (.var 0) (.var 1)) (.var 2))
    (addTerm (mulTerm (.var 0) (.var 2)) (mulTerm (.var 1) (.var 2)))

def associativityBody : Formula (Fin 3) :=
  termEqual (mulTerm (mulTerm (.var 0) (.var 1)) (.var 2))
    (mulTerm (.var 0) (mulTerm (.var 1) (.var 2)))

def zeroLeftSentence : Sentence := close zeroLeftBody
def oneLeftSentence : Sentence := close oneLeftBody
def successorLeftSentence : Sentence := close successorLeftBody
def commutativitySentence : Sentence := close commutativityBody
def leftDistributivitySentence : Sentence := close leftDistributivityBody
def rightDistributivitySentence : Sentence := close rightDistributivityBody
def associativitySentence : Sentence := close associativityBody

end
end Lemmatheca.ProofTheory.HeytingArithmetic.Multiplication
