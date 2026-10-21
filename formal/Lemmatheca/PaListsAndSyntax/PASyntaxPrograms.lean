import Lemmatheca.PaListsAndSyntax.PANativeSyntax

open Lemmatheca.MathematicalLogic Lemmatheca.ModelTheory Lemmatheca.ComputabilityTheory

/-! Internal syntax tests, auxiliary-name occurrence and finite list predicates. -/
namespace Lemmatheca.ProofTheory.PAComputations.ProofPrograms.CheckerPrograms
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic ArithmeticTheories ArithmeticRepresentability FirstOrderProofs
open SyntaxPrograms
noncomputable section
universe u

def conjunction {n : ℕ} (xs : List (Program n)) : Program n :=
  xs.foldr (fun a b => binary multiplication a b) (constant 1)

def booleanNot {n : ℕ} (a : Program n) : Program n := unary zeroTest a

def listAllStep (h : Program 2) : Program 3 :=
  binary multiplication (.proj 2) (binary h (.proj 0) (.proj 1))

/-- Inputs are a fixed parameter and an actual numerical list code. -/
def listAll (h : Program 2) : Program 2 :=
  ternary (paramFold (listAllStep h)) (.proj 0) (.proj 1) (constant 1)

def memberStep : Program 3 :=
  binary disjoin (.proj 2) (binary equalTest (.proj 0) (.proj 1))

def listMember : Program 2 :=
  ternary (paramFold memberStep) (.proj 0) (.proj 1) (constant 0)

def namedForm : Program 2 :=
  binary multiplication isForm
    (booleanNot (unary (part 2) (unary stats (.proj 1))))

def namedTerm : Program 1 :=
  binary multiplication (binary isTerm (constant 0) (.proj 0))
    (booleanNot (unary (part 2) stats))

def isSentence : Program 1 :=
  binary multiplication (binary namedForm (constant 0) (.proj 0))
    (booleanNot (unary (part 3) stats))

def instantiate : Program 2 :=
  ternary select
    (binary multiplication (binary namedForm (constant 1) (.proj 0))
      (unary namedTerm (.proj 1)))
    (.comp rewrite ![constant 2, constant 0, .proj 1, .proj 0]) (constant 0)

def occurrenceChild : Program 3 :=
  binary disjoin (.proj 2) (unary sign (binary listEntry (.proj 0) (.proj 1)))

def occursStep : Program 3 :=
  let j : Program 3 := .proj 0
  let e : Program 3 := .proj 1
  let h : Program 3 := .proj 2
  let tg := unary tag e
  ternary select (binary equalTest tg (constant 8))
    (binary equalTest (unary (argument 0) e) j)
    (ternary select
      (binary disjoin (binary equalTest tg (constant 0)) (binary equalTest tg (constant 1)))
      (constant 0)
      (ternary (paramFold occurrenceChild) h (unary children e) (constant 0)))

def occursAux : Program 2 := unary sign (courseValue occursStep)

def contextIncluded : Program 2 :=
  binary (listAll (binary listMember (.proj 1) (.proj 0))) (.proj 1) (.proj 0)

def contextFresh : Program 2 := listAll (booleanNot occursAux)

def formList : Program 2 := listAll (binary namedForm (constant 0) (.proj 1))

def bottom {n : ℕ} : Program n := syntaxNode 3 []
def equalCode {n : ℕ} (a b : Program n) : Program n := syntaxNode 4 [a, b]
def impCode {n : ℕ} (a b : Program n) : Program n := binary implication a b
def allCode {n : ℕ} (a : Program n) : Program n := syntaxNode 7 [a]
def negCode {n : ℕ} (a : Program n) : Program n := impCode a bottom
def andCode {n : ℕ} (a b : Program n) : Program n := negCode (impCode a (negCode b))
def orCode {n : ℕ} (a b : Program n) : Program n := impCode (negCode a) b
def exCode {n : ℕ} (a : Program n) : Program n := negCode (allCode (negCode a))
def auxCode {n : ℕ} (a : Program n) : Program n := syntaxNode 8 [a]


end
end Lemmatheca.ProofTheory.PAComputations.ProofPrograms.CheckerPrograms
