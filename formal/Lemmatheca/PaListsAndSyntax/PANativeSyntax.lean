import Lemmatheca.PaListsAndSyntax.PAHistoryPrograms
import Lemmatheca.PaListsAndSyntax.PAParametricFold
import Lemmatheca.CodingFormalProofs.CodingFormalProofsComputability

open Lemmatheca.MathematicalLogic Lemmatheca.ModelTheory Lemmatheca.ComputabilityTheory

/-! Native program presentations of the shared arithmetic syntax algorithms.
All branches and course-of-values histories are explicit program DAGs. -/
namespace Lemmatheca.ProofTheory.PAComputations.ProofPrograms.SyntaxPrograms
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic ArithmeticTheories ArithmeticRepresentability
noncomputable section
universe u

def unary {n : ℕ} (p : Program 1) (a : Program n) : Program n := .comp p ![a]
def binary {n : ℕ} (p : Program 2) (a b : Program n) : Program n := .comp p ![a, b]
def ternary {n : ℕ} (p : Program 3) (a b c : Program n) : Program n := .comp p ![a, b, c]

def equalTest : Program 2 :=
  unary zeroTest (binary addition subtraction (binary subtraction (.proj 1) (.proj 0)))

def maximum : Program 2 := ternary select less (.proj 1) (.proj 0)
def disjoin : Program 2 := unary sign addition

def quad {n : ℕ} (a b c d : Program n) : Program n :=
  binary squarePair a (binary squarePair b (binary squarePair c d))

def part : Fin 4 → Program 1
  | 0 => unpairLeft
  | 1 => unary unpairLeft unpairRight
  | 2 => unary unpairLeft (unary unpairRight unpairRight)
  | 3 => unary unpairRight (unary unpairRight unpairRight)

def tag : Program 1 := unary unpairLeft predecessor
def args : Program 1 := unary unpairRight predecessor
def argument (i : ℕ) : Program 1 := binary listEntry args (constant i)

def children : Program 1 :=
  ternary select
    (binary disjoin (binary equalTest tag (constant 2)) (binary equalTest tag (constant 5)))
    (unary listTail args) args

/-- Accumulate the maximum of one component of the earlier child summaries. -/
def maxSummary (i : Fin 4) : Program 3 :=
  binary maximum (.proj 2) (unary (part i) (binary listEntry (.proj 0) (.proj 1)))

def goodSummary (i : Fin 4) : Program 3 :=
  binary multiplication (.proj 2)
    (unary sign (unary (part i) (binary listEntry (.proj 0) (.proj 1))))

def foldSummary (h : Program 3) (initial : ℕ) : Program 2 :=
  ternary (paramFold h) (.proj 1) (unary children (.proj 0)) (constant initial)

def arithmeticFunctionTest : Program 2 :=
  binary disjoin
    (binary disjoin
      (binary multiplication (binary equalTest (.proj 0) (constant 0))
        (binary equalTest (.proj 1) (constant 0)))
      (binary multiplication (binary equalTest (.proj 0) (constant 1))
        (binary equalTest (.proj 1) (constant 1))))
    (binary multiplication
      (binary disjoin (binary equalTest (.proj 0) (constant 2))
        (binary equalTest (.proj 0) (constant 3)))
      (binary equalTest (.proj 1) (constant 2)))

/-- Inputs are the current syntax code and its table of prior summaries. -/
def summaryStep : Program 2 :=
  let e : Program 2 := .proj 0
  let a := unary args e
  let len := unary listLength a
  let first := unary listHead a
  let td := foldSummary (maxSummary 0) 1
  let fd := foldSummary (maxSummary 1) 1
  let fv := foldSummary (maxSummary 2) 0
  let av := foldSummary (maxSummary 3) 0
  let goodT := foldSummary (goodSummary 0) 1
  let goodF := foldSummary (goodSummary 1) 1
  let lenIs (n : ℕ) := binary equalTest len (constant n)
  let atTag (n : ℕ) := binary equalTest (unary tag e) (constant n)
  let choose := ternary select
  let invalid : Program 2 := constant 0
  choose e
    (choose (atTag 0) (choose (lenIs 1) (quad (constant 1) (constant 0) (constant 1) (constant 0)) invalid)
    (choose (atTag 1) (choose (lenIs 1)
      (quad (binary addition first (constant 2)) (constant 0) (constant 0) (constant 0)) invalid)
    (choose (atTag 2) (choose
      (binary multiplication (unary sign len)
        (binary multiplication (binary arithmeticFunctionTest first (unary predecessor len)) goodT))
      (quad td (constant 0) fv av) invalid)
    (choose (atTag 3) (choose (lenIs 0) (quad (constant 0) (constant 1) (constant 0) (constant 0)) invalid)
    (choose (atTag 4) (choose (binary multiplication (lenIs 2) goodT) (quad (constant 0) td fv av) invalid)
    (choose (atTag 6) (choose (binary multiplication (lenIs 2) goodF) (quad (constant 0) fd fv av) invalid)
    (choose (atTag 7) (choose (binary multiplication (lenIs 1) goodF)
      (quad (constant 0) (binary maximum (constant 1) (unary predecessor fd)) fv av) invalid)
    (choose (atTag 8) (choose (lenIs 1)
      (quad (constant 1) (constant 0) (constant 0) (binary addition first (constant 1))) invalid)
      invalid)))))))) invalid

def stats : Program 1 := courseValue summaryStep

def depthTest (i : Fin 4) : Program 2 :=
  let d := unary (part i) (unary stats (.proj 1))
  binary multiplication (unary sign d) (binary leq d (unary .succ (.proj 0)))

def isTerm : Program 2 := depthTest 0
def isForm : Program 2 := depthTest 1

def mapStep (h : Program 2) : Program 3 :=
  binary listCons (binary h (.proj 0) (.proj 1)) (.proj 2)

/-- Inputs are the fixed parameter and the coded list to map. -/
def listMap (h : Program 2) : Program 2 :=
  ternary (paramFold (mapStep h)) (.proj 0) (unary listReverse (.proj 1)) (constant 0)

/-- Inputs are mode, replaced name, replacement term, current code, prior history. -/
def rewriteStep : Program 5 :=
  let mode : Program 5 := .proj 0
  let i : Program 5 := .proj 1
  let t : Program 5 := .proj 2
  let e : Program 5 := .proj 3
  let hist : Program 5 := .proj 4
  let tg := unary tag e
  let a := unary args e
  let first := unary listHead a
  let eq := binary equalTest
  let choose := ternary select
  let replaceAt (m : ℕ) := binary multiplication (eq mode (constant m)) (eq first i)
  choose e
    (choose (eq tg (constant 0)) (choose (replaceAt 0) t e)
    (choose (eq tg (constant 8)) (choose (replaceAt 1) t e)
    (choose (eq tg (constant 1))
      (choose (eq mode (constant 2))
        (choose first (binary listCons (constant 1)
          (binary listCons (unary predecessor first) (constant 0))) t) e)
      (binary listCons tg
        (choose (binary disjoin (eq tg (constant 2)) (eq tg (constant 5)))
          (binary listCons first (binary (listMap listEntry) hist (unary listTail a)))
          (binary (listMap listEntry) hist a))))))
    (constant 0)

def rewrite : Program 4 := courseValue rewriteStep

def substitute : Program 4 :=
  ternary select
    (binary multiplication (binary isForm (.proj 0) (.proj 1))
      (binary isTerm (constant 0) (.proj 3)))
    (.comp rewrite ![constant 0, .proj 2, .proj 3, .proj 1])
    (constant 0)

end
end Lemmatheca.ProofTheory.PAComputations.ProofPrograms.SyntaxPrograms
