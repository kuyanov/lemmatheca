import Lemmatheca.PaProofCheckers.PAProofSpecializationPrograms
import Lemmatheca.PaProofCheckers.PAProofAxiomVerifier
import Lemmatheca.PaProofCheckers.PAProofRulePrograms
import Lemmatheca.PaProofCheckers.PAProofFixedCertificates
import Lemmatheca.PaListsAndSyntax.PAFixedSyntaxPrograms

open Lemmatheca.MathematicalLogic Lemmatheca.ModelTheory Lemmatheca.ComputabilityTheory

/-! Explicit proof-record programs for numerical equations. Fixed PA theorem
certificates are genuine finite proofs; arbitrary numerical inputs are handled
by the native proof constructors and primitive recursion below. -/
namespace Lemmatheca.ProofTheory.PAComputations.ProofPrograms.CheckerPrograms.NumericalProofs
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic ArithmeticTheories ArithmeticRepresentability FirstOrderProofs
open SyntaxPrograms
noncomputable section

private theorem qAxiom {A : language.Sentence} (hA : A ∈ Q) : Derives PA A :=
  derives_assumption (Or.inl hA)

def qAddZeroProof : ℕ := fixedCertificate qAddZero (qAxiom (by simp [Q]))
def qAddSuccProof : ℕ := fixedCertificate qAddSucc (qAxiom (by simp [Q]))
def qMulZeroProof : ℕ := fixedCertificate qMulZero (qAxiom (by simp [Q]))
def qMulSuccProof : ℕ := fixedCertificate qMulSucc (qAxiom (by simp [Q]))

def zeroCode {r : ℕ} : Program r := syntaxNode 2 [constant 0]
def succCode {r : ℕ} (a : Program r) : Program r := syntaxNode 2 [constant 1, a]
def addCode {r : ℕ} (a b : Program r) : Program r := syntaxNode 2 [constant 2, a, b]
def mulCode {r : ℕ} (a b : Program r) : Program r := syntaxNode 2 [constant 3, a, b]
def boundZero {r : ℕ} : Program r := syntaxNode 1 [constant 0]
/-- Inputs p,q,a,b,c, where p proves a=b and q proves b=c. -/
def transitivity : Program 5 :=
  .comp equalitySubstitutionCertificate ![.proj 1, .proj 0,
    equalCode (.proj 2) boundZero, .proj 3, .proj 4]

def composeEquality {r : ℕ} (p q a b c : Program r) : Program r :=
  .comp transitivity ![p, q, a, b, c]

/-- Inputs p,a,b; replace the hole of the displayed unary term context. -/
def unaryCongruence (frame : Program 1) : Program 3 :=
  let a := unary frame (.proj 1)
  let body := equalCode a (unary frame boundZero)
  .comp equalitySubstitutionCertificate ![.proj 0,
    unary equalityReflexivityCertificate a, body, .proj 1, .proj 2]

/-- Inputs p,a,b,parameter; the frame sees parameter, then the hole. -/
def parametricCongruence (frame : Program 2) : Program 4 :=
  let a := binary frame (.proj 3) (.proj 1)
  let body := equalCode a (binary frame (.proj 3) boundZero)
  .comp equalitySubstitutionCertificate ![.proj 0,
    unary equalityReflexivityCertificate a, body, .proj 1, .proj 2]

def succFrame : Program 1 := succCode (.proj 0)
def addLeftFrame : Program 2 := addCode (.proj 1) (.proj 0)
def addRightFrame : Program 2 := addCode (.proj 0) (.proj 1)
def mulLeftFrame : Program 2 := mulCode (.proj 1) (.proj 0)
def mulRightFrame : Program 2 := mulCode (.proj 0) (.proj 1)

def additionBase : Program 1 := specializeOne (constant qAddZeroProof) (num (.proj 0))

def additionStep : Program 3 :=
  let m : Program 3 := .proj 0
  let n : Program 3 := .proj 1
  let prev : Program 3 := .proj 2
  let a := num m
  let b := num n
  let result := num (binary addition m n)
  let axiomProof :=  specializeOne (specializeOne (constant qAddSuccProof) a) b
  let cong := .comp (unaryCongruence succFrame) ![prev, addCode a b, result]
  composeEquality axiomProof cong (addCode a (succCode b)) (succCode (addCode a b)) (succCode result)

def additionBuilder : Program 2 := .prec additionBase additionStep

def multiplicationBase : Program 1 := specializeOne (constant qMulZeroProof) (num (.proj 0))

def multiplicationStep : Program 3 :=
  let m : Program 3 := .proj 0
  let n : Program 3 := .proj 1
  let prev : Program 3 := .proj 2
  let a := num m
  let b := num n
  let product := num (binary multiplication m n)
  let axiomProof :=  specializeOne (specializeOne (constant qMulSuccProof) a) b
  let cong := .comp (parametricCongruence addLeftFrame) ![prev, mulCode a b, product, a]
  let step := composeEquality axiomProof cong (mulCode a (succCode b))
    (addCode (mulCode a b) a) (addCode product a)
  composeEquality step (binary additionBuilder (binary multiplication m n) m)
    (mulCode a (succCode b)) (addCode product a)
    (num (binary addition (binary multiplication m n) m))

def multiplicationBuilder : Program 2 := .prec multiplicationBase multiplicationStep

def termBuilder {r : ℕ} : language.Term (Fin r) → Program r
  | .var i => unary equalityReflexivityCertificate (num (.proj i))
  | .func .zero _ => unary equalityReflexivityCertificate zeroCode
  | .func .succ ts => .comp (unaryCongruence succFrame)
      ![termBuilder (ts 0), FixedSyntaxPrograms.termInstance (ts 0),
        num (FixedSyntaxPrograms.termValue (ts 0))]
  | .func .add ts =>
    let s := FixedSyntaxPrograms.termInstance (ts 0)
    let t := FixedSyntaxPrograms.termInstance (ts 1)
    let m := FixedSyntaxPrograms.termValue (ts 0)
    let n := FixedSyntaxPrograms.termValue (ts 1)
    let a := num m
    let b := num n
    let left := .comp (parametricCongruence addLeftFrame) ![termBuilder (ts 0), s, a, t]
    let right := .comp (parametricCongruence addRightFrame) ![termBuilder (ts 1), t, b, a]
    let normalized := composeEquality left right (addCode s t) (addCode a t) (addCode a b)
    composeEquality normalized (binary additionBuilder m n) (addCode s t)
      (addCode a b) (num (binary addition m n))
  | .func .mul ts =>
    let s := FixedSyntaxPrograms.termInstance (ts 0)
    let t := FixedSyntaxPrograms.termInstance (ts 1)
    let m := FixedSyntaxPrograms.termValue (ts 0)
    let n := FixedSyntaxPrograms.termValue (ts 1)
    let a := num m
    let b := num n
    let left := .comp (parametricCongruence mulLeftFrame) ![termBuilder (ts 0), s, a, t]
    let right := .comp (parametricCongruence mulRightFrame) ![termBuilder (ts 1), t, b, a]
    let normalized := composeEquality left right (mulCode s t) (mulCode a t) (mulCode a b)
    composeEquality normalized (binary multiplicationBuilder m n) (mulCode s t)
      (mulCode a b) (num (binary multiplication m n))

end
end Lemmatheca.ProofTheory.PAComputations.ProofPrograms.CheckerPrograms.NumericalProofs
