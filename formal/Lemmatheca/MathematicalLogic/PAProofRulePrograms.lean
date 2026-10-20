import Lemmatheca.MathematicalLogic.PAProofCheckerPrograms

/-! Actual proof-record constructors used by the arithmetic proof builders.
These preserve the corpus's numerical certificate format; they introduce no
new inference rules. -/
namespace Lemmatheca.MathematicalLogic.PAComputations.ProofPrograms.CheckerPrograms
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic ArithmeticTheories ArithmeticRepresentability
open SyntaxPrograms
noncomputable section
universe u

def root {n : ℕ} (p : Program n) : Program n := binary listEntry p (constant 0)
def witnesses {n : ℕ} (p : Program n) : Program n := binary listEntry p (constant 1)
def context {n : ℕ} (d : Program n) : Program n := unary (argument 0) d
def conclusion {n : ℕ} (d : Program n) : Program n := unary (argument 1) d

def certificateAt {n : ℕ} (d w : Program n) : Program n := list [d, w]
def retainWitnesses {n : ℕ} (p d : Program n) : Program n := certificateAt d (witnesses p)

/-- Inputs: accepted certificate, quantified body code, closed term code. -/
def forallEliminationCertificate : Program 3 :=
  let p : Program 3 := .proj 0
  let b : Program 3 := .proj 1
  let t : Program 3 := .proj 2
  retainWitnesses p (syntaxNode 113 [context (root p), binary instantiate b t, root p, b, t])

def existentialIntroductionCertificate : Program 3 :=
  let p : Program 3 := .proj 0
  let b : Program 3 := .proj 1
  let t : Program 3 := .proj 2
  retainWitnesses p (syntaxNode 114 [context (root p), exCode b, root p, b, t])

/-- Inputs: equality certificate, instance certificate, one-slot formula body,
source term, target term. Both axiom-certificate lists are retained. -/
def equalitySubstitutionCertificate : Program 5 :=
  let p : Program 5 := .proj 0
  let q : Program 5 := .proj 1
  let b : Program 5 := .proj 2
  let s : Program 5 := .proj 3
  let t : Program 5 := .proj 4
  certificateAt
    (syntaxNode 118 [binary listAppend (context (root p)) (context (root q)),
      binary instantiate b t, root p, root q, b, s, t])
    (binary listAppend (witnesses p) (witnesses q))

/-- Inputs: a closed term. Reflexivity has empty axiom context. -/
def equalityReflexivityCertificate : Program 1 :=
  let t : Program 1 := .proj 0
  certificateAt (syntaxNode 117 [constant 0, equalCode t t, t]) (constant 0)

def rootValue {M : Type u} [language.Structure M] [M ⊨ PA] (p : M) : M :=
  listEntry.value ![p, zeroValue M]
def witnessesValue {M : Type u} [language.Structure M] [M ⊨ PA] (p : M) : M :=
  listEntry.value ![p, numeralValue M 1]
def contextValue {M : Type u} [language.Structure M] [M ⊨ PA] (d : M) : M :=
  (argument 0).value ![d]
def conclusionValue {M : Type u} [language.Structure M] [M ⊨ PA] (d : M) : M :=
  (argument 1).value ![d]

/-- A raw proof record is checked in its displayed axiom context. -/
def Checked {M : Type u} [language.Structure M] [M ⊨ PA] (d gamma a : M) : Prop :=
  derivationCheck.value ![d] = numeralValue M 1 ∧
    (argument 0).value ![d] = gamma ∧ (argument 1).value ![d] = a

/-- Acceptance by this native presentation of the actual certificate checker. -/
def Certified {M : Type u} [language.Structure M] [M ⊨ PA]
    (E : Program 2) (p a : M) : Prop :=
  (certificateCheck E).value ![p, a] = numeralValue M 1

end
end Lemmatheca.MathematicalLogic.PAComputations.ProofPrograms.CheckerPrograms
