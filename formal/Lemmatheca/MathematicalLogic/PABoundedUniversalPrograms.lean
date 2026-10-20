import Lemmatheca.MathematicalLogic.PAInitialSegmentCertificates
import Lemmatheca.MathematicalLogic.PAProofEqualityReversal
import Lemmatheca.MathematicalLogic.PABoundedTruthPrograms

/-! A concrete certificate loop for positive bounded universal statements.
The body is an actual native formula code with one available outer slot. -/
namespace Lemmatheca.MathematicalLogic.PAComputations.ProofPrograms.CheckerPrograms.BoundedUniversalPrograms
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic ArithmeticTheories ArithmeticRepresentability FirstOrderProofs
open ArithmeticProofPredicates SyntaxPrograms FixedSyntaxPrograms InitialSegmentPrograms
noncomputable section
universe u

def matrix {r : ℕ} (body n : Program r) : Program r :=
  impCode (upperAt 1 (syntaxNode 1 [constant 0]) n) body

def boundedCode {r : ℕ} (body : Program r) : Program (r + 1) :=
  allCode (matrix (BoundedTruthPrograms.lift body) (.proj (Fin.last r)))

/-- Inputs are a certificate for the body at zero and the one-slot body code. -/
def baseCertificate : Program 2 :=
  let p : Program 2 := .proj 0
  let body : Program 2 := .proj 1
  let q : Program 2 := fixedProof (initialSegmentSentence 0) initial_segment_zero_derives
  let gamma := binary listAppend (context (root q)) (context (root p))
  let z : Program 2 := syntaxNode 8 [constant 0]
  let indexZero : Program 2 := constant 0
  let termZero := unary ProofPrograms.numeral indexZero
  let a := upperAt 0 z indexZero
  let eq := equalCode z termZero
  let out := binary instantiate body z
  let ext := binary listCons a gamma
  let qbody := unary (argument 0) (conclusion (root q))
  let qinst := binary instantiate qbody z
  let q1 := syntaxNode 113 [gamma, qinst, root q, qbody, z]
  let ass := syntaxNode 100 [ext, a]
  let eqProof := syntaxNode 108 [ext, eq, q1, ass]
  let transport := Program.comp transportAlongEqualityRecord ![ext, eqProof, root p, body, z, termZero]
  let discharged := syntaxNode 107 [gamma, impCode a out, transport, a]
  let b := matrix body indexZero
  certificateAt (syntaxNode 115 [gamma, allCode b, discharged, b, indexZero])
    (binary listAppend (witnesses q) (witnesses p))

/-- Inputs: n, the previous bounded-universal certificate, the body certificate
at n+1, and the one-slot body code. -/
def stepCertificate : Program 4 :=
  let n : Program 4 := .proj 0
  let p : Program 4 := .proj 1
  let next : Program 4 := .proj 2
  let body : Program 4 := .proj 3
  let q : Program 4 := fixedProof stepSentence step_sentence_derives
  let gamma := binary listAppend (context (root p))
    (binary listAppend (context (root q)) (context (root next)))
  let z : Program 4 := syntaxNode 8 [constant 0]
  let a := upperAt 0 z (unary .succ n)
  let b := upperAt 0 z n
  let c := equalCode z (unary ProofPrograms.numeral (unary .succ n))
  let out := binary instantiate body z
  let ext := binary listCons a gamma
  let left := binary listCons b ext
  let right := binary listCons c ext
  let qbody := unary (argument 0) (conclusion (root q))
  let qfirst := binary instantiate qbody (unary ProofPrograms.numeral n)
  let q1 := syntaxNode 113 [gamma, qfirst, root q, qbody, unary ProofPrograms.numeral n]
  let qinner := unary (argument 0) qfirst
  let qsecond := binary instantiate qinner z
  let q2 := syntaxNode 113 [gamma, qsecond, q1, qinner, z]
  let ass := syntaxNode 100 [ext, a]
  let dichotomy := syntaxNode 108 [ext, orCode b c, q2, ass]
  let pbody := unary (argument 0) (conclusion (root p))
  let pinst := binary instantiate pbody z
  let p1 := syntaxNode 113 [gamma, pinst, root p, pbody, z]
  let pass := syntaxNode 100 [left, b]
  let dl := syntaxNode 108 [left, out, p1, pass]
  let eqass := syntaxNode 100 [right, c]
  let dr := Program.comp transportAlongEqualityRecord
    ![right, eqass, root next, body, z, unary ProofPrograms.numeral (unary .succ n)]
  let cases := syntaxNode 106 [ext, out, dichotomy, dl, dr, b, c]
  let discharged := syntaxNode 107 [gamma, impCode a out, cases, a]
  let targetBody := matrix body (unary .succ n)
  certificateAt (syntaxNode 115 [gamma, allCode targetBody, discharged, targetBody, constant 0])
    (binary listAppend (witnesses p) (binary listAppend (witnesses q) (witnesses next)))

def forallBoundedBuilder {r : ℕ} (body : Program r) (positive : Program (r + 1)) : Program (r + 1) :=
  .prec
    (binary baseCertificate
      (.comp positive (Fin.snoc (fun i => .proj i) (constant 0))) body)
    (.comp stepCertificate ![
      .proj (Fin.last r).castSucc,
      .proj (Fin.last (r + 1)),
      .comp positive (Fin.snoc (fun i : Fin r => .proj (i.castAdd 2))
        (unary .succ (.proj (Fin.last r).castSucc))),
      .comp body (fun i : Fin r => .proj (i.castAdd 2))])

section Internal
variable {M : Type u} [language.Structure M] [M ⊨ PA]

theorem syntaxNode_model_value {r : ℕ} (k : ℕ) (ps : List (Program r)) (x : Fin r → M) :
    (syntaxNode k ps).value x = modelNode k (ps.map (fun p => p.value x)) := by
  rw [syntaxNode_value, FixedSyntaxPrograms.list_value]
  rfl

theorem root_program_value {r : ℕ} (p : Program r) (x : Fin r → M) :
    (root p).value x = rootValue (p.value x) := by
  simp only [root, binary_value, constant_value, numeral_value_zero, rootValue]

theorem context_program_value {r : ℕ} (p : Program r) (x : Fin r → M) :
    (context p).value x = contextValue (p.value x) := by
  simp only [context, unary_value, contextValue]

theorem conclusion_program_value {r : ℕ} (p : Program r) (x : Fin r → M) :
    (conclusion p).value x = conclusionValue (p.value x) := by
  simp only [conclusion, unary_value, conclusionValue]

theorem witnesses_program_value {r : ℕ} (p : Program r) (x : Fin r → M) :
    (witnesses p).value x = witnessesValue (p.value x) := by
  simp only [witnesses, binary_value, constant_value, witnessesValue]

def matrixValue (body n : M) : M :=
  implication.value ![upperValue 1 (modelNode 1 [zeroValue M]) n, body]

theorem matrix_model_value {r : ℕ} (body n : Program r) (x : Fin r → M) :
    (matrix body n).value x = matrixValue (body.value x) (n.value x) := by
  simp only [matrix, impCode, binary_value, upperAt_model_value, syntaxNode_value,
    list_cons_value, list_nil_value, constant_value, numeral_value_zero,
    matrixValue, modelNode, modelList_cons, modelList_nil]

theorem boundedCode_model_value {r : ℕ} (body : Program r) (x : Fin r → M) (n : M) :
    (boundedCode body).value (Fin.snoc x n) = modelNode 7 [matrixValue (body.value x) n] := by
  rw [boundedCode, allCode_value, matrix_model_value, BoundedTruthPrograms.lift_value,
    Program.value_proj, Fin.snoc_last]

theorem matrix_bound (body n : M) (hb : FormulaBound 1 body) : FormulaBound 1 (matrixValue body n) := by
  rw [matrixValue, implication_node_value]
  exact FormulaBound.imp (upperValue_bound 1 _ n bound_zero_termBound) hb

theorem matrix_namedForm (body n : M) (hb : FormulaBound 1 body) :
    namedForm.value ![numeralValue M 1, matrixValue body n] = numeralValue M 1 :=
  (matrix_bound body n hb).namedForm

theorem matrix_sentence (body n : M) (hb : FormulaBound 1 body) :
    isSentence.value ![modelNode 7 [matrixValue body n] ] = numeralValue M 1 :=
  isSentence_of_stats _ ((FormulaBound.all (matrix_bound body n hb)).pure)

theorem matrix_instantiate (body n : M) (hb : FormulaBound 1 body) :
    instantiate.value ![matrixValue body n, modelNode 8 [zeroValue M] ] =
      implication.value ![upperValue 0 (modelNode 8 [zeroValue M]) n,
        instantiate.value ![body, modelNode 8 [zeroValue M] ] ] := by
  rw [instantiate_value_of_tests _ _ (matrix_namedForm body n hb) aux_zero_namedTerm]
  simp only [matrixValue, implication_node_value]
  rw [rewrite_slot_imp_value, upperValue_rewrite 0, rewrite_slot_bound_zero_value,
    ← instantiate_value_of_tests _ _ hb.namedForm aux_zero_namedTerm]

theorem matrix_occursAux_zero (j body n : M)
    (hb : occursAux.value ![j, body] = zeroValue M) :
    occursAux.value ![j, matrixValue body n] = zeroValue M := by
  rw [matrixValue, implication_node_value]
  apply occursAux_modelNode_zero j 6 _ (by decide)
  intro a ha
  simp only [Nat.reduceEqDiff, or_self, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl
  · exact upperValue_occursAux_zero 1 j _ n (occursAux_original_leaf_zero j 1 _ (Or.inr rfl))
  · exact hb

end Internal
end
end Lemmatheca.MathematicalLogic.PAComputations.ProofPrograms.CheckerPrograms.BoundedUniversalPrograms
