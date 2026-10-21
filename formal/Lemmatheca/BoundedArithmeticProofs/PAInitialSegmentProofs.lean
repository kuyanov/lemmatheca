import Lemmatheca.BoundedArithmeticProofs.PAInitialSegmentSyntax
import Lemmatheca.PaListsAndSyntax.PAFixedSyntaxPrograms
import Lemmatheca.PaProofCheckers.PAProofAxiomVerifier
import Lemmatheca.PaProofCheckers.PAProofLocalRules
import Lemmatheca.PaProofCheckers.PAProofUniversalElimination
import Lemmatheca.PaListsAndSyntax.PANativeInstantiation
import Lemmatheca.PaListsAndSyntax.PANativeSyntaxEvalHelpers
import Lemmatheca.PaProofCheckers.PAProofFixedFreshness
import Lemmatheca.PaProofCheckers.PAProofNaturalDeduction
import Lemmatheca.BoundedArithmeticProofs.PAProofFiniteCases
import Lemmatheca.PaListsAndSyntax.PAModelSyntax

open Lemmatheca.MathematicalLogic Lemmatheca.ModelTheory Lemmatheca.ComputabilityTheory

/-! Explicit certificate recursion for the finite initial-segment sentences.
Only fixed finite PA proofs are reused as constant certificates; the growing
proof is assembled by the actual native CoreProof record constructors. -/
namespace Lemmatheca.ProofTheory.PAComputations.ProofPrograms.InitialSegmentPrograms
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic ArithmeticTheories ArithmeticRepresentability FirstOrderProofs
open ArithmeticProofPredicates SyntaxPrograms CheckerPrograms
noncomputable section
universe u

def stepBody : language.Formula (Unit ⊕ Unit) :=
  let u : language.Term (Unit ⊕ Unit) := .var (.inl ())
  let x : language.Term (Unit ⊕ Unit) := .var (.inr ())
  (leFormula x (succTerm u)).imp ((leFormula x u) ⊔ x.equal (succTerm u))

def stepSentence : language.Sentence := allClose (stepBody.iAlls Unit)

theorem initial_segment_zero_derives : Derives PA (initialSegmentSentence 0) := by
  apply HenkinCompleteness.deductive_completeness
  apply Theory.models_sentence_iff.mpr
  intro M
  rw [initialSegmentSentence, realize_allClose]
  intro v
  simp only [initialSegmentDisjunction, Formula.realize_imp, realize_leFormula,
    Formula.realize_equal, Term.realize_var, realize_numeralTerm, realize_zeroTerm,
    numeral_value_zero]
  intro hle
  exact le_antisymm_value hle (zero_le_value _)

theorem step_sentence_derives : Derives PA stepSentence := by
  apply HenkinCompleteness.deductive_completeness
  apply Theory.models_sentence_iff.mpr
  intro M
  rw [stepSentence, realize_allClose]
  intro v
  rw [Formula.realize_iAlls]
  intro w
  simp only [stepBody, Formula.realize_imp, Formula.realize_sup, Formula.realize_equal,
    realize_leFormula, Term.realize_var, realize_succTerm, Sum.elim_inl, Sum.elim_inr]
  intro hx
  let := modelLinearOrder M
  by_cases hle : leValue M (w ()) (v ())
  · exact Or.inl hle
  · apply Or.inr
    have hlt : v () < w () := lt_of_not_ge hle
    have hsucc : leValue M (succValue M (v ())) (w ()) :=
      (successor_le_iff_lt _ _).mpr hlt
    exact le_antisymm_value hx hsucc

/-- Closing one free variable uses bound slot zero, and shifts the existing
inner bound variables by one. The finite enumeration of `Unit` is immaterial. -/
theorem unit_closure_code (A : language.Formula Unit) :
    CodingFormalProofs.sentenceCode CodingFormalProofs.arithmeticSignature (allClose A) =
      CodingFormalProofs.allCode
        (CodingFormalProofs.codeAt CodingFormalProofs.arithmeticSignature
          (fun _ : Unit => CodingFormalProofs.boundName 0) 1 A) := by
  have aux (n : ℕ) (e : Unit ≃ Fin n) :
      CodingFormalProofs.formulaCode CodingFormalProofs.arithmeticSignature Empty.elim
        ((BoundedFormula.relabel (Sum.map id e) (A.relabel (Sum.inr : Unit → Empty ⊕ Unit))).alls) =
        CodingFormalProofs.allCode
          (CodingFormalProofs.codeAt CodingFormalProofs.arithmeticSignature
            (fun _ : Unit => CodingFormalProofs.boundName 0) 1 A) := by
    have hn : n = 1 := by simpa only [Fintype.card_fin, Fintype.card_unique] using
      (Fintype.card_congr e).symm
    subst n
    change CodingFormalProofs.allCode
      (CodingFormalProofs.formulaCode CodingFormalProofs.arithmeticSignature Empty.elim
        (BoundedFormula.relabel (Sum.map id e) (A.relabel Sum.inr))) = _
    rw [← CodingFormalProofs.codeAt_zero]
    rw [CodingFormalProofs.codeAt_relabel]
    have hname :
        (fun x : Empty ⊕ Unit => Sum.elim Empty.elim
          (fun j : Fin 1 => CodingFormalProofs.boundName (0 + j.val)) (Sum.map id e x)) =
          Sum.elim Empty.elim (fun u => CodingFormalProofs.boundName (e u).val) := by
      funext x
      cases x with
      | inl x => cases x
      | inr u => simp only [Sum.map_inr, Sum.elim_inr, Nat.zero_add]
    rw [hname]
    change CodingFormalProofs.allCode
      (CodingFormalProofs.codeAt CodingFormalProofs.arithmeticSignature
        (Sum.elim Empty.elim (fun u => CodingFormalProofs.boundName (e u).val)) 1
        (A.relabel Sum.inr)) = _
    rw [Formula.relabel, CodingFormalProofs.codeAt_relabel]
    congr 2
    funext u
    simp only [Function.comp_apply, Sum.elim_inl, Sum.elim_inr]
    exact congrArg CodingFormalProofs.boundName (Fin.val_eq_zero (e u))
  change CodingFormalProofs.formulaCode CodingFormalProofs.arithmeticSignature Empty.elim
    ((A.relabel (Sum.inr : Unit → Empty ⊕ Unit)).iAlls Unit) = _
  dsimp only [Formula.iAlls]
  exact aux _ _

def formulaCodeAt {α : Type*} {r : ℕ} (name : α → Program r) (offset : ℕ) :
    {k : ℕ} → language.BoundedFormula α k → Program r
  | _, .falsum => bottom
  | _, .equal s t => equalCode
      (FixedSyntaxPrograms.termCode
        (Sum.elim name (fun i => syntaxNode 1 [constant (offset + i.val)])) s)
      (FixedSyntaxPrograms.termCode
        (Sum.elim name (fun i => syntaxNode 1 [constant (offset + i.val)])) t)
  | _, .rel e _ => e.elim
  | _, .imp a b => impCode (formulaCodeAt name offset a) (formulaCodeAt name offset b)
  | _, .all a => allCode (formulaCodeAt name offset a)

theorem formulaCodeAt_eval {α : Type*} {r k : ℕ} (name : α → Program r)
    (offset : ℕ) (A : language.BoundedFormula α k) (x : Fin r → ℕ) :
    (formulaCodeAt name offset A).eval x =
      CodingFormalProofs.codeAt CodingFormalProofs.arithmeticSignature
        (fun a => (name a).eval x) offset A := by
  have hn (k : ℕ) :
      (fun i : α ⊕ Fin k =>
        (Sum.elim name (fun i => syntaxNode 1 [constant (offset + i.val)]) i).eval x) =
      Sum.elim (fun a => (name a).eval x)
        (fun i : Fin k => CodingFormalProofs.boundName (offset + i.val)) := by
    funext i
    cases i with
    | inl i => rfl
    | inr i => simp only [Sum.elim_inr, syntaxNode_eval, List.map_cons, List.map_nil,
        constant_eval, CodingFormalProofs.boundName]
  induction A with
  | falsum => rfl
  | equal s t =>
      simp only [formulaCodeAt, equalCode, syntaxNode_eval, List.map_cons, List.map_nil,
        FixedSyntaxPrograms.termCode_eval, hn, CodingFormalProofs.codeAt,
        CodingFormalProofs.equalCode]
  | rel e _ => exact e.elim
  | imp a b iha ihb =>
      simp only [formulaCodeAt, impCode, binary, Program.eval, implication_eval,
        Matrix.cons_val_zero, Matrix.cons_val_one, iha, ihb, CodingFormalProofs.codeAt]
  | all a ih =>
      simp only [formulaCodeAt, allCode, syntaxNode_eval, List.map_cons, List.map_nil,
        ih, CodingFormalProofs.codeAt, CodingFormalProofs.allCode]

def segmentDisjunction : Program 2 :=
  .prec (equalCode (.proj 0) (unary ProofPrograms.numeral (constant 0)))
    (orCode (.proj 2)
      (equalCode (.proj 0) (unary ProofPrograms.numeral (unary .succ (.proj 1)))))

def upperFormula : language.Formula (Unit ⊕ Unit) :=
  leFormula (.var (.inl ())) (.var (.inr ()))

def upperCode : Program 1 := formulaCodeAt
  (Sum.elim (fun _ => syntaxNode 1 [constant 0]) (fun _ => unary ProofPrograms.numeral (.proj 0)))
  1 upperFormula

def initialSegmentCode : Program 1 :=
  allCode (impCode upperCode
    (binary segmentDisjunction (syntaxNode 1 [constant 0]) (.proj 0)))

def upperAt {r : ℕ} (offset : ℕ) (z n : Program r) : Program r :=
  formulaCodeAt (Sum.elim (fun _ => z) (fun _ => unary ProofPrograms.numeral n))
    offset upperFormula

def segmentBody {r : ℕ} (n : Program r) : Program r :=
  impCode (upperAt 1 (syntaxNode 1 [constant 0]) n)
    (binary segmentDisjunction (syntaxNode 1 [constant 0]) n)

/-- One natural-deduction step. Inputs are the index and the previous
certificate. Every newly used axiom belongs to the one fixed decomposition
proof; its numerical witness is retained verbatim. -/
def initialSegmentStep : Program 2 :=
  let n : Program 2 := .proj 0
  let p : Program 2 := .proj 1
  let q : Program 2 := fixedProof stepSentence step_sentence_derives
  let gamma := binary listAppend (context (root p)) (context (root q))
  let z : Program 2 := syntaxNode 8 [constant 0]
  let a := upperAt 0 z (unary .succ n)
  let b := upperAt 0 z n
  let d := binary segmentDisjunction z n
  let c := equalCode z (unary ProofPrograms.numeral (unary .succ n))
  let qbody := unary (argument 0) (conclusion (root q))
  let qfirst := binary instantiate qbody (unary ProofPrograms.numeral n)
  let q1 := syntaxNode 113 [gamma, qfirst, root q, qbody, unary ProofPrograms.numeral n]
  let qinner := unary (argument 0) qfirst
  let qsecond := binary instantiate qinner z
  let q2 := syntaxNode 113 [gamma, qsecond, q1, qinner, z]
  let pbody := unary (argument 0) (conclusion (root p))
  let pinst := binary instantiate pbody z
  let p1 := syntaxNode 113 [gamma, pinst, root p, pbody, z]
  let discharged := Program.comp finiteCasesRecord ![gamma, a, b, c, d, q2, p1]
  let body := segmentBody (unary .succ n)
  let result := syntaxNode 115 [gamma, allCode body, discharged, body, constant 0]
  certificateAt result (binary listAppend (witnesses p) (witnesses q))

def initialSegmentProof : Program 1 :=
  .prec (fixedProof (initialSegmentSentence 0) initial_segment_zero_derives)
    initialSegmentStep

section Internal
variable {M : Type u} [language.Structure M] [M ⊨ PA]

theorem segmentDisjunction_zero_value (z : M) :
    segmentDisjunction.value ![z, zeroValue M] =
      modelNode 4 [z, ProofPrograms.numeral.value ![zeroValue M] ] := by
  have h := Program.value_rec_zero
    (equalCode (Program.proj (0 : Fin 1)) (unary ProofPrograms.numeral (constant 0)))
    (orCode (Program.proj (2 : Fin 3))
      (equalCode (Program.proj 0) (unary ProofPrograms.numeral (unary .succ (Program.proj 1))))) ![z]
  have hv : Fin.snoc (![z] : Fin 1 → M) (zeroValue M) = ![z, zeroValue M] := by
    ext i
    fin_cases i <;> rfl
  simpa only [segmentDisjunction, hv, equalCode_value, Program.value_proj,
    Matrix.cons_val_zero, unary_value, constant_value, numeral_value_zero] using h

theorem segmentDisjunction_successor_value (z n : M) :
    segmentDisjunction.value ![z, succValue M n] =
      orValue (segmentDisjunction.value ![z, n])
        (modelNode 4 [z, ProofPrograms.numeral.value ![succValue M n] ]) := by
  have h := Program.value_rec_succ
    (equalCode (Program.proj (0 : Fin 1)) (unary ProofPrograms.numeral (constant 0)))
    (orCode (Program.proj (2 : Fin 3))
      (equalCode (Program.proj 0) (unary ProofPrograms.numeral (unary .succ (Program.proj 1))))) ![z] n
  have hv (k : M) : Fin.snoc (![z] : Fin 1 → M) k = ![z, k] := by
    ext i
    fin_cases i <;> rfl
  simp only [hv, orCode_value, equalCode_value, unary_value, Program.value_proj,
    Program.value_succ] at h
  simpa [segmentDisjunction, Fin.snoc, Matrix.head_cons, Matrix.tail_cons] using h

end Internal

local instance initialSegmentProofsLocalInstance1 : ℕ ⊨ PA := nat_models_PA

theorem modelList_nat (xs : List ℕ) : modelList xs = FiniteSequenceCoding.code xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
      rw [modelList_cons, ih, value_nat_eq_eval, listCons_eval,
        Matrix.cons_val_zero, Matrix.cons_val_one, FiniteSequenceCoding.code_cons]
      rfl

theorem modelNode_nat (k : ℕ) (xs : List ℕ) : modelNode k xs = CodingFormalProofs.node k xs := by
  rw [modelNode, numeral_value_nat, modelList_nat, value_nat_eq_eval, listCons_eval]
  rfl

theorem orValue_nat (a b : ℕ) : orValue a b = CodingFormalProofs.orCode a b := by
  simp only [orValue, negValue, value_nat_eq_eval, implication_eval,
    Matrix.cons_val_zero, Matrix.cons_val_one, modelNode_nat]
  rfl

theorem segmentDisjunction_eval_zero (z : ℕ) :
    segmentDisjunction.eval ![z, 0] =
      CodingFormalProofs.equalCode z (CodingFormalProofs.numeralCode 0 1 0) := by
  have h := segmentDisjunction_zero_value (M := ℕ) z
  change segmentDisjunction.value ![z, 0] = modelNode 4 [z, ProofPrograms.numeral.value ![0] ] at h
  simpa only [value_nat_eq_eval, numeral_eval, Matrix.cons_val_zero, modelNode_nat,
    CodingFormalProofs.equalCode] using h

theorem segmentDisjunction_eval_successor (z n : ℕ) :
    segmentDisjunction.eval ![z, n + 1] =
      CodingFormalProofs.orCode (segmentDisjunction.eval ![z, n])
        (CodingFormalProofs.equalCode z (CodingFormalProofs.numeralCode 0 1 (n + 1))) := by
  have h := segmentDisjunction_successor_value (M := ℕ) z n
  change segmentDisjunction.value ![z, n + 1] =
    orValue (segmentDisjunction.value ![z, n])
      (modelNode 4 [z, ProofPrograms.numeral.value ![n + 1] ]) at h
  simpa only [value_nat_eq_eval, numeral_eval, Matrix.cons_val_zero, modelNode_nat,
    CodingFormalProofs.equalCode, orValue_nat] using h

theorem numeralTerm_code {α : Type*} (name : α → ℕ) (n : ℕ) :
    CodingFormalProofs.termCode CodingFormalProofs.arithmeticSignature name (numeralTerm n) =
      CodingFormalProofs.numeralCode 0 1 n := by
  rw [numeralTerm, CodingFormalProofs.termCode_relabel]
  have hn : name ∘ (Empty.elim : Empty → α) = Empty.elim := by
    funext i
    cases i
  rw [hn]
  exact (CodingFormalProofs.arithmetic_numeral_code n).symm

theorem codeAt_equal_numeral (name : Unit → ℕ) (offset n : ℕ) :
    CodingFormalProofs.codeAt CodingFormalProofs.arithmeticSignature name offset
      ((Term.var ()).equal (numeralTerm n)) =
        CodingFormalProofs.equalCode (name ()) (CodingFormalProofs.numeralCode 0 1 n) := by
  simp only [Term.equal, Term.bdEqual, CodingFormalProofs.codeAt,
    CodingFormalProofs.termCode_relabel, Function.comp_def, Sum.elim_inl,
    numeralTerm_code, CodingFormalProofs.termCode]

theorem segmentDisjunction_eval (z n : ℕ) :
    segmentDisjunction.eval ![z, n] =
      CodingFormalProofs.codeAt CodingFormalProofs.arithmeticSignature (fun _ : Unit => z) 1
        (initialSegmentDisjunction n) := by
  induction n with
  | zero =>
      rw [segmentDisjunction_eval_zero]
      change CodingFormalProofs.equalCode z (CodingFormalProofs.numeralCode 0 1 0) =
        CodingFormalProofs.codeAt CodingFormalProofs.arithmeticSignature
          (fun _ : Unit => z) 1 ((Term.var ()).equal (numeralTerm 0))
      exact (codeAt_equal_numeral (fun _ : Unit => z) 1 0).symm
  | succ n ih =>
      rw [segmentDisjunction_eval_successor, ih]
      change CodingFormalProofs.orCode _ _ = CodingFormalProofs.orCode _ _
      rw [codeAt_equal_numeral]

theorem substituted_codeAt {α β : Type*} {k : ℕ}
    (A : language.BoundedFormula α k) (name : β → ℕ) (offset : ℕ)
    (s : α → language.Term β) :
    CodingFormalProofs.codeAt CodingFormalProofs.arithmeticSignature name offset (A.subst s) =
      CodingFormalProofs.codeAt CodingFormalProofs.arithmeticSignature
        (fun i => CodingFormalProofs.termCode CodingFormalProofs.arithmeticSignature name (s i))
        offset A := by
  have hn (k : ℕ) :
      (fun i : α ⊕ Fin k => CodingFormalProofs.termCode CodingFormalProofs.arithmeticSignature
        (Sum.elim name (fun j => CodingFormalProofs.boundName (offset + j.val)))
        ((Sum.elim (Term.relabel Sum.inl ∘ s) (Term.var ∘ Sum.inr)) i)) =
      Sum.elim (fun i => CodingFormalProofs.termCode CodingFormalProofs.arithmeticSignature name (s i))
        (fun j => CodingFormalProofs.boundName (offset + j.val)) := by
    funext i
    cases i with
    | inl i => simp only [Sum.elim_inl, Function.comp_apply,
        CodingFormalProofs.termCode_relabel, Sum.elim_comp_inl]
    | inr i => rfl
  induction A with
  | falsum => rfl
  | equal a b =>
    simp only [BoundedFormula.subst, BoundedFormula.mapTermRel, CodingFormalProofs.codeAt,
      FixedSyntaxPrograms.substituted_term_code, hn]
  | rel e _ => exact e.elim
  | imp a b ha hb =>
    change CodingFormalProofs.impCode
      (CodingFormalProofs.codeAt CodingFormalProofs.arithmeticSignature name offset (a.subst s))
      (CodingFormalProofs.codeAt CodingFormalProofs.arithmeticSignature name offset (b.subst s)) = _
    rw [ha, hb]
    rfl
  | all a ha =>
    change CodingFormalProofs.allCode
      (CodingFormalProofs.codeAt CodingFormalProofs.arithmeticSignature name offset (a.subst s)) = _
    rw [ha]
    rfl

theorem upperCode_eval (n : ℕ) : upperCode.eval ![n] =
    CodingFormalProofs.codeAt CodingFormalProofs.arithmeticSignature
      (fun _ : Unit => CodingFormalProofs.boundName 0) 1
      (leFormula (.var ()) (numeralTerm n)) := by
  rw [upperCode, formulaCodeAt_eval]
  let s : Unit ⊕ Unit → language.Term Unit :=
    Sum.elim (fun _ => .var ()) (fun _ => numeralTerm n)
  have hs : upperFormula.subst s = leFormula (.var ()) (numeralTerm n) := by
    simp only [upperFormula, ArithmeticRepresentability.subst_leFormula, Term.subst,
      s, Sum.elim_inl, Sum.elim_inr]
  rw [← hs, substituted_codeAt]
  congr 1
  funext i
  cases i with
  | inl i =>
    simp only [Sum.elim_inl, syntaxNode_eval, List.map_cons, constant_eval, List.map_nil,
      s, CodingFormalProofs.termCode, CodingFormalProofs.boundName]
  | inr i =>
    simp only [Sum.elim_inr, unary, Program.eval, Matrix.cons_val_zero,
      numeral_eval, s, numeralTerm_code]

theorem initialSegmentCode_eval (n : ℕ) : initialSegmentCode.eval ![n] =
    CodingFormalProofs.sentenceCode CodingFormalProofs.arithmeticSignature
      (initialSegmentSentence n) := by
  rw [initialSegmentSentence, unit_closure_code]
  simp only [initialSegmentCode, allCode, syntaxNode_eval, List.map_cons,
    List.map_nil, impCode, binary_eval, implication_eval, Matrix.cons_val_zero,
    Matrix.cons_val_one, constant_eval, Program.eval]
  change CodingFormalProofs.allCode (CodingFormalProofs.impCode (upperCode.eval ![n])
    (segmentDisjunction.eval ![CodingFormalProofs.boundName 0, n])) = _
  rw [upperCode_eval, segmentDisjunction_eval]
  rfl

end
end Lemmatheca.ProofTheory.PAComputations.ProofPrograms.InitialSegmentPrograms
