import Lemmatheca.MathematicalLogic.PANumeralMultiplicationProofs

namespace Lemmatheca.MathematicalLogic.PAComputations.ProofPrograms.CheckerPrograms.NumericalProofs
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic ArithmeticTheories ArithmeticRepresentability
open SyntaxPrograms FixedSyntaxPrograms
noncomputable section
variable {M : Type} [language.Structure M] [M ⊨ PA]

def binaryEquationCertificate (f : ℕ) (p q s t a b c normalized : M) : M :=
  let left := (parametricCongruence (binaryFrame f true)).value ![p, s, a, t]
  let right := (parametricCongruence (binaryFrame f false)).value ![q, t, b, a]
  let op (x y : M) := modelNode 2 [numeralValue M f, x, y]
  let both := transitivity.value ![left, right, op s t, op a t, op a b]
  transitivity.value ![both, normalized, op s t, op a b, c]

theorem certified_binaryEquationCertificate (E : Program 2) (f : ℕ) (hf : f = 2 ∨ f = 3)
    (p q s t a b c normalized : M)
    (hp : Certified E p (modelNode 4 [s, a]))
    (hq : Certified E q (modelNode 4 [t, b]))
    (hn : Certified E normalized (modelNode 4 [modelNode 2 [numeralValue M f, a, b], c]))
    (hs : PureTerm s) (ht : PureTerm t) (ha : PureTerm a) (hb : PureTerm b) (hc : PureTerm c) :
    Certified E (binaryEquationCertificate f p q s t a b c normalized)
      (modelNode 4 [modelNode 2 [numeralValue M f, s, t], c]) := by
  let op (x y : M) := modelNode 2 [numeralValue M f, x, y]
  have hl := certified_binaryCongruence E f hf true p s a t hp hs ha ht
  have hr := certified_binaryCongruence E f hf false q t b a hq ht hb ha
  simp only [binaryFrame_value, Bool.false_eq_true, ↓reduceIte] at hl hr
  have hbth := certified_transitivity E
    ((parametricCongruence (binaryFrame f true)).value ![p, s, a, t])
    ((parametricCongruence (binaryFrame f false)).value ![q, t, b, a])
    (op s t) (op a t) (op a b) hl hr (PureTerm.binary f hf hs ht)
    (PureTerm.binary f hf ha ht) (PureTerm.binary f hf ha hb)
  exact certified_transitivity E _ normalized (op s t) (op a b) c hbth hn
    (PureTerm.binary f hf hs ht) (PureTerm.binary f hf ha hb) hc

theorem termEquationCode_model_value {r : ℕ} (t : language.Term (Fin r)) (x : Fin r → M) :
    (termEquationCode t).value x =
      modelNode 4 [(termInstance t).value x, numeralSyntax ((termValue t).value x)] := by
  simp only [termEquationCode, syntaxNode_value, list_cons_value, list_nil_value,
    unary_value, numeralSyntax, modelNode, modelList_cons, modelList_nil]

theorem termInstance_func_value {r k : ℕ} (f : language.Functions k)
    (ts : Fin k → language.Term (Fin r)) (x : Fin r → M) :
    (termInstance (.func f ts)).value x = modelNode 2
      (numeralValue M (CodingFormalProofs.arithFunctionCode f) ::
        List.ofFn (fun i => (termInstance (ts i)).value x)) :=
  termCode_value numeralName (.func f ts) x

theorem termInstance_model_value {r : ℕ} (t : language.Term (Fin r)) (x : Fin r → M) :
    (termInstance t).value x = modelTermCode (fun i => numeralSyntax (x i)) t := by
  rw [termInstance, termCode_model_value]
  apply congrArg (fun name => modelTermCode name t)
  funext i
  simp only [numeralName, unary_value, Program.value_proj, numeralSyntax]

theorem certified_termBuilder {r : ℕ} (t : language.Term (Fin r)) (x : Fin r → M) :
    Certified axiomVerifier ((termBuilder t).value x) ((termEquationCode t).value x) := by
  rw [termEquationCode_model_value]
  induction t with
  | var i =>
    have hn : PureTerm (numeralSyntax (x i)) := PureTerm.numeral _
    have h := certified_equalityReflexivity axiomVerifier (numeralSyntax (x i)) hn.namedTerm
      (hn.equal_sentence hn)
    simpa only [termBuilder, termInstance, termCode, numeralName, termValue,
      unary_value, num_model_value, Program.value_proj, numeralSyntax] using h
  | func f ts ih =>
    have hi (i) : Certified axiomVerifier ((termBuilder (ts i)).value x)
        (modelNode 4 [(termInstance (ts i)).value x,
          numeralSyntax ((termValue (ts i)).value x)]) := ih i
    have hp (i) := termInstance_pure (ts i) x
    have hn (i) : PureTerm (numeralSyntax ((termValue (ts i)).value x)) := PureTerm.numeral _
    rw [termInstance_func_value]
    cases f with
    | zero =>
      have h := certified_equalityReflexivity axiomVerifier (zeroSyntax (M := M))
        zeroSyntax_pure.namedTerm (zeroSyntax_pure.equal_sentence zeroSyntax_pure)
      simpa only [termBuilder, unary_value, zeroCode_model_value,
        CodingFormalProofs.arithFunctionCode, List.ofFn_zero, termValue, constant_value,
        numeral_value_zero, numeralSyntax_zero, zeroSyntax] using h
    | succ =>
      have h := certified_succCongruence axiomVerifier ((termBuilder (ts 0)).value x)
        ((termInstance (ts 0)).value x) (numeralSyntax ((termValue (ts 0)).value x))
        (hi 0) (hp 0) (hn 0)
      simpa only [termBuilder, Program.value_comp_three, num_model_value,
        CodingFormalProofs.arithFunctionCode, List.ofFn_succ,
        List.ofFn_zero, termValue, unary_value, Program.value_succ, Matrix.cons_val_zero,
        numeralSyntax_succ, successorSyntax] using h
    | add =>
      have hleft : binaryFrame 2 true = addLeftFrame := rfl
      have hright : binaryFrame 2 false = addRightFrame := rfl
      have h := certified_binaryEquationCertificate axiomVerifier 2 (Or.inl rfl)
        ((termBuilder (ts 0)).value x) ((termBuilder (ts 1)).value x)
        ((termInstance (ts 0)).value x) ((termInstance (ts 1)).value x)
        (numeralSyntax ((termValue (ts 0)).value x)) (numeralSyntax ((termValue (ts 1)).value x))
        (numeralSyntax (addValue M ((termValue (ts 0)).value x) ((termValue (ts 1)).value x)))
        (additionBuilder.value ![(termValue (ts 0)).value x, (termValue (ts 1)).value x])
        (hi 0) (hi 1) (certified_additionBuilder _ _) (hp 0) (hp 1) (hn 0) (hn 1) (PureTerm.numeral _)
      simpa only [termBuilder, composeEquality_model_value, compFour_model_value,
        binaryEquationCertificate, num_model_value, addCode_model_value, binary_value,
        addition_value, CodingFormalProofs.arithFunctionCode,
        List.ofFn_succ, List.ofFn_zero, Fin.succ_zero_eq_one, termValue,
        hleft, hright,
        additionSyntax] using h
    | mul =>
      have hleft : binaryFrame 3 true = mulLeftFrame := rfl
      have hright : binaryFrame 3 false = mulRightFrame := rfl
      have h := certified_binaryEquationCertificate axiomVerifier 3 (Or.inr rfl)
        ((termBuilder (ts 0)).value x) ((termBuilder (ts 1)).value x)
        ((termInstance (ts 0)).value x) ((termInstance (ts 1)).value x)
        (numeralSyntax ((termValue (ts 0)).value x)) (numeralSyntax ((termValue (ts 1)).value x))
        (numeralSyntax (mulValue M ((termValue (ts 0)).value x) ((termValue (ts 1)).value x)))
        (multiplicationBuilder.value ![(termValue (ts 0)).value x, (termValue (ts 1)).value x])
        (hi 0) (hi 1) (certified_multiplicationBuilder _ _) (hp 0) (hp 1) (hn 0) (hn 1) (PureTerm.numeral _)
      simpa only [termBuilder, composeEquality_model_value, compFour_model_value,
        binaryEquationCertificate, num_model_value, mulCode_model_value, binary_value,
        multiplication_value, CodingFormalProofs.arithFunctionCode,
        List.ofFn_succ, List.ofFn_zero, Fin.succ_zero_eq_one, termValue,
        hleft, hright,
        multiplicationSyntax] using h

end
end Lemmatheca.MathematicalLogic.PAComputations.ProofPrograms.CheckerPrograms.NumericalProofs
