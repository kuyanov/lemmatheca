import Lemmatheca.PaListsAndSyntax.PANativeSyntax
import Lemmatheca.ArithmeticRepresentability.ArithmeticRepresentabilityConverse
import Lemmatheca.PaListsAndSyntax.PANativeSyntaxValues

open Lemmatheca.MathematicalLogic Lemmatheca.ModelTheory Lemmatheca.ComputabilityTheory

/-! Structural compilers for a fixed arithmetic term or formula. Their inputs
are the values to be replaced by numeral codes, not a second formula syntax. -/
namespace Lemmatheca.ProofTheory.PAComputations.ProofPrograms.FixedSyntaxPrograms
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic ArithmeticTheories ArithmeticRepresentability
open SyntaxPrograms
noncomputable section
universe u

def termValue {r : ℕ} : language.Term (Fin r) → Program r
  | .var i => .proj i
  | .func .zero _ => constant 0
  | .func .succ ts => unary .succ (termValue (ts 0))
  | .func .add ts => binary addition (termValue (ts 0)) (termValue (ts 1))
  | .func .mul ts => binary multiplication (termValue (ts 0)) (termValue (ts 1))

def termCode {α : Type*} {r : ℕ} (name : α → Program r) : language.Term α → Program r
  | .var i => name i
  | .func f ts => syntaxNode 2
      (constant (CodingFormalProofs.arithFunctionCode f) ::
        List.ofFn (fun i => termCode name (ts i)))

def formulaCode {α : Type*} {r : ℕ} (name : α → Program r) :
    {k : ℕ} → language.BoundedFormula α k → Program r
  | _, .falsum => syntaxNode 3 []
  | _, .equal s t => syntaxNode 4 [
      termCode (Sum.elim name (fun i => syntaxNode 1 [constant i.val])) s,
      termCode (Sum.elim name (fun i => syntaxNode 1 [constant i.val])) t]
  | _, .rel e _ => e.elim
  | _, .imp a b => syntaxNode 6 [formulaCode name a, formulaCode name b]
  | _, .all a => syntaxNode 7 [formulaCode name a]

def numeralName {r : ℕ} (i : Fin r) : Program r := unary ProofPrograms.numeral (.proj i)

def substitution {r : ℕ} (A : language.Formula (Fin r)) : Program r :=
  formulaCode numeralName A

def termInstance {r : ℕ} (t : language.Term (Fin r)) : Program r :=
  termCode numeralName t

def termEquationCode {r : ℕ} (t : language.Term (Fin r)) : Program r :=
  syntaxNode 4 [termInstance t, unary ProofPrograms.numeral (termValue t)]

theorem termValue_eval {r : ℕ} (t : language.Term (Fin r)) (x : Fin r → ℕ) :
    (termValue t).eval x = t.realize x := by
  induction t with
  | var i => rfl
  | func f ts ih =>
    cases f <;>
      simp only [termValue, Program.eval, Term.realize,
        constant_eval, addition_eval, multiplication_eval, ih,
        Matrix.cons_val_zero, Matrix.cons_val_one, unary, binary] <;> rfl

theorem termCode_eval {α : Type*} {r : ℕ} (name : α → Program r)
    (t : language.Term α) (x : Fin r → ℕ) :
    (termCode name t).eval x = CodingFormalProofs.termCode CodingFormalProofs.arithmeticSignature
      (fun i => (name i).eval x) t := by
  induction t with
  | var i => rfl
  | func f ts ih =>
    simp only [termCode, syntaxNode_eval, List.map_cons, constant_eval, List.map_ofFn,
      CodingFormalProofs.termCode]
    congr 1
    apply congrArg₂ List.cons rfl
    apply congrArg List.ofFn
    funext i
    exact ih i

theorem formulaCode_eval {α : Type*} {r k : ℕ} (name : α → Program r)
    (A : language.BoundedFormula α k) (x : Fin r → ℕ) :
    (formulaCode name A).eval x =
      CodingFormalProofs.formulaCode CodingFormalProofs.arithmeticSignature
        (fun i => (name i).eval x) A := by
  have hn (k : ℕ) :
      (fun i : α ⊕ Fin k =>
        (Sum.elim name (fun i => syntaxNode 1 [constant i.val]) i).eval x) =
      Sum.elim (fun i => (name i).eval x) (fun i => CodingFormalProofs.boundName i.val) := by
    funext i
    cases i with
    | inl i => rfl
    | inr i => simp only [Sum.elim_inr, syntaxNode_eval, List.map_cons, constant_eval,
        List.map_nil, CodingFormalProofs.boundName]
  induction A with
  | falsum => rfl
  | equal s t =>
    simp only [formulaCode, syntaxNode_eval, List.map_cons, List.map_nil,
      termCode_eval, hn, CodingFormalProofs.formulaCode, CodingFormalProofs.equalCode]
  | rel e _ => exact e.elim
  | imp a b ha hb =>
    simp only [formulaCode, syntaxNode_eval, List.map_cons, List.map_nil,
      ha, hb, CodingFormalProofs.formulaCode, CodingFormalProofs.impCode]
  | all a ha =>
    simp only [formulaCode, syntaxNode_eval, List.map_cons, List.map_nil,
      ha, CodingFormalProofs.formulaCode, CodingFormalProofs.allCode]

theorem substituted_term_code {α β : Type*} (t : language.Term α)
    (name : β → ℕ) (s : α → language.Term β) :
    CodingFormalProofs.termCode CodingFormalProofs.arithmeticSignature name (t.subst s) =
      CodingFormalProofs.termCode CodingFormalProofs.arithmeticSignature
        (fun i => CodingFormalProofs.termCode CodingFormalProofs.arithmeticSignature name (s i)) t := by
  induction t with
  | var i => rfl
  | func f ts ih =>
    simp only [Term.subst, CodingFormalProofs.termCode]
    congr 2
    apply congrArg List.ofFn
    funext i
    exact ih i

theorem substituted_formula_code {α β : Type*} {k : ℕ}
    (A : language.BoundedFormula α k) (name : β → ℕ) (s : α → language.Term β) :
    CodingFormalProofs.formulaCode CodingFormalProofs.arithmeticSignature name (A.subst s) =
      CodingFormalProofs.formulaCode CodingFormalProofs.arithmeticSignature
        (fun i => CodingFormalProofs.termCode CodingFormalProofs.arithmeticSignature name (s i)) A := by
  have hn (k : ℕ) :
      (fun i : α ⊕ Fin k => CodingFormalProofs.termCode CodingFormalProofs.arithmeticSignature
        (Sum.elim name (fun j => CodingFormalProofs.boundName j.val))
        ((Sum.elim (Term.relabel Sum.inl ∘ s) (Term.var ∘ Sum.inr)) i)) =
      Sum.elim (fun i => CodingFormalProofs.termCode CodingFormalProofs.arithmeticSignature name (s i))
        (fun i => CodingFormalProofs.boundName i.val) := by
    funext i
    cases i with
    | inl i => simp only [Sum.elim_inl, Function.comp_apply,
        CodingFormalProofs.termCode_relabel, Sum.elim_comp_inl]
    | inr i => rfl
  induction A with
  | falsum => rfl
  | equal a b =>
    simp only [BoundedFormula.subst, BoundedFormula.mapTermRel, CodingFormalProofs.formulaCode,
      substituted_term_code, hn]
  | rel e _ => exact e.elim
  | imp a b ha hb =>
    change CodingFormalProofs.impCode
      (CodingFormalProofs.formulaCode CodingFormalProofs.arithmeticSignature name (a.subst s))
      (CodingFormalProofs.formulaCode CodingFormalProofs.arithmeticSignature name (b.subst s)) = _
    rw [ha, hb]
    rfl
  | all a ha =>
    change CodingFormalProofs.allCode
      (CodingFormalProofs.formulaCode CodingFormalProofs.arithmeticSignature name (a.subst s)) = _
    rw [ha]
    rfl

theorem substitution_eval {r : ℕ} (A : language.Formula (Fin r)) (x : Fin r → ℕ) :
    (substitution A).eval x = CodingFormalProofs.sentenceCode CodingFormalProofs.arithmeticSignature
      (numeralInstance A x) := by
  rw [substitution, formulaCode_eval]
  simp only [CodingFormalProofs.sentenceCode, numeralInstance, substituted_formula_code]
  congr 1
  funext i
  simp only [numeralName, unary, Program.eval, numeral_eval]
  exact CodingFormalProofs.arithmetic_numeral_code (x i)

theorem termInstance_eval {r : ℕ} (t : language.Term (Fin r)) (x : Fin r → ℕ) :
    (termInstance t).eval x = CodingFormalProofs.termCode CodingFormalProofs.arithmeticSignature
      Empty.elim (t.subst (fun i => ArithmeticTheories.numeral (x i))) := by
  rw [termInstance, termCode_eval, substituted_term_code]
  congr 1
  funext i
  simp only [numeralName, unary, Program.eval, numeral_eval]
  exact CodingFormalProofs.arithmetic_numeral_code (x i)

theorem termEquationCode_eval {r : ℕ} (t : language.Term (Fin r)) (x : Fin r → ℕ) :
    (termEquationCode t).eval x = CodingFormalProofs.sentenceCode CodingFormalProofs.arithmeticSignature
      ((t.subst (fun i => ArithmeticTheories.numeral (x i))).equal
        (ArithmeticTheories.numeral (t.realize x))) := by
  simp only [termEquationCode, syntaxNode_eval, List.map_cons, List.map_nil,
    termInstance_eval, unary, Program.eval, numeral_eval, termValue_eval,
    Matrix.cons_val_zero, CodingFormalProofs.sentenceCode, Term.equal, Term.bdEqual,
    CodingFormalProofs.formulaCode, CodingFormalProofs.termCode_relabel, Sum.elim_comp_inl,
    CodingFormalProofs.equalCode, ← CodingFormalProofs.arithmetic_numeral_code]

section Internal
variable {M : Type u} [language.Structure M] [M ⊨ PA]

theorem termValue_value {r : ℕ} (t : language.Term (Fin r)) (x : Fin r → M) :
    (termValue t).value x = t.realize x := by
  induction t with
  | var i => exact Program.value_proj i x
  | func f ts ih =>
    cases f <;>
      simp only [termValue, unary_value, binary_value, Program.value_succ,
        constant_value, numeral_value_zero, addition_value, multiplication_value, ih,
        Term.realize, zeroValue, succValue, addValue, mulValue]
    all_goals
      congr 1
      funext i
      fin_cases i <;> rfl

end Internal

end
end Lemmatheca.ProofTheory.PAComputations.ProofPrograms.FixedSyntaxPrograms
