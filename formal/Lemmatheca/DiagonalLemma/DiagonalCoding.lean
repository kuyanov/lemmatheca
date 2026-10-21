import Lemmatheca.CodingFormalProofs.CodingFormalProofsOperations
import Lemmatheca.CodingFormalProofs.CodingFormalProofsComputability
import Lemmatheca.ArithmeticRepresentability.ArithmeticRepresentabilityBasic

open Lemmatheca.MathematicalLogic Lemmatheca.ModelTheory Lemmatheca.ComputabilityTheory

/-! Diagonal substitution on the existing arithmetic syntax and its existing
numerical codes. There is no second formula syntax or decoding assumption. -/
namespace Lemmatheca.ProofTheory.DiagonalLemma

open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic ArithmeticTheories ArithmeticRepresentability
open CodingFormalProofs
attribute [local irreducible] rewrite stats

/-- A unary formula uses the original free name numbered zero. -/
def unaryFormulaCode (A : language.Formula Unit) : ℕ :=
  formulaCode arithmeticSignature (fun _ => freeName 0) A

/-- Close the unique free name by the specified arithmetic numeral. -/
def numeralSubstitution (A : language.Formula Unit) (n : ℕ) : language.Sentence :=
  numeralInstance A (fun _ => n)

/-- Substitute the input's own numeral for free name zero. The previously defined
syntactic checker makes this a total numerical function, including invalid codes. -/
def diagonalCode (n : ℕ) : ℕ :=
  substitute arithmeticSignature 0 n 0 (numeralCode 0 1 n)

/-- The total numerical diagonal operation is primitive recursive. -/
theorem diagonalCode_primrec : Primrec diagonalCode := by
  exact (primrec_substitute arithmeticSignature).comp
    ((Primrec.const 0).pair
      (Primrec.id.pair ((Primrec.const 0).pair (numeral_primrec 0 1))))

/-- The numerical operation agrees with substitution in the actual shared syntax. -/
theorem diagonalCode_unaryFormulaCode (A : language.Formula Unit) :
    diagonalCode (unaryFormulaCode A) =
      sentenceCode arithmeticSignature (numeralSubstitution A (unaryFormulaCode A)) := by
  let n := unaryFormulaCode A
  have ha : isForm arithmeticSignature 0 n = true := by
    simpa only [n, Formula.relabel, formulaCode_relabel, Function.comp_def,
      unaryFormulaCode] using
      formula_code_recognition arithmeticSignature (A.relabel (fun _ : Unit => 0))
  have ht : isTerm arithmeticSignature 0 (numeralCode 0 1 n) = true := by
    rw [arithmetic_numeral_code]
    have h := term_code_recognition arithmeticSignature (n := 0)
      ((numeral n).relabel (Empty.elim : Empty → ℕ ⊕ Fin 0))
    have he : (Sum.elim freeName (fun i : Fin 0 => boundName i.val)) ∘
        (Empty.elim : Empty → ℕ ⊕ Fin 0) = (Empty.elim : Empty → ℕ) := by
      funext i
      exact i.elim
    simpa only [termCode_relabel, he] using h
  unfold diagonalCode substitute
  rw [ha, ht]
  simp only [Bool.true_and, ↓reduceIte]
  apply rewrite_subst_formula arithmeticSignature
    (fun _ : Unit => freeName 0) Empty.elim 0 0 (numeralCode 0 1 n)
    (fun _ => numeral n) (by decide)
  intro i
  simp only [rewrite_free, and_self, ↓reduceIte, arithmetic_numeral_code]

end Lemmatheca.ProofTheory.DiagonalLemma
