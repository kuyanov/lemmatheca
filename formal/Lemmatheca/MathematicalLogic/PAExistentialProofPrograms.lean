import Lemmatheca.MathematicalLogic.PAProofNaturalDeduction
import Lemmatheca.MathematicalLogic.PAProofOccurrence

/-! Append a fixed finite existential prefix to an actual accepted certificate.
The constructor traverses the target's literal quantified syntax and retains the
original axiom witnesses. -/
namespace Lemmatheca.MathematicalLogic.PAComputations.ProofPrograms.CheckerPrograms
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic ArithmeticTheories ArithmeticRepresentability
open SyntaxPrograms
noncomputable section
universe u

/-- Extract the body from the literal code `¬∀¬b` of an existential formula. -/
def existentialBody : Program 1 :=
  unary (argument 0) (unary (argument 0) (unary (argument 0) (.proj 0)))

/-- Inputs are the target existential sentence, the witness list, and the
certificate for its fully instantiated matrix. The prefix length is fixed. -/
def existentialPrefix : ℕ → Program 3
  | 0 => .proj 2
  | k + 1 =>
    let body := unary existentialBody (.proj 0)
    let witness := unary ProofPrograms.numeral (unary listHead (.proj 1))
    let inner := binary instantiate body witness
    ternary existentialIntroductionCertificate
      (ternary (existentialPrefix k) inner (unary listTail (.proj 1)) (.proj 2))
      body witness

variable {M : Type u} [language.Structure M] [M ⊨ PA]

theorem existentialBody_value (b : M) :
    existentialBody.value ![exValue b] = b := by
  have himp (a c : M) : implication.value ![a, c] = modelNode 6 [a, c] := by
    rw [implication_value]
    rfl
  simp only [existentialBody, unary_value, Program.value_proj, Matrix.cons_val_zero,
    exValue, negValue, himp, argument_modelNode_value, List.getElem?_cons_zero, Option.getD_some]

def ExistentialChain : ℕ → M → M → M → Prop
  | 0, target, _, matrix => target = matrix
  | k + 1, target, witnesses, matrix => ∃ body : M,
      target = exValue body ∧
      namedForm.value ![numeralValue M 1, body] = numeralValue M 1 ∧
      isSentence.value ![target] = numeralValue M 1 ∧
      ExistentialChain k
        (instantiate.value ![body, ProofPrograms.numeral.value ![listHead.value ![witnesses] ] ])
        (listTail.value ![witnesses]) matrix

theorem certified_existentialPrefix (E : Program 2) (k : ℕ) (target witnesses matrix p : M)
    (hchain : ExistentialChain k target witnesses matrix) (hp : Certified E p matrix) :
    Certified E ((existentialPrefix k).value ![target, witnesses, p]) target := by
  induction k generalizing target witnesses with
  | zero =>
    change target = matrix at hchain
    simpa only [existentialPrefix, Program.value_proj, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, hchain] using hp
  | succ k ih =>
    obtain ⟨body, htarget, hbody, hsentence, htail⟩ := hchain
    subst target
    have hinner := ih _ _ htail
    have hterm := numeral_namedTerm (listHead.value ![witnesses])
    have hout := certified_exIntro E
      ((existentialPrefix k).value ![
        instantiate.value ![body, ProofPrograms.numeral.value ![listHead.value ![witnesses] ] ],
        listTail.value ![witnesses], p]) body
      (ProofPrograms.numeral.value ![listHead.value ![witnesses] ]) hinner hbody hterm hsentence
    simpa only [existentialPrefix, ternary_value, binary_value, unary_value,
      Program.value_proj, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      existentialBody_value, Matrix.tail_cons, Matrix.head_cons] using hout

end
end Lemmatheca.MathematicalLogic.PAComputations.ProofPrograms.CheckerPrograms
