import Lemmatheca.PaComputations.PAProgramValues
import Lemmatheca.PaListsAndSyntax.PAListPrograms
import Lemmatheca.PaListsAndSyntax.PANativeSubstitutionEvaluation
import Lemmatheca.PaListsAndSyntax.PANativeSyntaxCorrectness
import Lemmatheca.PaListsAndSyntax.PANumeralSyntax

open Lemmatheca.MathematicalLogic Lemmatheca.ModelTheory Lemmatheca.ComputabilityTheory

/-! Internal versions of the corpus's actual list and syntax algorithms.
The packages include internal correctness, not just equality of their standard
numerical interpretations to independently chosen primitive-recursive programs.
-/
namespace Lemmatheca.ProofTheory.PAComputations
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic ArithmeticTheories ArithmeticRepresentability
open FirstOrderProofs
noncomputable section
universe u

structure InternalListOperations where
  head : Program 1
  tail : Program 1
  length : Program 1
  cons : Program 2
  append : Program 2
  entry : Program 2
  head_eval : ∀ x, head.eval x = FiniteSequenceCoding.head (x 0)
  tail_eval : ∀ x, tail.eval x = FiniteSequenceCoding.tail (x 0)
  length_eval : ∀ x, length.eval x = FiniteSequenceCoding.length (x 0)
  cons_eval : ∀ x, cons.eval x = FiniteSequenceCoding.cons (x 0) (x 1)
  append_eval : ∀ x, append.eval x = FiniteSequenceCoding.append (x 0) (x 1)
  entry_eval : ∀ x, entry.eval x = FiniteSequenceCoding.entry (x 0) (x 1)
  head_cons : ∀ (M : Type) [language.Structure M] [M ⊨ PA] (a c : M),
    head.value ![(cons.value ![a, c])] = a
  tail_cons : ∀ (M : Type) [language.Structure M] [M ⊨ PA] (a c : M),
    tail.value ![(cons.value ![a, c])] = c
  tail_smaller : ∀ (M : Type) [language.Structure M] [M ⊨ PA] (c : M),
    c ≠ zeroValue M → leValue M (succValue M (tail.value ![c])) c
  append_zero : ∀ (M : Type) [language.Structure M] [M ⊨ PA] (c : M),
    append.value ![zeroValue M, c] = c
  append_cons : ∀ (M : Type) [language.Structure M] [M ⊨ PA] (a c d : M),
    append.value ![(cons.value ![a, c]), d] = cons.value ![a, (append.value ![c, d])]

/-- The chosen presentations of the existing list functions satisfy their
constructor laws at all internal codes in every PA model. -/
theorem exists_internal_list_operations : Nonempty InternalListOperations := by
  exact ⟨{
    head := ProofPrograms.listHead
    tail := ProofPrograms.listTail
    length := ProofPrograms.listLength
    cons := ProofPrograms.listCons
    append := ProofPrograms.listAppend
    entry := ProofPrograms.listEntry
    head_eval := ProofPrograms.head_eval
    tail_eval := ProofPrograms.tail_eval
    length_eval := ProofPrograms.listLength_eval
    cons_eval := ProofPrograms.listCons_eval
    append_eval := ProofPrograms.listAppend_eval
    entry_eval := ProofPrograms.listEntry_eval
    head_cons := fun _ _ _ => ProofPrograms.head_cons_value
    tail_cons := fun _ _ _ => ProofPrograms.tail_cons_value
    tail_smaller := fun _ _ _ => ProofPrograms.tail_smaller_value
    append_zero := fun _ _ _ => ProofPrograms.listAppend_zero_value
    append_cons := fun _ _ _ => ProofPrograms.listAppend_cons_value }⟩

def booleanValue (b : Bool) : ℕ := if b then 1 else 0

structure InternalSyntaxOperations where
  isTerm : Program 2
  isForm : Program 2
  substitute : Program 4
  numeral : Program 1
  isTerm_eval : ∀ x, isTerm.eval x =
    booleanValue (CodingFormalProofs.isTerm CodingFormalProofs.arithmeticSignature (x 0) (x 1))
  isForm_eval : ∀ x, isForm.eval x =
    booleanValue (CodingFormalProofs.isForm CodingFormalProofs.arithmeticSignature (x 0) (x 1))
  substitute_eval : ∀ x, substitute.eval x =
    CodingFormalProofs.substitute CodingFormalProofs.arithmeticSignature (x 0) (x 1) (x 2) (x 3)
  numeral_eval : ∀ x, numeral.eval x = CodingFormalProofs.numeralCode 0 1 (x 0)
  numeral_wellformed : ∀ (M : Type) [language.Structure M] [M ⊨ PA] (n : M),
    isTerm.value ![zeroValue M, (numeral.value ![n])] = numeralValue M 1
  substitution_preserves : ∀ (M : Type) [language.Structure M] [M ⊨ PA] (n a i t : M),
    isForm.value ![n, a] = numeralValue M 1 →
    isTerm.value ![zeroValue M, t] = numeralValue M 1 →
    isForm.value ![n, (substitute.value ![n, a, i, t])] = numeralValue M 1

/-- The actual shared-syntax numerical routines have presentations whose
internal equations prove numeral formation and substitution preservation. -/
theorem exists_internal_syntax_operations : Nonempty InternalSyntaxOperations := by
  exact ⟨{
    isTerm := ProofPrograms.SyntaxPrograms.isTerm
    isForm := ProofPrograms.SyntaxPrograms.isForm
    substitute := ProofPrograms.SyntaxPrograms.substitute
    numeral := ProofPrograms.numeral
    isTerm_eval := ProofPrograms.SyntaxPrograms.isTerm_eval
    isForm_eval := ProofPrograms.SyntaxPrograms.isForm_eval
    substitute_eval := ProofPrograms.SyntaxPrograms.substitute_eval
    numeral_eval := ProofPrograms.numeral_eval
    numeral_wellformed := fun _ _ _ => ProofPrograms.SyntaxPrograms.numeral_wellformed
    substitution_preserves := fun _ _ _ => ProofPrograms.SyntaxPrograms.substitute_preserves }⟩

end
end Lemmatheca.ProofTheory.PAComputations
