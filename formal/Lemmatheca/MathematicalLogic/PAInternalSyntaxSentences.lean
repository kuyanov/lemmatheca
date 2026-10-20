import Lemmatheca.MathematicalLogic.PAComputationsSentences
import Lemmatheca.MathematicalLogic.PAProofCheckerEvaluation
import Lemmatheca.MathematicalLogic.PANativeNoAux

namespace Lemmatheca.MathematicalLogic.PAComputations
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic ArithmeticTheories ArithmeticRepresentability FirstOrderProofs
open ProofPrograms ProofPrograms.SyntaxPrograms
noncomputable section

/-- The actual witnesses are transparent program expressions, not existentially
chosen presentations agreeing merely on standard natural inputs. -/
def internalListOperations : InternalListOperations where
  head := listHead
  tail := listTail
  length := listLength
  cons := listCons
  append := listAppend
  entry := listEntry
  head_eval := head_eval
  tail_eval := tail_eval
  length_eval := listLength_eval
  cons_eval := listCons_eval
  append_eval := listAppend_eval
  entry_eval := listEntry_eval
  head_cons := fun _ _ _ => head_cons_value
  tail_cons := fun _ _ _ => tail_cons_value
  tail_smaller := fun _ _ _ => tail_smaller_value
  append_zero := fun _ _ _ => listAppend_zero_value
  append_cons := fun _ _ _ => listAppend_cons_value

def internalSyntaxOperations : InternalSyntaxOperations where
  isTerm := isTerm
  isForm := isForm
  substitute := substitute
  numeral := numeral
  isTerm_eval := isTerm_eval
  isForm_eval := isForm_eval
  substitute_eval := substitute_eval
  numeral_eval := numeral_eval
  numeral_wellformed := fun _ _ _ => numeral_wellformed
  substitution_preserves := fun _ _ _ => substitute_preserves

structure InternalSyntaxRoutines extends InternalSyntaxOperations where
  occursAux : Program 2
  isSentence : Program 1
  occursAux_eval : ∀ x, occursAux.eval x = booleanValue (CodingFormalProofs.occursAux (x 0) (x 1))
  isSentence_eval : ∀ x, isSentence.eval x = booleanValue
    (CodingFormalProofs.isSentence CodingFormalProofs.arithmeticSignature (x 0))
  numeral_fresh : ∀ (M : Type) [language.Structure M] [M ⊨ PA] (j n : M),
    occursAux.value ![j, numeral.value ![n] ] = zeroValue M
  sentence_fresh : ∀ (M : Type) [language.Structure M] [M ⊨ PA] (j a : M),
    isSentence.value ![a] = numeralValue M 1 → occursAux.value ![j, a] = zeroValue M

def internalSyntaxRoutines : InternalSyntaxRoutines where
  toInternalSyntaxOperations := internalSyntaxOperations
  occursAux := CheckerPrograms.occursAux
  isSentence := CheckerPrograms.isSentence
  occursAux_eval := CheckerPrograms.occursAux_eval
  isSentence_eval := CheckerPrograms.isSentence_eval
  numeral_fresh := fun _ _ _ => CheckerPrograms.numeral_occursAux_zero
  sentence_fresh := fun _ _ _ => CheckerPrograms.isSentence_occursAux_zero

/-- Literal closed arithmetic meaning of a Boolean program returning one. -/
def Program.oneFormula {n : ℕ} (p : Program n) : language.Formula (Fin n) :=
  graphAt p.graph (fun i => .var i) (numeralTerm 1)

theorem Program.realize_oneFormula {n : ℕ} (p : Program n)
    (M : Theory.ModelType.{0,0,0} PA) (v : Fin n → M) :
    p.oneFormula.Realize v ↔ p.value v = numeralValue M 1 := by
  simp only [oneFormula, realize_graphAt, Term.realize_var, realize_numeralTerm]
  exact (p.value_iff v _).trans eq_comm

def numeralWellformedSentence : language.Sentence :=
  allClose (Program.comp isTerm ![constant 0, numeral]).oneFormula

theorem numeral_wellformed_derives : Derives PA numeralWellformedSentence := by
  apply derives_allClose_of_models
  intro M v
  rw [Program.realize_oneFormula]
  have hv : v = ![v 0] := by funext i; fin_cases i; rfl
  rw [hv]
  simpa only [Program.value_comp_two, constant_value, numeral_value_zero] using
    (numeral_wellformed (M := M) (v 0))

def substitutionPreservationSentence : language.Sentence :=
  let form : Program 4 := .comp isForm ![.proj 0, .proj 1]
  let term : Program 4 := .comp isTerm ![constant 0, .proj 3]
  let result : Program 4 := .comp isForm ![.proj 0, substitute]
  allClose (form.oneFormula.imp (term.oneFormula.imp result.oneFormula))

theorem substitution_preservation_derives : Derives PA substitutionPreservationSentence := by
  apply derives_allClose_of_models
  intro M v
  simp only [Formula.realize_imp, Program.realize_oneFormula,
    Program.value_comp_two, Program.value_proj, constant_value, numeral_value_zero]
  have hv : ![v 0, v 1, v 2, v 3] = v := by funext i; fin_cases i <;> rfl
  have h := substitute_preserves (M := M) (v 0) (v 1) (v 2) (v 3)
  rw [hv] at h
  exact h

theorem head_cons_derives : PAEquivalent
    (Program.comp listHead ![listCons]).graph (Program.proj (0 : Fin 2)).graph := by
  apply Program.equivalent_of_values
  intro M x
  have hx : x = ![x 0, x 1] := by funext i; fin_cases i <;> rfl
  simp only [Program.value_comp_one, Program.value_proj]
  rw [hx]
  exact head_cons_value (x 0) (x 1)

theorem tail_cons_derives : PAEquivalent
    (Program.comp listTail ![listCons]).graph (Program.proj (1 : Fin 2)).graph := by
  apply Program.equivalent_of_values
  intro M x
  have hx : x = ![x 0, x 1] := by funext i; fin_cases i <;> rfl
  simp only [Program.value_comp_one, Program.value_proj]
  rw [hx]
  exact tail_cons_value (x 0) (x 1)

theorem append_zero_derives : PAEquivalent
    (Program.comp listAppend ![constant 0, .proj 0]).graph (Program.proj (0 : Fin 1)).graph := by
  apply Program.equivalent_of_values
  intro M x
  simpa only [Program.value_comp_two, Program.value_proj, constant_value,
    numeral_value_zero] using listAppend_zero_value (x 0)

theorem append_cons_derives : PAEquivalent
    (Program.comp listAppend ![.comp listCons ![.proj 0, .proj 1], .proj (2 : Fin 3)]).graph
    (Program.comp listCons ![.proj 0, .comp listAppend ![.proj (1 : Fin 3), .proj 2] ]).graph := by
  apply Program.equivalent_of_values
  intro M x
  simpa only [Program.value_comp_two, Program.value_proj] using
    listAppend_cons_value (x 0) (x 1) (x 2)

end
end Lemmatheca.MathematicalLogic.PAComputations
