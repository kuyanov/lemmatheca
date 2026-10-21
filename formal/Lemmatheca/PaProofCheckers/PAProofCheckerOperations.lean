import Lemmatheca.PaListsAndSyntax.PASyntaxOperations
import Lemmatheca.PaProofCheckers.PAProofRulePrograms
import Lemmatheca.PaListsAndSyntax.PANativeSyntaxRecurrences

open Lemmatheca.MathematicalLogic Lemmatheca.ModelTheory Lemmatheca.ComputabilityTheory

namespace Lemmatheca.ProofTheory.PAComputations.ProofPrograms.CheckerPrograms
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic ArithmeticTheories ArithmeticRepresentability
open SyntaxPrograms
noncomputable section
universe u
section Internal
variable {M : Type u} [language.Structure M] [M ⊨ PA]
local instance proofCheckerOperationsLocalInstance1 (P : Prop) : Decidable P := Classical.propDecidable P

theorem certified_iff (E : Program 2) (p a : M) :
    Certified E p a ↔
      listLength.value ![p] = numeralValue M 2 ∧
      derivationCheck.value ![rootValue p] = numeralValue M 1 ∧
      conclusionValue (rootValue p) = a ∧
      isSentence.value ![a] = numeralValue M 1 ∧
      listLength.value ![contextValue (rootValue p)] = listLength.value ![witnessesValue p] ∧
      (axiomScan E).value ![contextValue (rootValue p), witnessesValue p,
        listLength.value ![contextValue (rootValue p)] ] = numeralValue M 1 := by
  simp only [Certified, certificateCheck, conjunction_cons_one_iff, conjunction_nil_value,
    binary_value, unary_value, ternary_value, Program.value_proj, constant_value,
    Matrix.cons_val_zero, Matrix.cons_val_one, equalTest_value,
    numeral_value_zero, rootValue, contextValue, witnessesValue, conclusionValue,
    and_true]
  have hzero : zeroValue M ≠ numeralValue M 1 := by
    rw [numeral_value_succ, numeral_value_zero]
    exact (successor_ne_zero _).symm
  simp only [ite_eq_left_iff, hzero, imp_false, not_not]

theorem modusPonensRecord_value (d e b : M) :
    modusPonensRecord.value ![d, e, b] =
      listCons.value ![numeralValue M 108,
        listCons.value ![listAppend.value ![(argument 0).value ![d], (argument 0).value ![e] ],
          listCons.value ![b, listCons.value ![d, listCons.value ![e, zeroValue M] ] ] ] ] := by
  simp only [modusPonensRecord, syntaxNode_value, list_cons_value, list_nil_value,
    binary, unary, Program.value_comp_two, Program.value_comp_one,
    Program.value_proj, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.head_cons]

end Internal
end
end Lemmatheca.ProofTheory.PAComputations.ProofPrograms.CheckerPrograms
