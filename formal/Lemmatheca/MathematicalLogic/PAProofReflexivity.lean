import Lemmatheca.MathematicalLogic.PAProofEqualitySubstitution
import Lemmatheca.MathematicalLogic.PAProofLocalRules

namespace Lemmatheca.MathematicalLogic.PAComputations.ProofPrograms.CheckerPrograms
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic ArithmeticTheories ArithmeticRepresentability
open SyntaxPrograms
noncomputable section
universe u
variable {M : Type u} [language.Structure M] [M ⊨ PA]

theorem checked_equalityReflexivity (t : M)
    (ht : namedTerm.value ![t] = numeralValue M 1)
    (hout : namedForm.value ![zeroValue M, modelNode 4 [t, t] ] = numeralValue M 1) :
    Checked (modelNode 117 [zeroValue M, modelNode 4 [t, t], t])
      (zeroValue M) (modelNode 4 [t, t]) := by
  apply checked_of_rule _ _ _ (modelNode_ne_zero _ _)
  · exact argument_modelNode_value 117 0 _
  · exact argument_modelNode_value 117 1 _
  · exact hout
  · exact listAll_zero_value _ _
  · exact (localRule_eqRefl_one_iff _ _ _ _).mpr ⟨ht, rfl⟩

theorem certified_empty_context (E : Program 2) (d a : M)
    (hd : Checked d (zeroValue M) a)
    (ha : isSentence.value ![a] = numeralValue M 1) :
    Certified E (modelList [d, zeroValue M]) a := by
  apply (certified_iff E _ a).mpr
  have hr : rootValue (modelList [d, zeroValue M]) = d := by
    simpa only [rootValue, numeral_value_zero, List.getElem?_cons_zero, Option.getD_some] using
      modelList_entry_value (M := M) [d, zeroValue M] 0
  have hw : witnessesValue (modelList [d, zeroValue M]) = zeroValue M :=
    modelList_entry_value (M := M) [d, zeroValue M] 1
  rw [hr, hw]
  refine ⟨modelList_length_value _, hd.1, hd.2.2, ha, ?_, ?_⟩
  · rw [show contextValue d = zeroValue M from hd.2.1]
  · change axiomListValue E (contextValue d) (zeroValue M) = _
    rw [show contextValue d = zeroValue M from hd.2.1, axiomList_zero_value]

theorem equalityReflexivityCertificate_model_value (t : M) :
    equalityReflexivityCertificate.value ![t] =
      modelList [modelNode 117 [zeroValue M, modelNode 4 [t, t], t], zeroValue M] := by
  simp only [equalityReflexivityCertificate, certificateAt, syntaxNode_value,
    list_cons_value, list_nil_value, equalCode_value, Program.value_proj,
    constant_value, numeral_value_zero, Matrix.cons_val_zero,
    modelNode, modelList_cons, modelList_nil]

theorem certified_equalityReflexivity (E : Program 2) (t : M)
    (ht : namedTerm.value ![t] = numeralValue M 1)
    (hout : isSentence.value ![modelNode 4 [t, t] ] = numeralValue M 1) :
    Certified E (equalityReflexivityCertificate.value ![t]) (modelNode 4 [t, t]) := by
  rw [equalityReflexivityCertificate_model_value]
  exact certified_empty_context E _ _ (checked_equalityReflexivity t ht (isSentence_namedForm _ hout)) hout

end
end Lemmatheca.MathematicalLogic.PAComputations.ProofPrograms.CheckerPrograms
