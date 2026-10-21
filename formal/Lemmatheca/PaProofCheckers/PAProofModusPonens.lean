import Lemmatheca.PaProofCheckers.PAProofRuleFacts

open Lemmatheca.MathematicalLogic Lemmatheca.ModelTheory Lemmatheca.ComputabilityTheory

namespace Lemmatheca.ProofTheory.PAComputations.ProofPrograms.CheckerPrograms
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic ArithmeticTheories ArithmeticRepresentability
open SyntaxPrograms
noncomputable section
universe u
variable {M : Type u} [language.Structure M] [M ⊨ PA]

theorem formList_append_value (p gamma delta : M) :
    formList.value ![p, listAppend.value ![gamma, delta] ] =
      mulValue M (formList.value ![p, gamma]) (formList.value ![p, delta]) :=
  listAll_append_value _ p gamma delta

theorem checked_modusPonens (d e gamma delta a b : M)
    (hd : Checked d gamma (implication.value ![a, b]))
    (he : Checked e delta a)
    (hb : namedForm.value ![zeroValue M, b] = numeralValue M 1) :
    Checked (modelNode 108 [listAppend.value ![gamma, delta], b, d, e])
      (listAppend.value ![gamma, delta]) b := by
  let m := modelNode 108 [listAppend.value ![gamma, delta], b, d, e]
  have hdctx : contextValue d = gamma := hd.2.1
  have hectx : contextValue e = delta := he.2.1
  have heconcl : conclusionValue e = a := he.2.2
  have hctxd := (derivation_well_formed d hd.1).2
  have hctxe := (derivation_well_formed e he.1).2
  change formList.value ![zeroValue M, contextValue d] = numeralValue M 1 at hctxd
  change formList.value ![zeroValue M, contextValue e] = numeralValue M 1 at hctxe
  rw [hdctx] at hctxd
  rw [hectx] at hctxe
  have hdm : leValue M (succValue M d) m :=
    modelNode_child_smaller 108 _ d (by simp)
  have hem : leValue M (succValue M e) m :=
    modelNode_child_smaller 108 _ e (by simp)
  apply checked_of_rule m _ b (modelNode_ne_zero _ _)
  · exact argument_modelNode_value 108 0 _
  · exact argument_modelNode_value 108 1 _
  · exact hb
  · rw [formList_append_value, hctxd, hctxe, numeral_one_mul_model]
  · apply (localRule_mp_one_iff _ _ _ _ _).mpr
    constructor
    · refine ⟨?_, ?_, ?_⟩
      · rw [derivation_history_entry_value m d hdm]
        exact hd.1
      · rw [heconcl]
        exact hd.2.2
      · rw [hdctx]
        exact contextIncluded_append_left_value gamma delta
    · refine ⟨?_, rfl, ?_⟩
      · rw [derivation_history_entry_value m e hem]
        exact he.1
      · rw [hectx]
        exact contextIncluded_append_right_value gamma delta

theorem modusPonensRecord_model_value (d e b : M) :
    modusPonensRecord.value ![d, e, b] =
      modelNode 108 [listAppend.value ![contextValue d, contextValue e], b, d, e] := by
  exact modusPonensRecord_value d e b

theorem modusPonensCertificate_model_value (p q b : M) :
    modusPonensCertificate.value ![p, q, b] =
      modelList [modusPonensRecord.value ![rootValue p, rootValue q, b],
        listAppend.value ![witnessesValue p, witnessesValue q] ] := by
  simp only [modusPonensCertificate, list_cons_value, list_nil_value,
    ternary_value, binary_value, Program.value_proj, constant_value, numeral_value_zero,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.head_cons, rootValue, witnessesValue, modelList_cons, modelList_nil]

/-- Uniform MP closure for the actual native certificate checker.  The axiom
verifier is arbitrary; accepted axiom/certificate pairs are simply retained. -/
theorem certified_modusPonens (E : Program 2) (p q a b : M)
    (hp : Certified E p (implication.value ![a, b]))
    (hq : Certified E q a)
    (hb : isSentence.value ![b] = numeralValue M 1) :
    Certified E (modusPonensCertificate.value ![p, q, b]) b := by
  obtain ⟨_, hpd, hpc, _, hpl, hpw⟩ := (certified_iff E p _).mp hp
  obtain ⟨_, hqd, hqc, _, hql, hqw⟩ := (certified_iff E q _).mp hq
  have hchecked := checked_modusPonens (rootValue p) (rootValue q)
    (contextValue (rootValue p)) (contextValue (rootValue q)) a b
    ⟨hpd, rfl, hpc⟩ ⟨hqd, rfl, hqc⟩ (isSentence_namedForm b hb)
  let d := modusPonensRecord.value ![rootValue p, rootValue q, b]
  have hd : Checked d
      (listAppend.value ![contextValue (rootValue p), contextValue (rootValue q)]) b := by
    rw [show d = _ from modusPonensRecord_model_value _ _ _]
    exact hchecked
  rw [modusPonensCertificate_model_value]
  apply (certified_iff E _ b).mpr
  have hr : rootValue (modelList [d, listAppend.value ![witnessesValue p, witnessesValue q] ]) = d := by
    simpa only [rootValue, numeral_value_zero, List.getElem?_cons_zero, Option.getD_some] using
      modelList_entry_value (M := M) [d, listAppend.value ![witnessesValue p, witnessesValue q] ] 0
  have hw : witnessesValue (modelList [d, listAppend.value ![witnessesValue p, witnessesValue q] ]) =
      listAppend.value ![witnessesValue p, witnessesValue q] := by
    exact modelList_entry_value (M := M) [d, listAppend.value ![witnessesValue p, witnessesValue q] ] 1
  change listLength.value ![modelList [d, listAppend.value ![witnessesValue p, witnessesValue q] ] ] = _ ∧ _
  rw [hr, hw]
  refine ⟨modelList_length_value _, hd.1, hd.2.2, hb, ?_, ?_⟩
  · rw [show contextValue d = _ from hd.2.1, listLength_append_value, listLength_append_value, hpl, hql]
  · change axiomListValue E (contextValue d) (listAppend.value ![witnessesValue p, witnessesValue q]) = _
    rw [show contextValue d = _ from hd.2.1, axiomList_append_value E _ _ _ _ hpl]
    rw [show axiomListValue E (contextValue (rootValue p)) (witnessesValue p) = numeralValue M 1 from hpw,
      show axiomListValue E (contextValue (rootValue q)) (witnessesValue q) = numeralValue M 1 from hqw,
      numeral_one_mul_model]

end
end Lemmatheca.ProofTheory.PAComputations.ProofPrograms.CheckerPrograms
