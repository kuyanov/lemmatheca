import Lemmatheca.PaProofCheckers.PAProofUniversalElimination

open Lemmatheca.MathematicalLogic Lemmatheca.ModelTheory Lemmatheca.ComputabilityTheory

namespace Lemmatheca.ProofTheory.PAComputations.ProofPrograms.CheckerPrograms
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic ArithmeticTheories ArithmeticRepresentability
open SyntaxPrograms
noncomputable section
universe u
variable {M : Type u} [language.Structure M] [M ⊨ PA]

theorem certified_merge_roots (E : Program 2) (p q a b d c : M)
    (hp : Certified E p a) (hq : Certified E q b)
    (hd : Checked d
      (listAppend.value ![contextValue (rootValue p), contextValue (rootValue q)]) c)
    (hc : isSentence.value ![c] = numeralValue M 1) :
    Certified E (modelList [d, listAppend.value ![witnessesValue p, witnessesValue q] ]) c := by
  obtain ⟨_, _, _, _, hpl, hpw⟩ := (certified_iff E p a).mp hp
  obtain ⟨_, _, _, _, hql, hqw⟩ := (certified_iff E q b).mp hq
  apply (certified_iff E _ c).mpr
  have hr : rootValue (modelList [d, listAppend.value ![witnessesValue p, witnessesValue q] ]) = d := by
    simpa only [rootValue, numeral_value_zero, List.getElem?_cons_zero, Option.getD_some] using
      modelList_entry_value (M := M) [d, listAppend.value ![witnessesValue p, witnessesValue q] ] 0
  have hw : witnessesValue (modelList [d, listAppend.value ![witnessesValue p, witnessesValue q] ]) =
      listAppend.value ![witnessesValue p, witnessesValue q] :=
    modelList_entry_value (M := M) [d, listAppend.value ![witnessesValue p, witnessesValue q] ] 1
  rw [hr, hw]
  refine ⟨modelList_length_value _, hd.1, hd.2.2, hc, ?_, ?_⟩
  · rw [show contextValue d = _ from hd.2.1, listLength_append_value, listLength_append_value, hpl, hql]
  · change axiomListValue E (contextValue d) (listAppend.value ![witnessesValue p, witnessesValue q]) = _
    rw [show contextValue d = _ from hd.2.1, axiomList_append_value E _ _ _ _ hpl]
    rw [show axiomListValue E (contextValue (rootValue p)) (witnessesValue p) = numeralValue M 1 from hpw,
      show axiomListValue E (contextValue (rootValue q)) (witnessesValue q) = numeralValue M 1 from hqw,
      numeral_one_mul_model]

theorem checked_equalitySubstitution (d e gamma delta b s t : M)
    (hd : Checked d gamma (modelNode 4 [s, t]))
    (he : Checked e delta (instantiate.value ![b, s]))
    (hb : namedForm.value ![numeralValue M 1, b] = numeralValue M 1)
    (hs : namedTerm.value ![s] = numeralValue M 1)
    (ht : namedTerm.value ![t] = numeralValue M 1)
    (hout : namedForm.value ![zeroValue M, instantiate.value ![b, t] ] = numeralValue M 1) :
    Checked (modelNode 118 [listAppend.value ![gamma, delta], instantiate.value ![b, t], d, e, b, s, t])
      (listAppend.value ![gamma, delta]) (instantiate.value ![b, t]) := by
  let m := modelNode 118 [listAppend.value ![gamma, delta], instantiate.value ![b, t], d, e, b, s, t]
  have hdctx : contextValue d = gamma := hd.2.1
  have hectx : contextValue e = delta := he.2.1
  have hctxd := (derivation_well_formed d hd.1).2
  have hctxe := (derivation_well_formed e he.1).2
  change formList.value ![zeroValue M, contextValue d] = numeralValue M 1 at hctxd
  change formList.value ![zeroValue M, contextValue e] = numeralValue M 1 at hctxe
  rw [hdctx] at hctxd
  rw [hectx] at hctxe
  have hdm : leValue M (succValue M d) m := modelNode_child_smaller 118 _ d (by simp)
  have hem : leValue M (succValue M e) m := modelNode_child_smaller 118 _ e (by simp)
  apply checked_of_rule m _ _ (modelNode_ne_zero _ _)
  · exact argument_modelNode_value 118 0 _
  · exact argument_modelNode_value 118 1 _
  · exact hout
  · rw [formList_append_value, hctxd, hctxe, numeral_one_mul_model]
  · apply (localRule_eqSubst_one_iff _ _ _ _ _ _ _ _).mpr
    refine ⟨hb, hs, ht, rfl, ?_, ?_⟩
    · refine ⟨?_, hd.2.2, ?_⟩
      · rw [derivation_history_entry_value m d hdm]
        exact hd.1
      · rw [hdctx]
        exact contextIncluded_append_left_value gamma delta
    · refine ⟨?_, he.2.2, ?_⟩
      · rw [derivation_history_entry_value m e hem]
        exact he.1
      · rw [hectx]
        exact contextIncluded_append_right_value gamma delta

theorem equalitySubstitutionCertificate_model_value (p q b s t : M) :
    equalitySubstitutionCertificate.value ![p, q, b, s, t] =
      modelList [modelNode 118
        [listAppend.value ![contextValue (rootValue p), contextValue (rootValue q)],
          instantiate.value ![b, t], rootValue p, rootValue q, b, s, t],
        listAppend.value ![witnessesValue p, witnessesValue q] ] := by
  simp only [equalitySubstitutionCertificate, certificateAt, root, witnesses, context,
    syntaxNode_value, list_cons_value, list_nil_value, binary_value, unary_value,
    Program.value_proj, constant_value, numeral_value_zero, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
    Matrix.tail_cons, Matrix.head_cons, rootValue, witnessesValue, contextValue,
    modelNode, modelList_cons, modelList_nil]

theorem certified_equalitySubstitution (E : Program 2) (p q b s t : M)
    (hp : Certified E p (modelNode 4 [s, t]))
    (hq : Certified E q (instantiate.value ![b, s]))
    (hb : namedForm.value ![numeralValue M 1, b] = numeralValue M 1)
    (hs : namedTerm.value ![s] = numeralValue M 1)
    (ht : namedTerm.value ![t] = numeralValue M 1)
    (hout : isSentence.value ![instantiate.value ![b, t] ] = numeralValue M 1) :
    Certified E (equalitySubstitutionCertificate.value ![p, q, b, s, t])
      (instantiate.value ![b, t]) := by
  obtain ⟨_, hpd, hpc, _, _, _⟩ := (certified_iff E p _).mp hp
  obtain ⟨_, hqd, hqc, _, _, _⟩ := (certified_iff E q _).mp hq
  rw [equalitySubstitutionCertificate_model_value]
  apply certified_merge_roots E p q _ _ _ _ hp hq ?_ hout
  exact checked_equalitySubstitution _ _ _ _ b s t ⟨hpd, rfl, hpc⟩ ⟨hqd, rfl, hqc⟩
    hb hs ht (isSentence_namedForm _ hout)

end
end Lemmatheca.ProofTheory.PAComputations.ProofPrograms.CheckerPrograms
