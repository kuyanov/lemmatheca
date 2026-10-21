import Lemmatheca.PaProofCheckers.PAProofModusPonens

open Lemmatheca.MathematicalLogic Lemmatheca.ModelTheory Lemmatheca.ComputabilityTheory

namespace Lemmatheca.ProofTheory.PAComputations.ProofPrograms.CheckerPrograms
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic ArithmeticTheories ArithmeticRepresentability
open SyntaxPrograms
noncomputable section
universe u
variable {M : Type u} [language.Structure M] [M ⊨ PA]

theorem checked_forallElimination (d gamma b t : M)
    (hd : Checked d gamma (modelNode 7 [b]))
    (hb : namedForm.value ![numeralValue M 1, b] = numeralValue M 1)
    (ht : namedTerm.value ![t] = numeralValue M 1)
    (hout : namedForm.value ![zeroValue M, instantiate.value ![b, t] ] = numeralValue M 1) :
    Checked (modelNode 113 [gamma, instantiate.value ![b, t], d, b, t])
      gamma (instantiate.value ![b, t]) := by
  let m := modelNode 113 [gamma, instantiate.value ![b, t], d, b, t]
  have hctx : contextValue d = gamma := hd.2.1
  have hcontext := (derivation_well_formed d hd.1).2
  change formList.value ![zeroValue M, contextValue d] = numeralValue M 1 at hcontext
  rw [hctx] at hcontext
  have hdm : leValue M (succValue M d) m :=
    modelNode_child_smaller 113 _ d (by simp)
  apply checked_of_rule m gamma _ (modelNode_ne_zero _ _)
  · exact argument_modelNode_value 113 0 _
  · exact argument_modelNode_value 113 1 _
  · exact hout
  · exact hcontext
  · apply (localRule_allElim_one_iff _ _ _ _ _ _).mpr
    refine ⟨hb, ht, rfl, ?_, hd.2.2, ?_⟩
    · rw [derivation_history_entry_value m d hdm]
      exact hd.1
    · rw [hctx]
      exact contextIncluded_refl_value gamma

/-- A checked new root over the same axiom context retains the old finite
axiom certificates unchanged. -/
theorem certified_retain_witnesses (E : Program 2) (p a d b : M)
    (hp : Certified E p a)
    (hd : Checked d (contextValue (rootValue p)) b)
    (hb : isSentence.value ![b] = numeralValue M 1) :
    Certified E (modelList [d, witnessesValue p]) b := by
  obtain ⟨_, _, _, _, hlen, hscan⟩ := (certified_iff E p a).mp hp
  apply (certified_iff E _ b).mpr
  have hr : rootValue (modelList [d, witnessesValue p]) = d := by
    simpa only [rootValue, numeral_value_zero, List.getElem?_cons_zero, Option.getD_some] using
      modelList_entry_value (M := M) [d, witnessesValue p] 0
  have hw : witnessesValue (modelList [d, witnessesValue p]) = witnessesValue p :=
    modelList_entry_value (M := M) [d, witnessesValue p] 1
  rw [hr, hw]
  refine ⟨modelList_length_value _, hd.1, hd.2.2, hb, ?_, ?_⟩
  · rw [show contextValue d = _ from hd.2.1]
    exact hlen
  · rw [show contextValue d = _ from hd.2.1]
    exact hscan

theorem forallEliminationCertificate_model_value (p b t : M) :
    forallEliminationCertificate.value ![p, b, t] =
      modelList [modelNode 113 [contextValue (rootValue p), instantiate.value ![b, t],
        rootValue p, b, t], witnessesValue p] := by
  simp only [forallEliminationCertificate, retainWitnesses, certificateAt,
    root, witnesses, context, syntaxNode_value, list_cons_value, list_nil_value,
    binary_value, unary_value, Program.value_proj, constant_value, numeral_value_zero,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.head_cons, rootValue, witnessesValue, contextValue,
    modelNode, modelList_cons, modelList_nil]

/-- Uniform universal elimination for the actual closed-term record constructor.
The hypotheses are the syntactic checks performed by the shared checker. -/
theorem certified_forallElimination (E : Program 2) (p b t : M)
    (hp : Certified E p (modelNode 7 [b]))
    (hb : namedForm.value ![numeralValue M 1, b] = numeralValue M 1)
    (ht : namedTerm.value ![t] = numeralValue M 1)
    (hout : isSentence.value ![instantiate.value ![b, t] ] = numeralValue M 1) :
    Certified E (forallEliminationCertificate.value ![p, b, t]) (instantiate.value ![b, t]) := by
  obtain ⟨_, hder, hconcl, _, _, _⟩ := (certified_iff E p _).mp hp
  have hd := checked_forallElimination (rootValue p) (contextValue (rootValue p)) b t
    ⟨hder, rfl, hconcl⟩ hb ht (isSentence_namedForm _ hout)
  rw [forallEliminationCertificate_model_value]
  exact certified_retain_witnesses E p _ _ _ hp hd hout

end
end Lemmatheca.ProofTheory.PAComputations.ProofPrograms.CheckerPrograms
