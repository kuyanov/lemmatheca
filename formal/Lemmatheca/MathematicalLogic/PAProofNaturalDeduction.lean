import Lemmatheca.MathematicalLogic.PAProofLocalRules
import Lemmatheca.MathematicalLogic.PAProofReflexivity

/-! Each wrapper checks the actual native record for its CoreProof rule. -/
namespace Lemmatheca.MathematicalLogic.PAComputations.ProofPrograms.CheckerPrograms
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic ArithmeticTheories ArithmeticRepresentability
open SyntaxPrograms
noncomputable section
universe u
variable {M : Type u} [language.Structure M] [M ⊨ PA]

theorem checked_native_node (k : ℕ) (gamma a : M) (xs : List M)
    (hform : namedForm.value ![zeroValue M, a] = numeralValue M 1)
    (hcontext : formList.value ![zeroValue M, gamma] = numeralValue M 1)
    (hrule : localRule.value ![modelNode k (gamma :: a :: xs),
      proofHistoryValue (modelNode k (gamma :: a :: xs))] = numeralValue M 1) :
    Checked (modelNode k (gamma :: a :: xs)) gamma a := by
  apply checked_of_rule _ _ _ (modelNode_ne_zero _ _)
  · exact argument_modelNode_value k 0 _
  · exact argument_modelNode_value k 1 _
  · exact hform
  · exact hcontext
  · exact hrule

theorem holds_checked_child (k : ℕ) (xs : List M) (d gamma a : M)
    (hd : Checked d gamma a) (hmem : d ∈ xs) :
    Holds (proofHistoryValue (modelNode k xs)) d gamma a :=
  holds_of_checked _ _ _ _ _ hd (modelNode_child_smaller k xs d hmem)
    (contextIncluded_refl_value gamma)

theorem holds_checked_child_included (k : ℕ) (xs : List M) (d gamma delta a : M)
    (hd : Checked d gamma a) (hmem : d ∈ xs)
    (hinc : contextIncluded.value ![gamma, delta] = numeralValue M 1) :
    Holds (proofHistoryValue (modelNode k xs)) d delta a :=
  holds_of_checked _ _ _ _ _ hd (modelNode_child_smaller k xs d hmem) hinc

theorem checked_context (d gamma a : M) (hd : Checked d gamma a) :
    formList.value ![zeroValue M, gamma] = numeralValue M 1 := by
  have hc := (derivation_well_formed d hd.1).2
  change formList.value ![zeroValue M, contextValue d] = _ at hc
  rwa [show contextValue d = gamma from hd.2.1] at hc

theorem checked_forallElimination_into (d gamma delta b t : M)
    (hd : Checked d gamma (modelNode 7 [b]))
    (hinc : contextIncluded.value ![gamma, delta] = numeralValue M 1)
    (hb : namedForm.value ![numeralValue M 1, b] = numeralValue M 1)
    (ht : namedTerm.value ![t] = numeralValue M 1)
    (hout : namedForm.value ![zeroValue M, instantiate.value ![b, t] ] = numeralValue M 1)
    (hcontext : formList.value ![zeroValue M, delta] = numeralValue M 1) :
    Checked (modelNode 113 [delta, instantiate.value ![b, t], d, b, t])
      delta (instantiate.value ![b, t]) := by
  apply checked_native_node 113 delta _ [d, b, t] hout hcontext
  exact (localRule_allElim_one_iff _ _ _ _ _ _).mpr
    ⟨hb, ht, rfl, holds_checked_child_included 113 _ d _ _ _ hd (by simp) hinc⟩

theorem checked_modusPonens_into (d e gamma delta target a b : M)
    (hd : Checked d gamma (implication.value ![a, b])) (he : Checked e delta a)
    (hincD : contextIncluded.value ![gamma, target] = numeralValue M 1)
    (hincE : contextIncluded.value ![delta, target] = numeralValue M 1)
    (hb : namedForm.value ![zeroValue M, b] = numeralValue M 1)
    (hcontext : formList.value ![zeroValue M, target] = numeralValue M 1) :
    Checked (modelNode 108 [target, b, d, e]) target b := by
  apply checked_native_node 108 target b [d, e] hb hcontext
  apply (localRule_mp_one_iff _ _ _ _ _).mpr
  rw [show conclusionValue e = a from he.2.2]
  exact ⟨holds_checked_child_included 108 _ d _ _ _ hd (by simp) hincD,
    holds_checked_child_included 108 _ e _ _ _ he (by simp) hincE⟩

theorem checked_equalitySubstitution_into (d e gamma delta target b s t : M)
    (hd : Checked d gamma (modelNode 4 [s, t]))
    (he : Checked e delta (instantiate.value ![b, s]))
    (hincD : contextIncluded.value ![gamma, target] = numeralValue M 1)
    (hincE : contextIncluded.value ![delta, target] = numeralValue M 1)
    (hb : namedForm.value ![numeralValue M 1, b] = numeralValue M 1)
    (hs : namedTerm.value ![s] = numeralValue M 1)
    (ht : namedTerm.value ![t] = numeralValue M 1)
    (hout : namedForm.value ![zeroValue M, instantiate.value ![b, t] ] = numeralValue M 1)
    (hcontext : formList.value ![zeroValue M, target] = numeralValue M 1) :
    Checked (modelNode 118 [target, instantiate.value ![b, t], d, e, b, s, t])
      target (instantiate.value ![b, t]) := by
  apply checked_native_node 118 target _ [d, e, b, s, t] hout hcontext
  exact (localRule_eqSubst_one_iff _ _ _ _ _ _ _ _).mpr
    ⟨hb, hs, ht, rfl,
      holds_checked_child_included 118 _ d _ _ _ hd (by simp) hincD,
      holds_checked_child_included 118 _ e _ _ _ he (by simp) hincE⟩

theorem checked_assumption (gamma a : M)
    (hform : namedForm.value ![zeroValue M, a] = numeralValue M 1)
    (hcontext : formList.value ![zeroValue M, gamma] = numeralValue M 1)
    (hmem : listMember.value ![a, gamma] = numeralValue M 1) :
    Checked (modelNode 100 [gamma, a]) gamma a := by
  apply checked_native_node 100 gamma a [] hform hcontext
  exact (localRule_assumption_one_iff _ _ _).mpr hmem

theorem checked_orLeft (d gamma a b : M) (hd : Checked d gamma a)
    (hb : namedForm.value ![zeroValue M, b] = numeralValue M 1)
    (hout : namedForm.value ![zeroValue M, orValue a b] = numeralValue M 1)
    (hcontext : formList.value ![zeroValue M, gamma] = numeralValue M 1) :
    Checked (modelNode 104 [gamma, orValue a b, d, b]) gamma (orValue a b) := by
  apply checked_native_node 104 gamma _ [d, b] hout hcontext
  apply (localRule_orLeft_one_iff _ _ _ _ _).mpr
  rw [show conclusionValue d = a from hd.2.2]
  exact ⟨holds_checked_child 104 _ d gamma a hd (by simp), hb, rfl⟩

theorem checked_orRight (d gamma a b : M) (hd : Checked d gamma b)
    (ha : namedForm.value ![zeroValue M, a] = numeralValue M 1)
    (hout : namedForm.value ![zeroValue M, orValue a b] = numeralValue M 1)
    (hcontext : formList.value ![zeroValue M, gamma] = numeralValue M 1) :
    Checked (modelNode 105 [gamma, orValue a b, d, a]) gamma (orValue a b) := by
  apply checked_native_node 105 gamma _ [d, a] hout hcontext
  apply (localRule_orRight_one_iff _ _ _ _ _).mpr
  rw [show conclusionValue d = b from hd.2.2]
  exact ⟨holds_checked_child 105 _ d gamma b hd (by simp), ha, rfl⟩

theorem checked_orElim (d e f gamma a b c : M)
    (hd : Checked d gamma (orValue b c))
    (he : Checked e (listCons.value ![b, gamma]) a)
    (hf : Checked f (listCons.value ![c, gamma]) a)
    (hb : namedForm.value ![zeroValue M, b] = numeralValue M 1)
    (hc : namedForm.value ![zeroValue M, c] = numeralValue M 1)
    (hout : namedForm.value ![zeroValue M, a] = numeralValue M 1)
    (hcontext : formList.value ![zeroValue M, gamma] = numeralValue M 1) :
    Checked (modelNode 106 [gamma, a, d, e, f, b, c]) gamma a := by
  apply checked_native_node 106 gamma a [d, e, f, b, c] hout hcontext
  apply (localRule_orElim_one_iff _ _ _ _ _ _ _ _).mpr
  exact ⟨hb, hc, holds_checked_child 106 _ d _ _ hd (by simp),
    holds_checked_child 106 _ e _ _ he (by simp),
    holds_checked_child 106 _ f _ _ hf (by simp)⟩

theorem checked_impIntro (d gamma a b : M)
    (hd : Checked d (listCons.value ![a, gamma]) b)
    (ha : namedForm.value ![zeroValue M, a] = numeralValue M 1)
    (hout : namedForm.value ![zeroValue M, implication.value ![a, b] ] = numeralValue M 1)
    (hcontext : formList.value ![zeroValue M, gamma] = numeralValue M 1) :
    Checked (modelNode 107 [gamma, implication.value ![a, b], d, a])
      gamma (implication.value ![a, b]) := by
  apply checked_native_node 107 gamma _ [d, a] hout hcontext
  apply (localRule_impIntro_one_iff _ _ _ _ _).mpr
  rw [show conclusionValue d = b from hd.2.2]
  exact ⟨ha, rfl, holds_checked_child 107 _ d _ _ hd (by simp)⟩

theorem checked_impIntro_included (d gamma delta a b : M) (hd : Checked d delta b)
    (hinc : contextIncluded.value ![delta, listCons.value ![a, gamma] ] = numeralValue M 1)
    (ha : namedForm.value ![zeroValue M, a] = numeralValue M 1)
    (hout : namedForm.value ![zeroValue M, implication.value ![a, b] ] = numeralValue M 1)
    (hcontext : formList.value ![zeroValue M, gamma] = numeralValue M 1) :
    Checked (modelNode 107 [gamma, implication.value ![a, b], d, a])
      gamma (implication.value ![a, b]) := by
  apply checked_native_node 107 gamma _ [d, a] hout hcontext
  apply (localRule_impIntro_one_iff _ _ _ _ _).mpr
  rw [show conclusionValue d = b from hd.2.2]
  exact ⟨ha, rfl, holds_checked_child_included 107 _ d _ _ _ hd (by simp) hinc⟩

theorem checked_allIntro (d gamma b c : M)
    (hd : Checked d gamma (instantiate.value ![b, modelNode 8 [c] ]))
    (hb : namedForm.value ![numeralValue M 1, b] = numeralValue M 1)
    (hout : namedForm.value ![zeroValue M, modelNode 7 [b] ] = numeralValue M 1)
    (hcontext : formList.value ![zeroValue M, gamma] = numeralValue M 1)
    (hfresh : occursAux.value ![c, b] = zeroValue M)
    (hcontextFresh : contextFresh.value ![c, gamma] = numeralValue M 1) :
    Checked (modelNode 115 [gamma, modelNode 7 [b], d, b, c]) gamma (modelNode 7 [b]) := by
  apply checked_native_node 115 gamma _ [d, b, c] hout hcontext
  apply (localRule_allIntro_one_iff _ _ _ _ _ _).mpr
  exact ⟨hb, rfl, holds_checked_child 115 _ d _ _ hd (by simp), hfresh, hcontextFresh⟩

theorem checked_exIntro (d gamma b t : M)
    (hd : Checked d gamma (instantiate.value ![b, t]))
    (hb : namedForm.value ![numeralValue M 1, b] = numeralValue M 1)
    (ht : namedTerm.value ![t] = numeralValue M 1)
    (hout : namedForm.value ![zeroValue M, exValue b] = numeralValue M 1)
    (hcontext : formList.value ![zeroValue M, gamma] = numeralValue M 1) :
    Checked (modelNode 114 [gamma, exValue b, d, b, t]) gamma (exValue b) := by
  apply checked_native_node 114 gamma _ [d, b, t] hout hcontext
  exact (localRule_exIntro_one_iff _ _ _ _ _ _).mpr
    ⟨hb, ht, rfl, holds_checked_child 114 _ d _ _ hd (by simp)⟩

theorem existentialIntroductionCertificate_model_value (p b t : M) :
    existentialIntroductionCertificate.value ![p, b, t] =
      modelList [modelNode 114 [contextValue (rootValue p), exValue b, rootValue p, b, t],
        witnessesValue p] := by
  simp only [existentialIntroductionCertificate, retainWitnesses, certificateAt,
    root, witnesses, context, syntaxNode_value, list_cons_value, list_nil_value,
    binary_value, unary_value, exCode_value, Program.value_proj, constant_value,
    numeral_value_zero, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.head_cons, rootValue, witnessesValue, contextValue,
    modelNode, modelList_cons, modelList_nil]

theorem certified_exIntro (E : Program 2) (p b t : M)
    (hp : Certified E p (instantiate.value ![b, t]))
    (hb : namedForm.value ![numeralValue M 1, b] = numeralValue M 1)
    (ht : namedTerm.value ![t] = numeralValue M 1)
    (hout : isSentence.value ![exValue b] = numeralValue M 1) :
    Certified E (existentialIntroductionCertificate.value ![p, b, t]) (exValue b) := by
  obtain ⟨_, hd, hc, _, _, _⟩ := (certified_iff E p _).mp hp
  have hd' : Checked (rootValue p) (contextValue (rootValue p))
      (instantiate.value ![b, t]) := ⟨hd, rfl, hc⟩
  have hnew := checked_exIntro _ _ b t hd' hb ht (isSentence_namedForm _ hout)
    (checked_context _ _ _ hd')
  rw [existentialIntroductionCertificate_model_value]
  exact certified_retain_witnesses E p _ _ _ hp hnew hout

theorem checked_falseElim (d gamma a : M) (hd : Checked d gamma (modelNode 3 []))
    (hout : namedForm.value ![zeroValue M, a] = numeralValue M 1)
    (hcontext : formList.value ![zeroValue M, gamma] = numeralValue M 1) :
    Checked (modelNode 111 [gamma, a, d]) gamma a := by
  apply checked_native_node 111 gamma a [d] hout hcontext
  exact (localRule_falseElim_one_iff _ _ _ _).mpr
    (holds_checked_child 111 _ d _ _ hd (by simp))

theorem checked_notIntro (d gamma a : M)
    (hd : Checked d (listCons.value ![a, gamma]) (modelNode 3 []))
    (ha : namedForm.value ![zeroValue M, a] = numeralValue M 1)
    (hout : namedForm.value ![zeroValue M, negValue a] = numeralValue M 1)
    (hcontext : formList.value ![zeroValue M, gamma] = numeralValue M 1) :
    Checked (modelNode 109 [gamma, negValue a, d, a]) gamma (negValue a) := by
  apply checked_native_node 109 gamma _ [d, a] hout hcontext
  exact (localRule_notIntro_one_iff _ _ _ _ _).mpr
    ⟨ha, rfl, holds_checked_child 109 _ d _ _ hd (by simp)⟩

theorem checked_notElim (d e gamma a : M)
    (hd : Checked d gamma a) (he : Checked e gamma (negValue a))
    (hout : namedForm.value ![zeroValue M, modelNode 3 [] ] = numeralValue M 1)
    (hcontext : formList.value ![zeroValue M, gamma] = numeralValue M 1) :
    Checked (modelNode 110 [gamma, modelNode 3 [], d, e]) gamma (modelNode 3 []) := by
  apply checked_native_node 110 gamma _ [d, e] hout hcontext
  apply (localRule_notElim_one_iff _ _ _ _ _).mpr
  rw [show conclusionValue d = a from hd.2.2]
  exact ⟨rfl, holds_checked_child 110 _ d _ _ hd (by simp),
    holds_checked_child 110 _ e _ _ he (by simp)⟩

theorem checked_notElim_into (d e gamma delta target a : M)
    (hd : Checked d gamma a) (he : Checked e delta (negValue a))
    (hincD : contextIncluded.value ![gamma, target] = numeralValue M 1)
    (hincE : contextIncluded.value ![delta, target] = numeralValue M 1)
    (hout : namedForm.value ![zeroValue M, modelNode 3 [] ] = numeralValue M 1)
    (hcontext : formList.value ![zeroValue M, target] = numeralValue M 1) :
    Checked (modelNode 110 [target, modelNode 3 [], d, e]) target (modelNode 3 []) := by
  apply checked_native_node 110 target _ [d, e] hout hcontext
  apply (localRule_notElim_one_iff _ _ _ _ _).mpr
  rw [show conclusionValue d = a from hd.2.2]
  exact ⟨rfl, holds_checked_child_included 110 _ d _ _ _ hd (by simp) hincD,
    holds_checked_child_included 110 _ e _ _ _ he (by simp) hincE⟩

theorem checked_byContra (d gamma a : M)
    (hd : Checked d (listCons.value ![negValue a, gamma]) (modelNode 3 []))
    (hout : namedForm.value ![zeroValue M, a] = numeralValue M 1)
    (hcontext : formList.value ![zeroValue M, gamma] = numeralValue M 1) :
    Checked (modelNode 112 [gamma, a, d]) gamma a := by
  apply checked_native_node 112 gamma _ [d] hout hcontext
  exact (localRule_byContra_one_iff _ _ _ _).mpr
    (holds_checked_child 112 _ d _ _ hd (by simp))

end
end Lemmatheca.MathematicalLogic.PAComputations.ProofPrograms.CheckerPrograms
