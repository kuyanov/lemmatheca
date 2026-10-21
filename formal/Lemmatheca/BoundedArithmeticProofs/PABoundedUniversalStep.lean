import Lemmatheca.BoundedArithmeticProofs.PABoundedUniversalBase

open Lemmatheca.MathematicalLogic Lemmatheca.ModelTheory Lemmatheca.ComputabilityTheory

namespace Lemmatheca.ProofTheory.PAComputations.ProofPrograms.CheckerPrograms.BoundedUniversalPrograms
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic ArithmeticTheories ArithmeticRepresentability FirstOrderProofs
open ArithmeticProofPredicates SyntaxPrograms FixedSyntaxPrograms InitialSegmentPrograms
noncomputable section
universe u
variable {M : Type u} [language.Structure M] [M ⊨ PA]

def stepRootValue (body n p next q : M) : M :=
  let gamma := listAppend.value ![contextValue (rootValue p),
    listAppend.value ![contextValue (rootValue q), contextValue (rootValue next)] ]
  let z := modelNode 8 [zeroValue M]
  let a := upperValue 0 z (succValue M n)
  let b := upperValue 0 z n
  let c := modelNode 4 [z, ProofPrograms.numeral.value ![succValue M n] ]
  let out := instantiate.value ![body, z]
  let ext := listCons.value ![a, gamma]
  let left := listCons.value ![b, ext]
  let right := listCons.value ![c, ext]
  let q1 := modelNode 113 [gamma, stepFirstValue n, rootValue q,
    stepOuterBodyValue, ProofPrograms.numeral.value ![n] ]
  let q2 := modelNode 113 [gamma, stepSecondValue n, q1, stepInnerBodyValue n, z]
  let ass := modelNode 100 [ext, a]
  let dichotomy := modelNode 108 [ext, orValue b c, q2, ass]
  let p1 := modelNode 113 [gamma, implication.value ![b, out], rootValue p, matrixValue body n, z]
  let pass := modelNode 100 [left, b]
  let dl := modelNode 108 [left, out, p1, pass]
  let eqass := modelNode 100 [right, c]
  let dr := transportAlongEqualityValue right eqass (rootValue next) body z
    (ProofPrograms.numeral.value ![succValue M n])
  let cases := modelNode 106 [ext, out, dichotomy, dl, dr, b, c]
  let discharged := modelNode 107 [gamma, implication.value ![a, out], cases, a]
  let targetBody := matrixValue body (succValue M n)
  modelNode 115 [gamma, modelNode 7 [targetBody], discharged, targetBody, zeroValue M]

theorem checked_boundedStepRoot (body n p next q : M)
    (hp : Checked (rootValue p) (contextValue (rootValue p)) (modelNode 7 [matrixValue body n]))
    (hn : Checked (rootValue next) (contextValue (rootValue next))
      (instantiate.value ![body, ProofPrograms.numeral.value ![succValue M n] ]))
    (hq : Checked (rootValue q) (contextValue (rootValue q)) (modelNode 7 [stepOuterBodyValue]))
    (hb : FormulaBound 1 body)
    (hinst : NamedFormulaBound 0 (instantiate.value ![body, modelNode 8 [zeroValue M] ]))
    (hbodyFresh : occursAux.value ![zeroValue M, body] = zeroValue M)
    (hfresh : contextFresh.value ![zeroValue M, listAppend.value
      ![contextValue (rootValue p), listAppend.value
        ![contextValue (rootValue q), contextValue (rootValue next)] ] ] = numeralValue M 1) :
    Checked (stepRootValue body n p next q) (listAppend.value
      ![contextValue (rootValue p), listAppend.value
        ![contextValue (rootValue q), contextValue (rootValue next)] ])
      (modelNode 7 [matrixValue body (succValue M n)]) := by
  let gamma := listAppend.value ![contextValue (rootValue p), listAppend.value
    ![contextValue (rootValue q), contextValue (rootValue next)] ]
  let z := modelNode 8 [zeroValue M]
  let a := upperValue 0 z (succValue M n)
  let b := upperValue 0 z n
  let c := modelNode 4 [z, ProofPrograms.numeral.value ![succValue M n] ]
  let out := instantiate.value ![body, z]
  let ext := listCons.value ![a, gamma]
  let left := listCons.value ![b, ext]
  let right := listCons.value ![c, ext]
  have hgamma : formList.value ![zeroValue M, gamma] = numeralValue M 1 := by
    rw [show gamma = _ from rfl, formList_append_value, formList_append_value,
      checked_context _ _ _ hp, checked_context _ _ _ hq, checked_context _ _ _ hn,
      numeral_one_mul_model, numeral_one_mul_model]
  have hincQ : contextIncluded.value ![contextValue (rootValue q), gamma] = numeralValue M 1 :=
    contextIncluded_trans_value _ _ gamma (contextIncluded_append_left_value _ _)
      (contextIncluded_append_right_value _ _)
  have hincN : contextIncluded.value ![contextValue (rootValue next), gamma] = numeralValue M 1 :=
    contextIncluded_trans_value _ _ gamma (contextIncluded_append_right_value _ _)
      (contextIncluded_append_right_value _ _)
  have hq1 := checked_forallElimination_into (rootValue q) (contextValue (rootValue q)) gamma
    stepOuterBodyValue (ProofPrograms.numeral.value ![n]) hq hincQ stepOuterBody_namedForm
    (numeral_namedTerm n) (by rw [stepOuterBody_instantiate]; exact stepFirst_namedForm n) hgamma
  rw [stepOuterBody_instantiate] at hq1
  have hq1' : Checked
      (modelNode 113 [gamma, stepFirstValue n, rootValue q, stepOuterBodyValue,
        ProofPrograms.numeral.value ![n] ]) gamma (modelNode 7 [stepInnerBodyValue n]) := by
    simpa only [stepFirst_all] using hq1
  have hq2 := checked_forallElimination_into _ gamma gamma (stepInnerBodyValue n) z hq1'
    (contextIncluded_refl_value gamma) (stepInnerBody_namedForm n) aux_zero_namedTerm
    (by rw [stepInnerBody_instantiate]; exact stepSecond_namedForm n) hgamma
  rw [stepInnerBody_instantiate] at hq2
  have ha := upperValue_namedBound 0 z (succValue M n) (NamedTermBound.aux 0 _)
  have hbf := upperValue_namedBound 0 z n (NamedTermBound.aux 0 _)
  have hc : NamedFormulaBound 0 c := NamedFormulaBound.equal (NamedTermBound.aux 0 _)
    (((PureTerm.numeral (succValue M n)).termBound 0).named)
  have hbc := named_or_bound hbf hc
  have hext : formList.value ![zeroValue M, ext] = numeralValue M 1 :=
    (formList_cons_one_iff _ _ _).mpr ⟨namedForm_zero ha, hgamma⟩
  have hleft : formList.value ![zeroValue M, left] = numeralValue M 1 :=
    (formList_cons_one_iff _ _ _).mpr ⟨namedForm_zero hbf, hext⟩
  have hright : formList.value ![zeroValue M, right] = numeralValue M 1 :=
    (formList_cons_one_iff _ _ _).mpr ⟨namedForm_zero hc, hext⟩
  have hass := checked_assumption ext a (namedForm_zero ha) hext
    ((listMember_cons_one_iff _ _ _).mpr (Or.inl rfl))
  have hq2' := hq2
  rw [stepSecond_implication] at hq2'
  have hsplit := checked_modusPonens_into _ _ gamma ext ext a (orValue b c) hq2' hass
    (contextIncluded_under_cons gamma a) (contextIncluded_refl_value ext) (namedForm_zero hbc) hext
  have hp1 := checked_forallElimination_into (rootValue p) (contextValue (rootValue p)) gamma
    (matrixValue body n) z hp (contextIncluded_append_left_value _ _) (matrix_namedForm body n hb)
    aux_zero_namedTerm (by
      rw [matrix_instantiate body n hb, implication_node_value]
      exact namedForm_zero (hbf.imp hinst)) hgamma
  rw [matrix_instantiate body n hb] at hp1
  have hpass := checked_assumption left b (namedForm_zero hbf) hleft
    ((listMember_cons_one_iff _ _ _).mpr (Or.inl rfl))
  have hincL : contextIncluded.value ![gamma, left] = numeralValue M 1 :=
    contextIncluded_trans_value gamma ext left (contextIncluded_under_cons gamma a)
      (contextIncluded_under_cons ext b)
  have hdl := checked_modusPonens_into _ _ gamma left left b out hp1 hpass hincL
    (contextIncluded_refl_value left) (namedForm_zero hinst) hleft
  have heqass := checked_assumption right c (namedForm_zero hc) hright
    ((listMember_cons_one_iff _ _ _).mpr (Or.inl rfl))
  have hincR : contextIncluded.value ![contextValue (rootValue next), right] = numeralValue M 1 :=
    contextIncluded_trans_value _ gamma right hincN
      (contextIncluded_trans_value gamma ext right (contextIncluded_under_cons gamma a)
        (contextIncluded_under_cons ext c))
  have hdr := checked_transportAlongEquality right (contextValue (rootValue next)) _ (rootValue next)
    body z (ProofPrograms.numeral.value ![succValue M n]) heqass hn hincR (NamedTermBound.aux 0 _)
    (((PureTerm.numeral (succValue M n)).termBound 0).named)
    (fun u => rewrite_slot_aux_name_value _ _ _) hb.namedForm (namedForm_zero hinst) hright
  have hcases := checked_orElim _ _ _ ext out b c hsplit hdl hdr
    (namedForm_zero hbf) (namedForm_zero hc) (namedForm_zero hinst) hext
  have himp := checked_impIntro _ gamma a out hcases (namedForm_zero ha)
    (by rw [implication_node_value]; exact namedForm_zero (ha.imp hinst)) hgamma
  have hfinal := checked_allIntro _ gamma (matrixValue body (succValue M n)) (zeroValue M)
    (by rw [matrix_instantiate body _ hb]; exact himp)
    (matrix_namedForm body _ hb) (isSentence_namedForm _ (matrix_sentence body _ hb)) hgamma
    (matrix_occursAux_zero _ body _ hbodyFresh) hfresh
  simpa only [stepRootValue, stepSecond_implication] using hfinal

def stepFixedValue : M := numeralValue M (fixedCertificate stepSentence step_sentence_derives)

theorem stepCertificate_model_value (n p next body : M)
    (hp : conclusionValue (rootValue p) = modelNode 7 [matrixValue body n])
    (hb : FormulaBound 1 body) :
    stepCertificate.value ![n, p, next, body] =
      modelList [stepRootValue body n p next (stepFixedValue (M := M)), listAppend.value
        ![witnessesValue p, listAppend.value
          ![witnessesValue (stepFixedValue (M := M)), witnessesValue next] ] ] := by
  have hq : conclusionValue (rootValue (stepFixedValue (M := M))) = modelNode 7 [stepOuterBodyValue] :=
    (certified_iff _ _ _).mp fixedStep_certified |>.2.2.1
  simp only [stepCertificate, certificateAt, FixedSyntaxPrograms.list_value,
    syntaxNode_model_value, List.map_cons, List.map_nil, root_program_value,
    context_program_value, conclusion_program_value, witnesses_program_value,
    impCode, binary_value, unary_value, upperAt_model_value, equalCode_value, matrix_model_value,
    allCode_value, orCode_value, value_comp_six, transportAlongEqualityRecord_model_value,
    fixedProof, constant_value, numeral_value_zero, Program.value_proj, Program.value_succ,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons, stepFixedValue, stepRootValue] at hq ⊢
  rw [hp, hq, argument_modelNode_value, argument_modelNode_value]
  simp only [List.getElem?_cons_zero, Option.getD_some, stepOuterBody_instantiate]
  have hi : (argument 0).value ![stepFirstValue n] = stepInnerBodyValue n := by
    rw [stepFirst_all, argument_modelNode_value]
    rfl
  rw [hi, stepInnerBody_instantiate]
  rw [matrix_instantiate body n hb]

theorem certified_stepCertificate (n p next body : M)
    (hp : Certified axiomVerifier p (modelNode 7 [matrixValue body n]))
    (hn : Certified axiomVerifier next
      (instantiate.value ![body, ProofPrograms.numeral.value ![succValue M n] ]))
    (hb : FormulaBound 1 body)
    (hinst : NamedFormulaBound 0 (instantiate.value ![body, modelNode 8 [zeroValue M] ]))
    (hbodyFresh : occursAux.value ![zeroValue M, body] = zeroValue M) :
    Certified axiomVerifier (stepCertificate.value ![n, p, next, body])
      (modelNode 7 [matrixValue body (succValue M n)]) := by
  let q := stepFixedValue (M := M)
  have hq : Certified axiomVerifier q (modelNode 7 [stepOuterBodyValue]) := fixedStep_certified
  obtain ⟨_, hpd, hpc, _, _, _⟩ := (certified_iff _ _ _).mp hp
  obtain ⟨_, hnd, hnc, _, _, _⟩ := (certified_iff _ _ _).mp hn
  obtain ⟨_, hqd, hqc, _, _, _⟩ := (certified_iff _ _ _).mp hq
  have hfresh : contextFresh.value ![zeroValue M, listAppend.value
      ![contextValue (rootValue p), listAppend.value
        ![contextValue (rootValue q), contextValue (rootValue next)] ] ] = numeralValue M 1 := by
    rw [contextFresh_append_value, contextFresh_append_value,
      certified_contextFresh _ _ _ _ hp, certified_contextFresh _ _ _ _ hq,
      certified_contextFresh _ _ _ _ hn, numeral_one_mul_model, numeral_one_mul_model]
  have hd := checked_boundedStepRoot body n p next q ⟨hpd, rfl, hpc⟩ ⟨hnd, rfl, hnc⟩
    ⟨hqd, rfl, hqc⟩ hb hinst hbodyFresh hfresh
  rw [stepCertificate_model_value _ _ _ _ hpc hb]
  exact certified_from_axiomContext _ _ _ _ _ hd (matrix_sentence body _ hb)
    ((certified_axiomContext _ _ _ hp).append
      ((certified_axiomContext _ _ _ hq).append (certified_axiomContext _ _ _ hn)))

end
end Lemmatheca.ProofTheory.PAComputations.ProofPrograms.CheckerPrograms.BoundedUniversalPrograms
