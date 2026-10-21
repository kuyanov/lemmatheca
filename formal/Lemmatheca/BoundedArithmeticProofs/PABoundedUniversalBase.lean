import Lemmatheca.BoundedArithmeticProofs.PABoundedUniversalPrograms
import Lemmatheca.PaProofCheckers.PAProofContextFreshness

open Lemmatheca.MathematicalLogic Lemmatheca.ModelTheory Lemmatheca.ComputabilityTheory

namespace Lemmatheca.ProofTheory.PAComputations.ProofPrograms.CheckerPrograms.BoundedUniversalPrograms
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic ArithmeticTheories ArithmeticRepresentability FirstOrderProofs
open ArithmeticProofPredicates SyntaxPrograms FixedSyntaxPrograms InitialSegmentPrograms
noncomputable section
universe u
variable {M : Type u} [language.Structure M] [M ⊨ PA]

def AxiomContext (E : Program 2) (gamma witnesses : M) : Prop :=
  listLength.value ![gamma] = listLength.value ![witnesses] ∧
    axiomListValue E gamma witnesses = numeralValue M 1

theorem certified_axiomContext (E : Program 2) (p a : M) (hp : Certified E p a) :
    AxiomContext E (contextValue (rootValue p)) (witnessesValue p) := by
  obtain ⟨_, _, _, _, hlen, hscan⟩ := (certified_iff E p a).mp hp
  exact ⟨hlen, hscan⟩

theorem AxiomContext.append {E : Program 2} {gamma delta w v : M}
    (hp : AxiomContext E gamma w) (hq : AxiomContext E delta v) :
    AxiomContext E (listAppend.value ![gamma, delta]) (listAppend.value ![w, v]) := by
  constructor
  · rw [listLength_append_value, listLength_append_value, hp.1, hq.1]
  · rw [axiomList_append_value E gamma w delta v hp.1, hp.2, hq.2, numeral_one_mul_model]

theorem certified_from_axiomContext (E : Program 2) (d gamma w a : M)
    (hd : Checked d gamma a) (ha : isSentence.value ![a] = numeralValue M 1)
    (hctx : AxiomContext E gamma w) : Certified E (modelList [d, w]) a := by
  apply (certified_iff E _ a).mpr
  have hr : rootValue (modelList [d, w]) = d := by
    simpa only [rootValue, numeral_value_zero, List.getElem?_cons_zero, Option.getD_some] using
      modelList_entry_value (M := M) [d, w] 0
  have hw : witnessesValue (modelList [d, w]) = w := modelList_entry_value (M := M) [d, w] 1
  rw [hr, hw]
  refine ⟨modelList_length_value _, hd.1, hd.2.2, ha, ?_, ?_⟩
  · rw [show contextValue d = gamma from hd.2.1]
    exact hctx.1
  · change axiomListValue E (contextValue d) w = _
    rw [show contextValue d = gamma from hd.2.1]
    exact hctx.2

def baseRootValue (body p q : M) : M :=
  let gamma := listAppend.value ![contextValue (rootValue q), contextValue (rootValue p)]
  let z := modelNode 8 [zeroValue M]
  let a := upperValue 0 z (zeroValue M)
  let eq := modelNode 4 [z, ProofPrograms.numeral.value ![zeroValue M] ]
  let out := instantiate.value ![body, z]
  let ext := listCons.value ![a, gamma]
  let qinst := implication.value ![a, eq]
  let q1 := modelNode 113 [gamma, qinst, rootValue q, bodyValue (zeroValue M), z]
  let ass := modelNode 100 [ext, a]
  let eqProof := modelNode 108 [ext, eq, q1, ass]
  let transport := transportAlongEqualityValue ext eqProof (rootValue p) body z
    (ProofPrograms.numeral.value ![zeroValue M])
  let discharged := modelNode 107 [gamma, implication.value ![a, out], transport, a]
  let b := matrixValue body (zeroValue M)
  modelNode 115 [gamma, modelNode 7 [b], discharged, b, zeroValue M]

theorem initialSegment_zero_instance :
    instantiate.value ![bodyValue (zeroValue M), modelNode 8 [zeroValue M] ] =
      implication.value ![upperValue 0 (modelNode 8 [zeroValue M]) (zeroValue M),
        modelNode 4 [modelNode 8 [zeroValue M], ProofPrograms.numeral.value ![zeroValue M] ] ] := by
  rw [bodyValue_instantiate _ (bodyValue_namedForm _) aux_zero_namedTerm,
    segmentDisjunction_zero_value]

theorem checked_baseRoot (body p q : M)
    (hp : Checked (rootValue p) (contextValue (rootValue p))
      (instantiate.value ![body, ProofPrograms.numeral.value ![zeroValue M] ]))
    (hq : Checked (rootValue q) (contextValue (rootValue q))
      (modelNode 7 [bodyValue (zeroValue M)]))
    (hb : FormulaBound 1 body)
    (hinst : NamedFormulaBound 0 (instantiate.value ![body, modelNode 8 [zeroValue M] ]))
    (hbodyFresh : occursAux.value ![zeroValue M, body] = zeroValue M)
    (hfresh : contextFresh.value ![zeroValue M, listAppend.value
      ![contextValue (rootValue q), contextValue (rootValue p)] ] = numeralValue M 1) :
    Checked (baseRootValue body p q) (listAppend.value
      ![contextValue (rootValue q), contextValue (rootValue p)])
      (modelNode 7 [matrixValue body (zeroValue M)]) := by
  let gamma := listAppend.value ![contextValue (rootValue q), contextValue (rootValue p)]
  let z := modelNode 8 [zeroValue M]
  let a := upperValue 0 z (zeroValue M)
  let eq := modelNode 4 [z, ProofPrograms.numeral.value ![zeroValue M] ]
  let out := instantiate.value ![body, z]
  let ext := listCons.value ![a, gamma]
  have hgamma : formList.value ![zeroValue M, gamma] = numeralValue M 1 := by
    rw [show gamma = _ from rfl, formList_append_value,
      checked_context _ _ _ hq, checked_context _ _ _ hp, numeral_one_mul_model]
  have ha := upperValue_namedBound 0 z (zeroValue M) (NamedTermBound.aux 0 _)
  have heq : NamedFormulaBound 0 eq := NamedFormulaBound.equal (NamedTermBound.aux 0 _)
    (((PureTerm.numeral (zeroValue M)).termBound 0).named)
  have hext : formList.value ![zeroValue M, ext] = numeralValue M 1 :=
    (formList_cons_one_iff _ _ _).mpr ⟨namedForm_zero ha, hgamma⟩
  have hqi := checked_forallElimination_into (rootValue q) (contextValue (rootValue q)) gamma
    (bodyValue (zeroValue M)) z hq (contextIncluded_append_left_value _ _) (bodyValue_namedForm _)
    aux_zero_namedTerm (by
      rw [initialSegment_zero_instance, implication_node_value]
      exact namedForm_zero (ha.imp heq)) hgamma
  rw [initialSegment_zero_instance] at hqi
  have hass := checked_assumption ext a (namedForm_zero ha) hext
    ((listMember_cons_one_iff _ _ _).mpr (Or.inl rfl))
  have heqp := checked_modusPonens_into _ _ gamma ext ext a eq hqi hass
    (contextIncluded_under_cons gamma a) (contextIncluded_refl_value ext) (namedForm_zero heq) hext
  have hinc : contextIncluded.value ![contextValue (rootValue p), ext] = numeralValue M 1 :=
    contextIncluded_trans_value _ gamma ext (contextIncluded_append_right_value _ _)
      (contextIncluded_under_cons gamma a)
  have htransport := checked_transportAlongEquality ext (contextValue (rootValue p)) _ (rootValue p)
    body z (ProofPrograms.numeral.value ![zeroValue M]) heqp hp hinc (NamedTermBound.aux 0 _)
    (((PureTerm.numeral (zeroValue M)).termBound 0).named)
    (fun u => rewrite_slot_aux_name_value _ _ _) hb.namedForm
    (namedForm_zero hinst) hext
  have hout : namedForm.value ![zeroValue M, implication.value ![a, out] ] = numeralValue M 1 := by
    rw [implication_node_value]
    exact namedForm_zero (ha.imp hinst)
  have himp := checked_impIntro _ gamma a out htransport (namedForm_zero ha) hout hgamma
  have himp' : Checked
      (modelNode 107 [gamma, implication.value ![a, out],
        transportAlongEqualityValue ext
          (modelNode 108 [ext, eq,
            modelNode 113 [gamma, implication.value ![a, eq], rootValue q, bodyValue (zeroValue M), z],
            modelNode 100 [ext, a] ]) (rootValue p) body z
          (ProofPrograms.numeral.value ![zeroValue M]), a])
      gamma (instantiate.value ![matrixValue body (zeroValue M), z]) := by
    rw [matrix_instantiate body _ hb]
    exact himp
  exact checked_allIntro _ gamma (matrixValue body (zeroValue M)) (zeroValue M) himp'
    (matrix_namedForm body _ hb) (isSentence_namedForm _ (matrix_sentence body _ hb)) hgamma
    (matrix_occursAux_zero _ body _ hbodyFresh) hfresh

def baseFixedValue : M :=
  numeralValue M (fixedCertificate (initialSegmentSentence 0) initial_segment_zero_derives)

theorem baseFixed_certified : Certified axiomVerifier (baseFixedValue (M := M))
    (modelNode 7 [bodyValue (zeroValue M)]) := by
  have h := fixedProof_certified (initialSegmentSentence 0) initial_segment_zero_derives
    (M := M) (Fin.elim0 : Fin 0 → M)
  have hc : numeralValue M (CodingFormalProofs.sentenceCode CodingFormalProofs.arithmeticSignature
      (initialSegmentSentence 0)) = modelNode 7 [bodyValue (zeroValue M)] := by
    rw [← initialSegmentCode_numeral_value 0, numeral_value_zero, initialSegmentCode_model_value]
  simpa only [fixedProof, constant_value, baseFixedValue, hc] using h

theorem baseCertificate_model_value (p body : M) :
    baseCertificate.value ![p, body] =
      modelList [baseRootValue body p (baseFixedValue (M := M)), listAppend.value
        ![witnessesValue (baseFixedValue (M := M)), witnessesValue p] ] := by
  have hc : conclusionValue (rootValue (baseFixedValue (M := M))) =
      modelNode 7 [bodyValue (zeroValue M)] :=
    (certified_iff _ _ _).mp baseFixed_certified |>.2.2.1
  simp only [baseCertificate, certificateAt, FixedSyntaxPrograms.list_value,
    syntaxNode_model_value, List.map_cons, List.map_nil, root_program_value,
    context_program_value, conclusion_program_value, witnesses_program_value,
    impCode, binary_value, unary_value, upperAt_model_value, equalCode_value, matrix_model_value,
    allCode_value, value_comp_six, transportAlongEqualityRecord_model_value,
    fixedProof, constant_value, numeral_value_zero, Program.value_proj,
    Matrix.cons_val_zero, Matrix.cons_val_one, baseFixedValue, baseRootValue] at hc ⊢
  rw [hc, argument_modelNode_value]
  simp only [List.getElem?_cons_zero, Option.getD_some, initialSegment_zero_instance]

theorem certified_baseCertificate (p body : M)
    (hp : Certified axiomVerifier p
      (instantiate.value ![body, ProofPrograms.numeral.value ![zeroValue M] ]))
    (hb : FormulaBound 1 body)
    (hinst : NamedFormulaBound 0 (instantiate.value ![body, modelNode 8 [zeroValue M] ]))
    (hbodyFresh : occursAux.value ![zeroValue M, body] = zeroValue M) :
    Certified axiomVerifier (baseCertificate.value ![p, body])
      (modelNode 7 [matrixValue body (zeroValue M)]) := by
  let q := baseFixedValue (M := M)
  have hq : Certified axiomVerifier q (modelNode 7 [bodyValue (zeroValue M)]) := baseFixed_certified
  obtain ⟨_, hpd, hpc, _, _, _⟩ := (certified_iff _ _ _).mp hp
  obtain ⟨_, hqd, hqc, _, _, _⟩ := (certified_iff _ _ _).mp hq
  have hfresh : contextFresh.value ![zeroValue M, listAppend.value
      ![contextValue (rootValue q), contextValue (rootValue p)] ] = numeralValue M 1 := by
    rw [contextFresh_append_value, certified_contextFresh _ _ _ _ hq,
      certified_contextFresh _ _ _ _ hp, numeral_one_mul_model]
  have hd := checked_baseRoot body p q ⟨hpd, rfl, hpc⟩ ⟨hqd, rfl, hqc⟩ hb hinst hbodyFresh hfresh
  rw [baseCertificate_model_value]
  exact certified_from_axiomContext _ _ _ _ _ hd (matrix_sentence body _ hb)
    ((certified_axiomContext _ _ _ hq).append (certified_axiomContext _ _ _ hp))

end
end Lemmatheca.ProofTheory.PAComputations.ProofPrograms.CheckerPrograms.BoundedUniversalPrograms
