import Lemmatheca.BoundedArithmeticProofs.PAInitialSegmentFacts
import Lemmatheca.PaListsAndSyntax.PAModelSyntaxCorrectness

open Lemmatheca.MathematicalLogic Lemmatheca.ModelTheory Lemmatheca.ComputabilityTheory

namespace Lemmatheca.ProofTheory.PAComputations.ProofPrograms.InitialSegmentPrograms
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic ArithmeticTheories ArithmeticRepresentability FirstOrderProofs
open ArithmeticProofPredicates SyntaxPrograms CheckerPrograms FixedSyntaxPrograms
noncomputable section
universe u
variable {M : Type u} [language.Structure M] [M ⊨ PA]

theorem value_comp_seven {r : ℕ} (p : Program 7) (a b c d e f g : Program r) (x : Fin r → M) :
    (Program.comp p ![a, b, c, d, e, f, g]).value x =
      p.value ![a.value x, b.value x, c.value x, d.value x, e.value x, f.value x, g.value x] := by
  rw [Program.value_comp]
  congr 1
  funext i
  fin_cases i <;> rfl

def upperValue (offset : ℕ) (z n : M) : M :=
  modelFormulaCodeAt (Sum.elim (fun _ : Unit => z)
    (fun _ : Unit => ProofPrograms.numeral.value ![n])) offset upperFormula

def bodyValue (n : M) : M :=
  implication.value ![upperValue 1 (modelNode 1 [zeroValue M]) n,
    segmentDisjunction.value ![modelNode 1 [zeroValue M], n] ]

theorem upperAt_model_value {r : ℕ} (offset : ℕ) (z n : Program r) (x : Fin r → M) :
    (upperAt offset z n).value x = upperValue offset (z.value x) (n.value x) := by
  rw [upperAt, formulaCodeAt_model_value]
  congr 1
  funext i
  cases i with
  | inl i => rfl
  | inr i => simp only [Sum.elim_inr, unary_value]

theorem upperCode_model_value (n : M) :
    upperCode.value ![n] = upperValue 1 (modelNode 1 [zeroValue M]) n := by
  have h := upperAt_model_value 1 (syntaxNode 1 [constant 0]) (Program.proj 0) ![n]
  simpa only [upperAt, upperCode, syntaxNode_value, list_cons_value, list_nil_value, constant_value,
    numeral_value_zero, Program.value_proj, Matrix.cons_val_zero,
    modelNode, modelList_cons, modelList_nil] using h

theorem segmentBody_model_value {r : ℕ} (n : Program r) (x : Fin r → M) :
    (segmentBody n).value x = bodyValue (n.value x) := by
  simp only [segmentBody, impCode, binary_value, upperAt_model_value, syntaxNode_value,
    list_cons_value, list_nil_value, constant_value, numeral_value_zero,
    modelNode, modelList_cons, modelList_nil, bodyValue]

theorem initialSegmentCode_model_value (n : M) :
    initialSegmentCode.value ![n] = modelNode 7 [bodyValue n] := by
  simp only [initialSegmentCode, allCode_value, impCode, binary_value,
    upperCode_model_value, syntaxNode_value, list_cons_value, list_nil_value,
    constant_value, numeral_value_zero, Program.value_proj, Matrix.cons_val_zero,
    modelNode, modelList_cons, modelList_nil, bodyValue]

def stepCertificateValue (n p q : M) : M :=
  let gamma := listAppend.value ![contextValue (rootValue p), contextValue (rootValue q)]
  let z := modelNode 8 [zeroValue M]
  let a := upperValue 0 z (succValue M n)
  let b := upperValue 0 z n
  let d := segmentDisjunction.value ![z, n]
  let c := modelNode 4 [z, ProofPrograms.numeral.value ![succValue M n] ]
  let qbody := (argument 0).value ![conclusionValue (rootValue q)]
  let qfirst := instantiate.value ![qbody, ProofPrograms.numeral.value ![n] ]
  let q1 := modelNode 113 [gamma, qfirst, rootValue q, qbody, ProofPrograms.numeral.value ![n] ]
  let qinner := (argument 0).value ![qfirst]
  let qsecond := instantiate.value ![qinner, z]
  let q2 := modelNode 113 [gamma, qsecond, q1, qinner, z]
  let pbody := (argument 0).value ![conclusionValue (rootValue p)]
  let pinst := instantiate.value ![pbody, z]
  let p1 := modelNode 113 [gamma, pinst, rootValue p, pbody, z]
  let discharged := finiteCasesValue gamma a b c d q2 p1
  let body := bodyValue (succValue M n)
  let result := modelNode 115 [gamma, modelNode 7 [body], discharged, body, zeroValue M]
  modelList [result, listAppend.value ![witnessesValue p, witnessesValue q] ]

theorem initialSegmentStep_model_value (n p : M) :
    initialSegmentStep.value ![n, p] = stepCertificateValue n p
      (numeralValue M (fixedCertificate stepSentence step_sentence_derives)) := by
  simp only [initialSegmentStep, certificateAt, list_cons_value, list_nil_value,
    syntaxNode_value, allCode_value, segmentBody_model_value, upperAt_model_value,
    root, context, conclusion, witnesses, binary_value, unary_value,
    value_comp_seven, finiteCasesRecord_model_value, equalCode_value,
    fixedProof, constant_value, numeral_value_zero, Program.value_proj, Program.value_succ,
    Matrix.cons_val_zero, Matrix.cons_val_one, rootValue, contextValue,
    conclusionValue, witnessesValue, stepCertificateValue, modelNode, modelList_cons, modelList_nil]

theorem numeral_le_model (m n : ℕ) (hmn : m ≤ n) :
    leValue M (numeralValue M m) (numeralValue M n) := by
  let := PA_models_Q M
  exact (finite_bound _ n).mpr ⟨m, hmn, rfl⟩

theorem bound_zero_stats : stats.value ![modelNode 1 [zeroValue M] ] =
    modelSummary (numeralValue M 2) (zeroValue M) (zeroValue M) (zeroValue M) := by
  rw [stats_bound_modelNode_value, zero_add_value]

theorem aux_zero_stats : stats.value ![modelNode 8 [zeroValue M] ] =
    modelSummary (numeralValue M 1) (zeroValue M) (zeroValue M) (numeralValue M 1) := by
  rw [stats_aux_modelNode_value, zero_add_value]

theorem segment_bound_formula (n : M) :
    FormulaBound 1 (segmentDisjunction.value ![modelNode 1 [zeroValue M], n]) :=
  ⟨numeralValue M 2, numeral_le_model 1 2 (by decide), le_refl_value _,
    segmentDisjunction_stats _ _ _ bound_zero_stats (numeral_le_model 1 2 (by decide)) n⟩

theorem segment_aux_formula (n : M) :
    NamedFormulaBound 0 (segmentDisjunction.value ![modelNode 8 [zeroValue M], n]) :=
  ⟨numeralValue M 1, numeralValue M 1, le_refl_value _, le_refl_value _,
    segmentDisjunction_stats _ _ _ aux_zero_stats (le_refl_value _) n⟩

theorem upperValue_namedBound (offset : ℕ) (z n : M)
    (hz : NamedTermBound offset z) : NamedFormulaBound offset (upperValue offset z n) := by
  change NamedFormulaBound (offset + 0) (modelFormulaCodeAt
    (Sum.elim (fun _ : Unit => z) (fun _ : Unit => ProofPrograms.numeral.value ![n])) offset upperFormula)
  apply modelFormulaCodeAt_namedBound _ offset _ upperFormula
  intro i
  cases i with
  | inl i => exact hz
  | inr i => exact ((PureTerm.numeral n).termBound offset).named

theorem upperValue_rewrite (offset : ℕ) (i t z n : M) :
    rewrite.value ![numeralValue M 2, i, t, upperValue (offset + 1) z n] =
      upperValue offset (rewrite.value ![numeralValue M 2, i, t, z]) n := by
  rw [upperValue, rewrite_slot_modelFormulaCodeAt]
  congr 1
  funext j
  cases j with
  | inl j => rfl
  | inr j => exact rewrite_slot_numeral_value i t n

theorem bodyValue_rewrite (n t : M) :
    rewrite.value ![numeralValue M 2, zeroValue M, t, bodyValue n] =
      implication.value ![upperValue 0 t n, segmentDisjunction.value ![t, n] ] := by
  simp only [bodyValue, implication_node_value]
  rw [rewrite_slot_imp_value, upperValue_rewrite 0, segmentDisjunction_rewrite,
    rewrite_slot_bound_zero_value]

theorem bodyValue_instantiate (n : M)
    (hb : namedForm.value ![numeralValue M 1, bodyValue n] = numeralValue M 1)
    (ht : namedTerm.value ![modelNode 8 [zeroValue M] ] = numeralValue M 1) :
    instantiate.value ![bodyValue n, modelNode 8 [zeroValue M] ] =
      implication.value ![upperValue 0 (modelNode 8 [zeroValue M]) n,
        segmentDisjunction.value ![modelNode 8 [zeroValue M], n] ] := by
  rw [instantiate_value_of_tests _ _ hb ht, bodyValue_rewrite]

theorem aux_zero_namedTerm : namedTerm.value ![modelNode 8 [zeroValue M] ] = numeralValue M 1 :=
  namedTerm_of_stats _ _ aux_zero_stats

theorem bound_zero_termBound : TermBound 1 (modelNode 1 [zeroValue M]) := by
  simpa only [Fin.val_zero, numeral_value_zero] using (TermBound.bound (M := M) 1 (0 : Fin 1))

theorem upperValue_bound (offset : ℕ) (z n : M)
    (hz : TermBound offset z) : FormulaBound offset (upperValue offset z n) := by
  change FormulaBound (offset + 0) (modelFormulaCodeAt
    (Sum.elim (fun _ : Unit => z) (fun _ : Unit => ProofPrograms.numeral.value ![n])) offset upperFormula)
  apply modelFormulaCodeAt_bound _ offset _ upperFormula
  intro i
  cases i with
  | inl i => exact hz
  | inr i => exact (PureTerm.numeral n).termBound offset

theorem bodyValue_bound (n : M) : FormulaBound 1 (bodyValue n) := by
  rw [bodyValue, implication_node_value]
  exact FormulaBound.imp (upperValue_bound 1 _ n bound_zero_termBound) (segment_bound_formula n)

theorem bodyValue_namedForm (n : M) :
    namedForm.value ![numeralValue M 1, bodyValue n] = numeralValue M 1 :=
  (bodyValue_bound n).namedForm

theorem segmentCode_sentence (n : M) :
    isSentence.value ![modelNode 7 [bodyValue n] ] = numeralValue M 1 :=
  isSentence_of_stats _ ((FormulaBound.all (bodyValue_bound n)).pure)

theorem upperValue_occursAux_zero (offset : ℕ) (j z n : M)
    (hz : occursAux.value ![j, z] = zeroValue M) :
    occursAux.value ![j, upperValue offset z n] = zeroValue M := by
  apply modelFormulaCodeAt_occursAux_zero
  intro i
  cases i with
  | inl i => exact hz
  | inr i => exact numeral_occursAux_zero j n

theorem bodyValue_occursAux_zero (j n : M) :
    occursAux.value ![j, bodyValue n] = zeroValue M := by
  rw [bodyValue, implication_node_value]
  apply occursAux_modelNode_zero j 6 _ (by decide)
  intro x hx
  simp only [Nat.reduceEqDiff, or_self, ↓reduceIte, List.mem_cons, List.not_mem_nil,
    or_false] at hx
  rcases hx with rfl | rfl
  · exact upperValue_occursAux_zero 1 j _ n
      (occursAux_original_leaf_zero j 1 _ (Or.inr rfl))
  · exact segmentDisjunction_occursAux_zero j _
      (occursAux_original_leaf_zero j 1 _ (Or.inr rfl)) n

theorem allClose_model_code (A : language.Formula Unit) :
    numeralValue M (CodingFormalProofs.sentenceCode CodingFormalProofs.arithmeticSignature (allClose A)) =
      modelNode 7 [modelFormulaCodeAt (fun _ : Unit => modelNode 1 [zeroValue M]) 1 A] := by
  rw [unit_closure_code]
  change numeralValue M (CodingFormalProofs.node 7 [_]) = _
  rw [← modelNode_numerals]
  simp only [List.map_cons, List.map_nil]
  congr 2
  have h := modelFormulaCodeAt_numerals (M := M)
    (fun _ : Unit => CodingFormalProofs.boundName 0) 1 A
  have hn : (fun _ : Unit => numeralValue M (CodingFormalProofs.boundName 0)) =
      (fun _ : Unit => modelNode 1 [zeroValue M]) := by
    funext i
    rw [CodingFormalProofs.boundName, ← modelNode_numerals]
    simp only [List.map_cons, List.map_nil, numeral_value_zero]
  rw [hn] at h
  exact h.symm

def stepOuterBodyValue : M :=
  modelFormulaCodeAt (fun _ : Unit => modelNode 1 [zeroValue M]) 1 (stepBody.iAlls Unit)

def stepFirstValue (n : M) : M :=
  modelFormulaCodeAt (fun _ : Unit => ProofPrograms.numeral.value ![n]) 0 (stepBody.iAlls Unit)

def stepInnerBodyValue (n : M) : M :=
  modelFormulaCodeAt (Sum.elim (fun _ : Unit => ProofPrograms.numeral.value ![n])
    (fun _ : Unit => modelNode 1 [zeroValue M])) 1 stepBody

def stepSecondValue (n : M) : M :=
  modelFormulaCodeAt (Sum.elim (fun _ : Unit => ProofPrograms.numeral.value ![n])
    (fun _ : Unit => modelNode 8 [zeroValue M])) 0 stepBody

theorem stepSentence_model_code :
    numeralValue M (CodingFormalProofs.sentenceCode CodingFormalProofs.arithmeticSignature stepSentence) =
      modelNode 7 [stepOuterBodyValue (M := M)] :=
  allClose_model_code (stepBody.iAlls Unit)

theorem stepOuterBody_namedForm :
    namedForm.value ![numeralValue M 1, stepOuterBodyValue (M := M)] = numeralValue M 1 := by
  exact modelFormulaCodeAt_namedForm _ 1 (fun _ => bound_zero_termBound.named) (stepBody.iAlls Unit)

theorem stepFirst_namedForm (n : M) :
    namedForm.value ![zeroValue M, stepFirstValue n] = numeralValue M 1 := by
  simpa only [stepFirstValue, Nat.add_zero, numeral_value_zero] using
    modelFormulaCodeAt_namedForm _ 0
      (fun _ => ((PureTerm.numeral n).termBound 0).named) (stepBody.iAlls Unit)

theorem stepInnerBody_namedForm (n : M) :
    namedForm.value ![numeralValue M 1, stepInnerBodyValue n] = numeralValue M 1 := by
  apply modelFormulaCodeAt_namedForm _ 1 _ stepBody
  intro i
  cases i with
  | inl i => exact ((PureTerm.numeral n).termBound 1).named
  | inr i => exact bound_zero_termBound.named

theorem stepSecond_namedForm (n : M) :
    namedForm.value ![zeroValue M, stepSecondValue n] = numeralValue M 1 := by
  have hn : ∀ i : Unit ⊕ Unit, NamedTermBound 0
      (Sum.elim (fun _ => ProofPrograms.numeral.value ![n])
        (fun _ => modelNode 8 [zeroValue M]) i) := by
    intro i
    cases i with
    | inl i => exact ((PureTerm.numeral n).termBound 0).named
    | inr i => exact NamedTermBound.aux 0 _
  simpa only [stepSecondValue, Nat.add_zero, numeral_value_zero] using modelFormulaCodeAt_namedForm _ 0 hn stepBody

theorem stepOuterBody_instantiate (n : M) :
    instantiate.value ![stepOuterBodyValue, ProofPrograms.numeral.value ![n] ] =
      stepFirstValue n := by
  rw [instantiate_value_of_tests _ _ stepOuterBody_namedForm (numeral_namedTerm n)]
  rw [stepOuterBodyValue, rewrite_slot_modelFormulaCodeAt]
  congr 1
  funext i
  exact rewrite_slot_bound_zero_value _ _

theorem stepFirst_all (n : M) : stepFirstValue n = modelNode 7 [stepInnerBodyValue n] := by
  rw [stepFirstValue, modelFormulaCodeAt_iAlls_unit]
  simp only [numeral_value_zero]
  rfl

theorem stepInnerBody_instantiate (n : M) :
    instantiate.value ![stepInnerBodyValue n, modelNode 8 [zeroValue M] ] =
      stepSecondValue n := by
  rw [instantiate_value_of_tests _ _ (stepInnerBody_namedForm n) aux_zero_namedTerm]
  rw [stepInnerBodyValue, rewrite_slot_modelFormulaCodeAt]
  congr 1
  funext i
  cases i with
  | inl i => exact rewrite_slot_numeral_value _ _ n
  | inr i => exact rewrite_slot_bound_zero_value _ _

theorem model_leFormula_value {α : Type*} (name : α → M) (offset : ℕ)
    (s t : language.Term α) :
    modelFormulaCodeAt name offset (leFormula s t) =
      modelFormulaCodeAt (Sum.elim (fun _ : Unit => modelTermCode name s)
        (fun _ : Unit => modelTermCode name t)) offset upperFormula := by
  let sub : Unit ⊕ Unit → language.Term α := Sum.elim (fun _ => s) (fun _ => t)
  have hs : upperFormula.subst sub = leFormula s t := by
    simp only [upperFormula, ArithmeticRepresentability.subst_leFormula, Term.subst,
      sub, Sum.elim_inl, Sum.elim_inr]
  rw [← hs, modelFormulaCodeAt_subst]
  congr 1
  funext i
  cases i <;> rfl

theorem stepSecond_implication (n : M) : stepSecondValue n =
    implication.value ![upperValue 0 (modelNode 8 [zeroValue M]) (succValue M n),
      orValue (upperValue 0 (modelNode 8 [zeroValue M]) n)
        (modelNode 4 [modelNode 8 [zeroValue M], ProofPrograms.numeral.value ![succValue M n] ])] := by
  unfold stepSecondValue stepBody
  change modelNode 6 [modelFormulaCodeAt _ 0 (leFormula _ _),
    modelNode 6 [modelNode 6 [modelFormulaCodeAt _ 0 (leFormula _ _), modelNode 3 [] ],
      modelNode 4 [_, _] ] ] = _
  rw [model_leFormula_value, model_leFormula_value]
  simp only [succTerm, modelTermCode_relabel, modelTermCode, Sum.elim_inl, Sum.elim_inr,
    Function.comp_def, CodingFormalProofs.arithFunctionCode, List.ofFn_succ, List.ofFn_zero]
  simp only [← numeral_successor_modelNode_value]
  simp only [upperValue, orValue, negValue, implication_node_value]

theorem named_or_bound {k : ℕ} {a b : M}
    (ha : NamedFormulaBound k a) (hb : NamedFormulaBound k b) :
    NamedFormulaBound k (orValue a b) := by
  simp only [orValue, negValue, implication_node_value]
  exact NamedFormulaBound.imp (NamedFormulaBound.imp ha (NamedFormulaBound.bottom k)) hb

theorem namedForm_zero {a : M} (ha : NamedFormulaBound 0 a) :
    namedForm.value ![zeroValue M, a] = numeralValue M 1 := by
  simpa only [numeral_value_zero] using ha.namedForm

def stepRootValue (n p q : M) : M :=
  let gamma := listAppend.value ![contextValue (rootValue p), contextValue (rootValue q)]
  let z := modelNode 8 [zeroValue M]
  let a := upperValue 0 z (succValue M n)
  let b := upperValue 0 z n
  let d := segmentDisjunction.value ![z, n]
  let c := modelNode 4 [z, ProofPrograms.numeral.value ![succValue M n] ]
  let q1 := modelNode 113 [gamma, stepFirstValue n, rootValue q,
    stepOuterBodyValue, ProofPrograms.numeral.value ![n] ]
  let q2 := modelNode 113 [gamma, stepSecondValue n, q1, stepInnerBodyValue n, z]
  let p1 := modelNode 113 [gamma, implication.value ![b, d], rootValue p, bodyValue n, z]
  let discharged := finiteCasesValue gamma a b c d q2 p1
  let body := bodyValue (succValue M n)
  modelNode 115 [gamma, modelNode 7 [body], discharged, body, zeroValue M]

theorem stepCertificateValue_known (n p q : M)
    (hp : conclusionValue (rootValue p) = modelNode 7 [bodyValue n])
    (hq : conclusionValue (rootValue q) = modelNode 7 [stepOuterBodyValue]) :
    stepCertificateValue n p q =
      modelList [stepRootValue n p q, listAppend.value ![witnessesValue p, witnessesValue q] ] := by
  dsimp only [stepCertificateValue]
  rw [hp, hq, argument_modelNode_value, argument_modelNode_value]
  simp only [List.getElem?_cons_zero, Option.getD_some]
  rw [stepOuterBody_instantiate]
  have harg : (argument 0).value ![stepFirstValue n] = stepInnerBodyValue n := by
    rw [stepFirst_all, argument_modelNode_value]
    rfl
  rw [harg, stepInnerBody_instantiate, bodyValue_instantiate n (bodyValue_namedForm n) aux_zero_namedTerm]
  rfl

theorem checked_stepRoot (n p q : M)
    (hp : Checked (rootValue p) (contextValue (rootValue p)) (modelNode 7 [bodyValue n]))
    (hq : Checked (rootValue q) (contextValue (rootValue q)) (modelNode 7 [stepOuterBodyValue]))
    (hfresh : contextFresh.value ![zeroValue M, listAppend.value
      ![contextValue (rootValue p), contextValue (rootValue q)] ] = numeralValue M 1) :
    Checked (stepRootValue n p q) (listAppend.value
      ![contextValue (rootValue p), contextValue (rootValue q)])
      (modelNode 7 [bodyValue (succValue M n)]) := by
  let gamma := listAppend.value ![contextValue (rootValue p), contextValue (rootValue q)]
  let z := modelNode 8 [zeroValue M]
  let a := upperValue 0 z (succValue M n)
  let b := upperValue 0 z n
  let d := segmentDisjunction.value ![z, n]
  let c := modelNode 4 [z, ProofPrograms.numeral.value ![succValue M n] ]
  have hgamma : formList.value ![zeroValue M, gamma] = numeralValue M 1 := by
    rw [show gamma = _ from rfl, formList_append_value,
      checked_context _ _ _ hp, checked_context _ _ _ hq, numeral_one_mul_model]
  have hq1 := checked_forallElimination_into (rootValue q) (contextValue (rootValue q)) gamma
    stepOuterBodyValue (ProofPrograms.numeral.value ![n]) hq
    (contextIncluded_append_right_value _ _) stepOuterBody_namedForm
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
  have hp1 := checked_forallElimination_into (rootValue p) (contextValue (rootValue p)) gamma
    (bodyValue n) z hp (contextIncluded_append_left_value _ _) (bodyValue_namedForm n) aux_zero_namedTerm
    (by
      rw [bodyValue_instantiate n (bodyValue_namedForm n) aux_zero_namedTerm, implication_node_value]
      exact namedForm_zero (NamedFormulaBound.imp
        (upperValue_namedBound 0 z n (NamedTermBound.aux 0 _)) (segment_aux_formula n)))
    hgamma
  rw [bodyValue_instantiate n (bodyValue_namedForm n) aux_zero_namedTerm] at hp1
  have ha := upperValue_namedBound 0 z (succValue M n) (NamedTermBound.aux 0 _)
  have hb := upperValue_namedBound 0 z n (NamedTermBound.aux 0 _)
  have hc : NamedFormulaBound 0 c := NamedFormulaBound.equal (NamedTermBound.aux 0 _)
    (((PureTerm.numeral (succValue M n)).termBound 0).named)
  have hd := segment_aux_formula n
  have hbc := named_or_bound hb hc
  have hdc := named_or_bound hd hc
  have hout : namedForm.value ![zeroValue M, implication.value ![a, orValue d c] ] = numeralValue M 1 := by
    rw [implication_node_value]
    exact namedForm_zero (NamedFormulaBound.imp ha hdc)
  rw [stepSecond_implication] at hq2
  have hcases := checked_finiteCases gamma a b c d _ _ hq2 hp1
    (namedForm_zero ha) (namedForm_zero hb) (namedForm_zero hc) (namedForm_zero hd)
    (namedForm_zero hbc) (namedForm_zero hdc) hout hgamma
  have hinst : instantiate.value ![bodyValue (succValue M n), z] =
      implication.value ![a, orValue d c] := by
    rw [bodyValue_instantiate _ (bodyValue_namedForm _) aux_zero_namedTerm,
      segmentDisjunction_successor_value]
  have hcases' := hcases
  rw [← hinst] at hcases'
  simpa only [stepRootValue, stepSecond_implication] using
    checked_allIntro _ gamma (bodyValue (succValue M n)) (zeroValue M) hcases'
    (bodyValue_namedForm _) (isSentence_namedForm _ (segmentCode_sentence _))
    hgamma (bodyValue_occursAux_zero _ _) hfresh

theorem stepRoot_context (n p q : M) : contextValue (stepRootValue n p q) =
    listAppend.value ![contextValue (rootValue p), contextValue (rootValue q)] := by
  unfold contextValue stepRootValue
  rw [argument_modelNode_value]
  rfl

theorem fixedStep_certified :
    Certified axiomVerifier
      (numeralValue M (fixedCertificate stepSentence step_sentence_derives))
      (modelNode 7 [stepOuterBodyValue (M := M)]) := by
  have h := fixedProof_certified stepSentence step_sentence_derives (M := M) (Fin.elim0 : Fin 0 → M)
  simpa only [fixedProof, constant_value, stepSentence_model_code] using h

theorem fixedStep_fresh : contextFresh.value ![zeroValue M, contextValue (rootValue
    (numeralValue M (fixedCertificate stepSentence step_sentence_derives)))] = numeralValue M 1 := by
  have h := fixedProof_context_fresh stepSentence step_sentence_derives (zeroValue M)
    (Fin.elim0 : Fin 0 → M)
  simpa only [fixedProof, constant_value] using h

theorem initialSegmentStep_certified (n p : M)
    (hp : Certified axiomVerifier p (initialSegmentCode.value ![n]))
    (hf : contextFresh.value ![zeroValue M, contextValue (rootValue p)] = numeralValue M 1) :
    Certified axiomVerifier (initialSegmentStep.value ![n, p])
      (initialSegmentCode.value ![succValue M n]) ∧
    contextFresh.value ![zeroValue M,
      contextValue (rootValue (initialSegmentStep.value ![n, p]))] = numeralValue M 1 := by
  let q := numeralValue M (fixedCertificate stepSentence step_sentence_derives)
  have hq : Certified axiomVerifier q (modelNode 7 [stepOuterBodyValue]) := fixedStep_certified
  obtain ⟨_, hpd, hpc, _, _, _⟩ := (certified_iff _ _ _).mp hp
  obtain ⟨_, hqd, hqc, _, _, _⟩ := (certified_iff _ _ _).mp hq
  rw [initialSegmentCode_model_value] at hpc
  have hgamma : contextFresh.value ![zeroValue M, listAppend.value
      ![contextValue (rootValue p), contextValue (rootValue q)] ] = numeralValue M 1 := by
    rw [contextFresh_append_value, hf, show contextFresh.value
      ![zeroValue M, contextValue (rootValue q)] = numeralValue M 1 from fixedStep_fresh,
      numeral_one_mul_model]
  have hd := checked_stepRoot n p q ⟨hpd, rfl, hpc⟩ ⟨hqd, rfl, hqc⟩ hgamma
  have hvalue : initialSegmentStep.value ![n, p] =
      modelList [stepRootValue n p q, listAppend.value ![witnessesValue p, witnessesValue q] ] := by
    rw [initialSegmentStep_model_value, stepCertificateValue_known n p q hpc hqc]
  constructor
  · rw [hvalue, initialSegmentCode_model_value]
    exact certified_merge_contexts axiomVerifier p q _ _ _ _ hp hq hd (segmentCode_sentence _)
  · rw [hvalue]
    have hroot : rootValue
        (modelList [stepRootValue n p q, listAppend.value ![witnessesValue p, witnessesValue q] ]) =
        stepRootValue n p q := by
      simpa only [rootValue, numeral_value_zero, List.getElem?_cons_zero, Option.getD_some] using
        modelList_entry_value (M := M)
          [stepRootValue n p q, listAppend.value ![witnessesValue p, witnessesValue q] ] 0
    rw [hroot, stepRoot_context]
    exact hgamma

theorem initialSegmentProof_zero_value :
    initialSegmentProof.value ![zeroValue M] =
      (fixedProof (initialSegmentSentence 0) initial_segment_zero_derives : Program 0).value Fin.elim0 := by
  have h := Program.value_rec_zero
    (fixedProof (initialSegmentSentence 0) initial_segment_zero_derives : Program 0)
    initialSegmentStep (Fin.elim0 : Fin 0 → M)
  have hv : Fin.snoc (Fin.elim0 : Fin 0 → M) (zeroValue M) = ![zeroValue M] := by
    funext i
    fin_cases i
    rfl
  simpa only [initialSegmentProof, hv] using h

theorem initialSegmentProof_successor_value (n : M) :
    initialSegmentProof.value ![succValue M n] =
      initialSegmentStep.value ![n, initialSegmentProof.value ![n] ] := by
  have h := Program.value_rec_succ
    (fixedProof (initialSegmentSentence 0) initial_segment_zero_derives : Program 0)
    initialSegmentStep (Fin.elim0 : Fin 0 → M) n
  have hv (a : M) : Fin.snoc (Fin.elim0 : Fin 0 → M) a = ![a] := by
    funext i
    fin_cases i
    rfl
  have hv2 (a b : M) : Fin.snoc (![a] : Fin 1 → M) b = ![a, b] := by
    funext i
    fin_cases i <;> rfl
  simpa only [initialSegmentProof, hv, hv2] using h

theorem initialSegmentCode_numeral_value (n : ℕ) :
    initialSegmentCode.value ![numeralValue M n] =
      numeralValue M (CodingFormalProofs.sentenceCode CodingFormalProofs.arithmeticSignature
        (initialSegmentSentence n)) := by
  have h := initialSegmentCode.value_numerals (M := M) ![n]
  have hv : (fun i : Fin 1 => numeralValue M (![n] i)) = ![numeralValue M n] := by
    funext i
    fin_cases i
    rfl
  rw [hv, initialSegmentCode_eval] at h
  exact h

/-- The one concrete primitive-recursive builder is accepted uniformly even
at nonstandard input indices. The proof is PA induction on its actual checker
acceptance and auxiliary-name freshness invariants. -/
theorem initialSegmentProof_certified_and_fresh (n : M) :
    Certified axiomVerifier (initialSegmentProof.value ![n]) (initialSegmentCode.value ![n]) ∧
    contextFresh.value ![zeroValue M,
      contextValue (rootValue (initialSegmentProof.value ![n]))] = numeralValue M 1 := by
  have h : ∀ n : M,
      Certified axiomVerifier (initialSegmentProof.value ![n]) (initialSegmentCode.value ![n]) ∧
      contextFresh.value ![zeroValue M,
        contextValue (rootValue (initialSegmentProof.value ![n]))] = numeralValue M 1 := by
    apply definable_induction
    · change DPred (fun v : Fin 1 → M =>
        Certified axiomVerifier (initialSegmentProof.value ![v 0]) (initialSegmentCode.value ![v 0]) ∧
        contextFresh.value ![zeroValue M,
          contextValue (rootValue (initialSegmentProof.value ![v 0]))] = numeralValue M 1)
      unfold Certified contextValue rootValue
      pa_definable
    · rw [initialSegmentProof_zero_value, ← numeral_value_zero M,
        initialSegmentCode_numeral_value]
      exact ⟨fixedProof_certified _ _ (Fin.elim0 : Fin 0 → M),
        fixedProof_context_fresh _ _ (numeralValue M 0) (Fin.elim0 : Fin 0 → M)⟩
    · intro k hk
      rw [initialSegmentProof_successor_value]
      exact initialSegmentStep_certified k _ hk.1 hk.2
  exact h n

theorem initialSegmentProof_certified (n : M) :
    Certified axiomVerifier (initialSegmentProof.value ![n]) (initialSegmentCode.value ![n]) :=
  (initialSegmentProof_certified_and_fresh n).1

theorem initialSegmentProof_context_fresh (n : M) :
    contextFresh.value ![zeroValue M,
      contextValue (rootValue (initialSegmentProof.value ![n]))] = numeralValue M 1 :=
  (initialSegmentProof_certified_and_fresh n).2

theorem initialSegmentCode_eval_inputs (x : Fin 1 → ℕ) :
    initialSegmentCode.eval x =
      CodingFormalProofs.sentenceCode CodingFormalProofs.arithmeticSignature
        (initialSegmentSentence (x 0)) := by
  have hx : x = ![x 0] := by
    funext i
    fin_cases i
    rfl
  rw [hx]
  exact initialSegmentCode_eval _

end
end Lemmatheca.ProofTheory.PAComputations.ProofPrograms.InitialSegmentPrograms
