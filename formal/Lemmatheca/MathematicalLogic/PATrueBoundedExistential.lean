import Lemmatheca.MathematicalLogic.PAFalseBoundedUniversal

/-! A bounded existential certificate from its accepted numerical bound and
accepted matrix instance. -/
namespace Lemmatheca.MathematicalLogic.PAComputations.ProofPrograms.CheckerPrograms.BoundedCounterexamplePrograms
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic ArithmeticTheories ArithmeticRepresentability
open SyntaxPrograms FixedSyntaxPrograms InitialSegmentPrograms BoundedUniversalPrograms LogicalProofs
noncomputable section
universe u

def existentialMatrix {r : ℕ} (body n : Program r) : Program r :=
  andCode (upperAt 1 (syntaxNode 1 [constant 0]) n) body

/-- Inputs: upper-bound certificate, positive-instance certificate, one-slot
body, witness, bound. -/
def existentialInstanceCertificate : Program 5 :=
  let p : Program 5 := .proj 0
  let q : Program 5 := .proj 1
  let body : Program 5 := .proj 2
  let i : Program 5 := .proj 3
  let n : Program 5 := .proj 4
  let term := unary ProofPrograms.numeral i
  let gamma := binary listAppend (context (root p)) (context (root q))
  let upper := upperAt 0 term n
  let out := binary instantiate body term
  let joint := syntaxNode 101 [gamma, andCode upper out, root p, root q]
  let m := existentialMatrix body n
  certificateAt (syntaxNode 114 [gamma, exCode m, joint, m, term])
    (binary listAppend (witnesses p) (witnesses q))

variable {M : Type u} [language.Structure M] [M ⊨ PA]

def existentialMatrixValue (body n : M) : M :=
  andValue (upperValue 1 (modelNode 1 [zeroValue M]) n) body

def existentialInstanceRecordValue (p q body i n : M) : M :=
  let term := ProofPrograms.numeral.value ![i]
  let gamma := listAppend.value ![contextValue (rootValue p), contextValue (rootValue q)]
  let upper := upperValue 0 term n
  let out := instantiate.value ![body, term]
  let joint := modelNode 101 [gamma, andValue upper out, rootValue p, rootValue q]
  let m := existentialMatrixValue body n
  modelNode 114 [gamma, exValue m, joint, m, term]

theorem existentialMatrix_value {r : ℕ} (body n : Program r) (x : Fin r → M) :
    (existentialMatrix body n).value x = existentialMatrixValue (body.value x) (n.value x) := by
  simp only [existentialMatrix, andCode_value, upperAt_model_value, syntaxNode_model_value,
    List.map_cons, List.map_nil, constant_value, numeral_value_zero, existentialMatrixValue]

theorem existentialInstanceCertificate_value (p q body i n : M) :
    existentialInstanceCertificate.value ![p, q, body, i, n] =
      modelList [existentialInstanceRecordValue p q body i n,
        listAppend.value ![witnessesValue p, witnessesValue q] ] := by
  simp only [existentialInstanceCertificate, certificateAt, FixedSyntaxPrograms.list_value,
    syntaxNode_model_value, List.map_cons, List.map_nil, binary_value, unary_value,
    root_program_value, context_program_value, witnesses_program_value,
    existentialMatrix_value, upperAt_model_value, andCode_value, exCode_value,
    Program.value_proj, modelList_cons, modelList_nil,
    existentialInstanceRecordValue, modelNode]
  rfl

private theorem conjunction_bound {k : ℕ} {a b : M}
    (ha : FormulaBound k a) (hb : FormulaBound k b) : FormulaBound k (andValue a b) := by
  simp only [andValue, negValue, implication_node_value]
  exact (ha.imp (hb.imp (FormulaBound.bottom k))).imp (FormulaBound.bottom k)

private theorem pure_conjunction {a b : M} (ha : PureFormula a) (hb : PureFormula b) :
    PureFormula (andValue a b) := (conjunction_bound (ha.formulaBound 0) (hb.formulaBound 0)).pure

theorem existentialMatrix_bound (body n : M) (hb : FormulaBound 1 body) :
    FormulaBound 1 (existentialMatrixValue body n) :=
  conjunction_bound (upperValue_bound 1 _ n bound_zero_termBound) hb

private theorem rewrite_slot_conjunction (i t a b : M) :
    rewrite.value ![numeralValue M 2, i, t, andValue a b] =
      andValue (rewrite.value ![numeralValue M 2, i, t, a])
        (rewrite.value ![numeralValue M 2, i, t, b]) := by
  simp only [andValue, negValue, implication_node_value]
  rw [rewrite_slot_imp_value, rewrite_slot_imp_value, rewrite_slot_imp_value,
    rewrite_slot_nonleaf_value 3 (by decide) (by decide) (by decide)]
  rfl

theorem existentialMatrix_instantiate_numeral (body i n : M) (hb : FormulaBound 1 body) :
    instantiate.value ![existentialMatrixValue body n, ProofPrograms.numeral.value ![i] ] =
      andValue (upperValue 0 (ProofPrograms.numeral.value ![i]) n)
        (instantiate.value ![body, ProofPrograms.numeral.value ![i] ]) := by
  rw [instantiate_value_of_tests _ _ (existentialMatrix_bound body n hb).namedForm
    (PureTerm.numeral i).namedTerm]
  rw [existentialMatrixValue, rewrite_slot_conjunction, upperValue_rewrite 0,
    rewrite_slot_bound_zero_value,
    ← instantiate_value_of_tests _ _ hb.namedForm (PureTerm.numeral i).namedTerm]

theorem checked_conjunction_into (d e gamma delta target a b : M)
    (hd : Checked d gamma a) (he : Checked e delta b)
    (hincD : contextIncluded.value ![gamma, target] = numeralValue M 1)
    (hincE : contextIncluded.value ![delta, target] = numeralValue M 1)
    (ha : PureFormula a) (hb : PureFormula b)
    (hcontext : formList.value ![zeroValue M, target] = numeralValue M 1) :
    Checked (modelNode 101 [target, andValue a b, d, e]) target (andValue a b) := by
  apply checked_native_node 101 target _ [d, e]
    (isSentence_namedForm _ (pure_conjunction ha hb).sentence) hcontext
  apply (localRule_andIntro_one_iff _ _ _ _ _).mpr
  rw [show conclusionValue d = a from hd.2.2, show conclusionValue e = b from he.2.2]
  exact ⟨holds_checked_child_included 101 _ d gamma target a hd (by simp) hincD,
    holds_checked_child_included 101 _ e delta target b he (by simp) hincE, rfl⟩

theorem checked_existentialInstanceRecord (p q body i n : M)
    (hp : Checked (rootValue p) (contextValue (rootValue p))
      (upperValue 0 (ProofPrograms.numeral.value ![i]) n))
    (hq : Checked (rootValue q) (contextValue (rootValue q))
      (instantiate.value ![body, ProofPrograms.numeral.value ![i] ]))
    (hb : FormulaBound 1 body)
    (hi : PureFormula (instantiate.value ![body, ProofPrograms.numeral.value ![i] ])) :
    Checked (existentialInstanceRecordValue p q body i n)
      (listAppend.value ![contextValue (rootValue p), contextValue (rootValue q)])
      (exValue (existentialMatrixValue body n)) := by
  let term := ProofPrograms.numeral.value ![i]
  let upper := upperValue 0 term n
  let out := instantiate.value ![body, term]
  let gamma := listAppend.value ![contextValue (rootValue p), contextValue (rootValue q)]
  let joint := modelNode 101 [gamma, andValue upper out, rootValue p, rootValue q]
  let m := existentialMatrixValue body n
  have hupper : PureFormula upper :=
    (upperValue_bound 0 term n ((PureTerm.numeral i).termBound 0)).pure
  have hgamma : formList.value ![zeroValue M, gamma] = numeralValue M 1 := by
    rw [formList_append_value, checked_context _ _ _ hp, checked_context _ _ _ hq,
      numeral_one_mul_model]
  have hjoint : Checked joint gamma (andValue upper out) :=
    checked_conjunction_into (rootValue p) (rootValue q) _ _ gamma upper out hp hq
      (contextIncluded_append_left_value _ _) (contextIncluded_append_right_value _ _)
      hupper hi hgamma
  have hinst : instantiate.value ![m, term] = andValue upper out :=
    existentialMatrix_instantiate_numeral body i n hb
  rw [← hinst] at hjoint
  exact checked_exIntro joint gamma m term hjoint (existentialMatrix_bound body n hb).namedForm
    (PureTerm.numeral i).namedTerm
    (isSentence_namedForm _ (pure_existential (existentialMatrix_bound body n hb)).sentence) hgamma

theorem certified_existentialInstanceCertificate (E : Program 2) (p q body i n : M)
    (hp : Certified E p (upperValue 0 (ProofPrograms.numeral.value ![i]) n))
    (hq : Certified E q (instantiate.value ![body, ProofPrograms.numeral.value ![i] ]))
    (hb : FormulaBound 1 body)
    (hi : PureFormula (instantiate.value ![body, ProofPrograms.numeral.value ![i] ])) :
    Certified E (existentialInstanceCertificate.value ![p, q, body, i, n])
      (exValue (existentialMatrixValue body n)) := by
  obtain ⟨_, hpd, hpc, _, _, _⟩ := (certified_iff E p _).mp hp
  obtain ⟨_, hqd, hqc, _, _, _⟩ := (certified_iff E q _).mp hq
  rw [existentialInstanceCertificate_value]
  exact certified_merge_contexts E p q _ _ _ _ hp hq
    (checked_existentialInstanceRecord p q body i n ⟨hpd, rfl, hpc⟩ ⟨hqd, rfl, hqc⟩ hb hi)
    (pure_existential (existentialMatrix_bound body n hb)).sentence

end
end Lemmatheca.MathematicalLogic.PAComputations.ProofPrograms.CheckerPrograms.BoundedCounterexamplePrograms
