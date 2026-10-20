import Lemmatheca.MathematicalLogic.PABoundedUniversalPrograms
import Lemmatheca.MathematicalLogic.PANativeLogicalProofs

/-! The actual counterexample proof: specialize a proposed bounded universal,
apply its accepted numerical bound proof, and contradict the accepted negative
body instance. -/
namespace Lemmatheca.MathematicalLogic.PAComputations.ProofPrograms.CheckerPrograms.BoundedCounterexamplePrograms
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic ArithmeticTheories ArithmeticRepresentability
open SyntaxPrograms FixedSyntaxPrograms InitialSegmentPrograms BoundedUniversalPrograms LogicalProofs
noncomputable section
universe u

/-- Inputs: upper-bound certificate, negative-instance certificate, one-slot
body, witness, bound. -/
def counterexampleCertificate : Program 5 :=
  let p : Program 5 := .proj 0
  let q : Program 5 := .proj 1
  let body : Program 5 := .proj 2
  let i : Program 5 := .proj 3
  let n : Program 5 := .proj 4
  let term := unary ProofPrograms.numeral i
  let gamma := binary listAppend (context (root p)) (context (root q))
  let m := matrix body n
  let target := allCode m
  let ext := binary listCons target gamma
  let ass := syntaxNode 100 [ext, target]
  let inst := binary instantiate m term
  let spec := syntaxNode 113 [ext, inst, ass, m, term]
  let out := binary instantiate body term
  let application := syntaxNode 108 [ext, out, spec, root p]
  let contradiction := syntaxNode 110 [ext, bottom, application, root q]
  certificateAt (syntaxNode 109 [gamma, negCode target, contradiction, target])
    (binary listAppend (witnesses p) (witnesses q))

variable {M : Type u} [language.Structure M] [M ⊨ PA]

def counterexampleRecordValue (p q body i n : M) : M :=
  let term := ProofPrograms.numeral.value ![i]
  let gamma := listAppend.value ![contextValue (rootValue p), contextValue (rootValue q)]
  let m := matrixValue body n
  let target := modelNode 7 [m]
  let ext := listCons.value ![target, gamma]
  let ass := modelNode 100 [ext, target]
  let inst := instantiate.value ![m, term]
  let spec := modelNode 113 [ext, inst, ass, m, term]
  let out := instantiate.value ![body, term]
  let application := modelNode 108 [ext, out, spec, rootValue p]
  let contradiction := modelNode 110 [ext, modelNode 3 [], application, rootValue q]
  modelNode 109 [gamma, negValue target, contradiction, target]

theorem counterexampleCertificate_value (p q body i n : M) :
    counterexampleCertificate.value ![p, q, body, i, n] =
      modelList [counterexampleRecordValue p q body i n,
        listAppend.value ![witnessesValue p, witnessesValue q] ] := by
  simp only [counterexampleCertificate, certificateAt, FixedSyntaxPrograms.list_value, syntaxNode_model_value,
    List.map_cons, List.map_nil, binary_value, unary_value,
    root_program_value, context_program_value, witnesses_program_value,
    matrix_model_value, allCode_value, negCode_value, bottom_value, Program.value_proj,
    modelList_cons, modelList_nil,
    counterexampleRecordValue, modelNode]
  rfl

theorem matrix_instantiate_numeral (body i n : M) (hb : FormulaBound 1 body) :
    instantiate.value ![matrixValue body n, ProofPrograms.numeral.value ![i] ] =
      implication.value ![upperValue 0 (ProofPrograms.numeral.value ![i]) n,
        instantiate.value ![body, ProofPrograms.numeral.value ![i] ] ] := by
  rw [instantiate_value_of_tests _ _ (matrix_namedForm body n hb) (PureTerm.numeral i).namedTerm]
  simp only [matrixValue, implication_node_value]
  rw [rewrite_slot_imp_value, upperValue_rewrite 0, rewrite_slot_bound_zero_value,
    ← instantiate_value_of_tests _ _ hb.namedForm (PureTerm.numeral i).namedTerm]

theorem checked_counterexampleRecord (p q body i n : M)
    (hp : Checked (rootValue p) (contextValue (rootValue p))
      (upperValue 0 (ProofPrograms.numeral.value ![i]) n))
    (hq : Checked (rootValue q) (contextValue (rootValue q))
      (negValue (instantiate.value ![body, ProofPrograms.numeral.value ![i] ])))
    (hb : FormulaBound 1 body)
    (hi : PureFormula (instantiate.value ![body, ProofPrograms.numeral.value ![i] ])) :
    Checked (counterexampleRecordValue p q body i n)
      (listAppend.value ![contextValue (rootValue p), contextValue (rootValue q)])
      (negValue (modelNode 7 [matrixValue body n])) := by
  let term := ProofPrograms.numeral.value ![i]
  let upper := upperValue 0 term n
  let out := instantiate.value ![body, term]
  let gamma := listAppend.value ![contextValue (rootValue p), contextValue (rootValue q)]
  let m := matrixValue body n
  let target := modelNode 7 [m]
  let ext := listCons.value ![target, gamma]
  let ass := modelNode 100 [ext, target]
  let inst := instantiate.value ![m, term]
  let spec := modelNode 113 [ext, inst, ass, m, term]
  let application := modelNode 108 [ext, out, spec, rootValue p]
  have htarget : PureFormula target := (matrix_bound body n hb).all.pure
  have hupper : PureFormula upper :=
    (upperValue_bound 0 term n ((PureTerm.numeral i).termBound 0)).pure
  have hinst : inst = implication.value ![upper, out] := matrix_instantiate_numeral body i n hb
  have hgamma : formList.value ![zeroValue M, gamma] = numeralValue M 1 := by
    rw [formList_append_value, checked_context _ _ _ hp, checked_context _ _ _ hq,
      numeral_one_mul_model]
  have hext : formList.value ![zeroValue M, ext] = numeralValue M 1 :=
    (formList_cons_one_iff _ _ _).mpr ⟨isSentence_namedForm _ htarget.sentence, hgamma⟩
  have hass := checked_assumption ext target (isSentence_namedForm _ htarget.sentence) hext
    ((listMember_cons_one_iff _ _ _).mpr (Or.inl rfl))
  have hspec : Checked spec ext inst := checked_forallElimination_into ass ext ext m term hass
    (contextIncluded_refl_value _) (matrix_namedForm body n hb) (PureTerm.numeral i).namedTerm
    (by
      change namedForm.value ![zeroValue M, inst] = numeralValue M 1
      rw [hinst]
      exact isSentence_namedForm _ (pure_implication hupper hi).sentence) hext
  have hip : contextIncluded.value ![contextValue (rootValue p), ext] = numeralValue M 1 :=
    contextIncluded_trans_value _ gamma ext (contextIncluded_append_left_value _ _)
      (contextIncluded_under_cons _ _)
  have hiq : contextIncluded.value ![contextValue (rootValue q), ext] = numeralValue M 1 :=
    contextIncluded_trans_value _ gamma ext (contextIncluded_append_right_value _ _)
      (contextIncluded_under_cons _ _)
  rw [hinst] at hspec
  have happ : Checked application ext out := checked_modusPonens_into spec (rootValue p)
    ext (contextValue (rootValue p)) ext upper out hspec hp (contextIncluded_refl_value _)
    hip (isSentence_namedForm _ hi.sentence) hext
  have hcontra := checked_notElim_into application (rootValue q) ext
    (contextValue (rootValue q)) ext out happ hq (contextIncluded_refl_value _) hiq
    (isSentence_namedForm _ PureFormula.bottom.sentence) hext
  exact checked_notIntro _ gamma target hcontra (isSentence_namedForm _ htarget.sentence)
    (isSentence_namedForm _ (pure_negation htarget).sentence) hgamma

theorem certified_counterexampleCertificate (E : Program 2) (p q body i n : M)
    (hp : Certified E p (upperValue 0 (ProofPrograms.numeral.value ![i]) n))
    (hq : Certified E q (negValue (instantiate.value ![body, ProofPrograms.numeral.value ![i] ])))
    (hb : FormulaBound 1 body)
    (hi : PureFormula (instantiate.value ![body, ProofPrograms.numeral.value ![i] ])) :
    Certified E (counterexampleCertificate.value ![p, q, body, i, n])
      (negValue (modelNode 7 [matrixValue body n])) := by
  obtain ⟨_, hpd, hpc, _, _, _⟩ := (certified_iff E p _).mp hp
  obtain ⟨_, hqd, hqc, _, _, _⟩ := (certified_iff E q _).mp hq
  rw [counterexampleCertificate_value]
  exact certified_merge_contexts E p q _ _ _ _ hp hq
    (checked_counterexampleRecord p q body i n ⟨hpd, rfl, hpc⟩ ⟨hqd, rfl, hqc⟩ hb hi)
    (pure_negation (matrix_bound body n hb).all.pure).sentence

end
end Lemmatheca.MathematicalLogic.PAComputations.ProofPrograms.CheckerPrograms.BoundedCounterexamplePrograms
