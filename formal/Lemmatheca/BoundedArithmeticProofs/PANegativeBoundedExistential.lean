import Lemmatheca.BoundedArithmeticProofs.PABoundedUniversalPrograms
import Lemmatheca.PaProofCheckers.PAProofContextFreshness
import Lemmatheca.BoundedArithmeticProofs.PANativeEqualityLogic

open Lemmatheca.MathematicalLogic Lemmatheca.ModelTheory Lemmatheca.ComputabilityTheory

/-! A native proof of ¬∃z(A(z) ∧ B(z)) from ∀z(A(z) → ¬B(z)).
The actual existential-elimination freshness checks are retained. -/
namespace Lemmatheca.ProofTheory.PAComputations.ProofPrograms.CheckerPrograms.BoundedExistentialNegation
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic ArithmeticTheories ArithmeticRepresentability
open SyntaxPrograms FixedSyntaxPrograms LogicalProofs NumericalProofs BoundedUniversalPrograms InitialSegmentPrograms
noncomputable section

def universalNegativeToNegativeExistential : Program 3 :=
  let p : Program 3 := .proj 0
  let a : Program 3 := .proj 1
  let b : Program 3 := .proj 2
  let matrix := impCode a (negCode b)
  let conjunction := andCode a b
  let existential := exCode conjunction
  let gamma := context (root p)
  let ext := binary listCons existential gamma
  let z : Program 3 := syntaxNode 8 [constant 0]
  let ai := binary instantiate a z
  let bi := binary instantiate b z
  let pair := andCode ai bi
  let inner := binary listCons pair ext
  let pairAss := syntaxNode 100 [inner, pair]
  let first := syntaxNode 102 [inner, ai, pairAss, bi]
  let second := syntaxNode 103 [inner, bi, pairAss, ai]
  let inst := syntaxNode 113 [inner, impCode ai (negCode bi), root p, matrix, z]
  let negative := syntaxNode 108 [inner, negCode bi, inst, first]
  let contradiction := syntaxNode 110 [inner, bottom, second, negative]
  let existsAss := syntaxNode 100 [ext, existential]
  let eliminated := syntaxNode 116 [ext, bottom, existsAss, contradiction, conjunction, constant 0]
  retainWitnesses p (syntaxNode 109 [gamma, negCode existential, eliminated, existential])

section Internal
universe u
variable {M : Type u} [language.Structure M] [M ⊨ PA]

theorem bounded_implication {k : ℕ} {a b : M} (ha : FormulaBound k a) (hb : FormulaBound k b) :
    FormulaBound k (implication.value ![a, b]) := by
  rw [implication_node]
  exact ha.imp hb

theorem bounded_conjunction {k : ℕ} {a b : M} (ha : FormulaBound k a) (hb : FormulaBound k b) :
    FormulaBound k (andValue a b) :=
  negation_bound (bounded_implication ha (negation_bound hb))

theorem named_implication {k : ℕ} {a b : M} (ha : NamedFormulaBound k a) (hb : NamedFormulaBound k b) :
    NamedFormulaBound k (implication.value ![a, b]) := by
  rw [implication_node]
  exact ha.imp hb

theorem named_negation {k : ℕ} {a : M} (ha : NamedFormulaBound k a) :
    NamedFormulaBound k (negValue a) := named_implication ha (NamedFormulaBound.bottom k)

theorem named_conjunction {k : ℕ} {a b : M} (ha : NamedFormulaBound k a) (hb : NamedFormulaBound k b) :
    NamedFormulaBound k (andValue a b) := named_negation (named_implication ha (named_negation hb))

theorem instantiate_implication {a b t : M} (ha : FormulaBound 1 a) (hb : FormulaBound 1 b)
    (ht : namedTerm.value ![t] = numeralValue M 1) :
    instantiate.value ![implication.value ![a, b], t] =
      implication.value ![instantiate.value ![a, t], instantiate.value ![b, t] ] := by
  rw [instantiate_value_of_tests _ _ (bounded_implication ha hb).namedForm ht,
    implication_node, rewrite_slot_imp_value,
    ← instantiate_value_of_tests _ _ ha.namedForm ht,
    ← instantiate_value_of_tests _ _ hb.namedForm ht, implication_node]

theorem instantiate_negation {a t : M} (ha : FormulaBound 1 a)
    (ht : namedTerm.value ![t] = numeralValue M 1) :
    instantiate.value ![negValue a, t] = negValue (instantiate.value ![a, t]) := by
  rw [negValue, instantiate_implication ha (FormulaBound.bottom 1) ht]
  have hb : instantiate.value ![modelNode 3 ([] : List M), t] = modelNode 3 [] := by
    rw [instantiate_value_of_tests _ _ (FormulaBound.bottom 1).namedForm ht,
      rewrite_slot_nonleaf_value 3 (by decide) (by decide) (by decide)]
    rfl
  rw [hb]
  rfl

theorem instantiate_conjunction {a b t : M} (ha : FormulaBound 1 a) (hb : FormulaBound 1 b)
    (ht : namedTerm.value ![t] = numeralValue M 1) :
    instantiate.value ![andValue a b, t] =
      andValue (instantiate.value ![a, t]) (instantiate.value ![b, t]) := by
  rw [andValue, instantiate_negation (bounded_implication ha (negation_bound hb)) ht,
    instantiate_implication ha (negation_bound hb) ht, instantiate_negation hb ht]
  rfl

theorem occurs_negation_zero (j a : M) (ha : occursAux.value ![j, a] = zeroValue M) :
    occursAux.value ![j, negValue a] = zeroValue M := by
  simp only [negValue, implication_node]
  apply occursAux_modelNode_zero j 6 _ (by decide)
  intro x hx
  simp only [Nat.reduceEqDiff, or_self, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · exact ha
  · apply occursAux_modelNode_zero j 3 _ (by decide)
    simp

theorem occurs_implication_zero (j a b : M)
    (ha : occursAux.value ![j, a] = zeroValue M) (hb : occursAux.value ![j, b] = zeroValue M) :
    occursAux.value ![j, implication.value ![a, b] ] = zeroValue M := by
  rw [implication_node]
  apply occursAux_modelNode_zero j 6 _ (by decide)
  intro x hx
  simp only [Nat.reduceEqDiff, or_self, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · exact ha
  · exact hb

theorem occurs_conjunction_zero (j a b : M)
    (ha : occursAux.value ![j, a] = zeroValue M) (hb : occursAux.value ![j, b] = zeroValue M) :
    occursAux.value ![j, andValue a b] = zeroValue M :=
  occurs_negation_zero j _ (occurs_implication_zero j _ _ ha (occurs_negation_zero j b hb))

theorem occurs_existential_zero (j a : M) (ha : occursAux.value ![j, a] = zeroValue M) :
    occursAux.value ![j, exValue a] = zeroValue M := by
  apply occurs_negation_zero
  apply occursAux_modelNode_zero j 7 _ (by decide)
  intro x hx
  simp only [Nat.reduceEqDiff, or_self, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hx
  subst x
  exact occurs_negation_zero j a ha

theorem checked_andLeft (d gamma a b : M) (hd : Checked d gamma (andValue a b))
    (ha : namedForm.value ![zeroValue M, a] = numeralValue M 1)
    (hb : namedForm.value ![zeroValue M, b] = numeralValue M 1) :
    Checked (modelNode 102 [gamma, a, d, b]) gamma a := by
  apply checked_native_node 102 gamma a [d, b] ha (checked_context _ _ _ hd)
  exact (localRule_andLeft_one_iff _ _ _ _ _).mpr
    ⟨hb, holds_checked_child 102 _ d _ _ hd (by simp)⟩

theorem checked_andRight (d gamma a b : M) (hd : Checked d gamma (andValue a b))
    (ha : namedForm.value ![zeroValue M, a] = numeralValue M 1)
    (hb : namedForm.value ![zeroValue M, b] = numeralValue M 1) :
    Checked (modelNode 103 [gamma, b, d, a]) gamma b := by
  apply checked_native_node 103 gamma b [d, a] hb (checked_context _ _ _ hd)
  exact (localRule_andRight_one_iff _ _ _ _ _).mpr
    ⟨ha, holds_checked_child 103 _ d _ _ hd (by simp)⟩

def negativeExistentialRecord (p a b : M) : M :=
  let matrix := implication.value ![a, negValue b]
  let conjunction := andValue a b
  let existential := exValue conjunction
  let gamma := contextValue (rootValue p)
  let ext := listCons.value ![existential, gamma]
  let z := modelNode 8 [zeroValue M]
  let ai := instantiate.value ![a, z]
  let bi := instantiate.value ![b, z]
  let pair := andValue ai bi
  let inner := listCons.value ![pair, ext]
  let pairAss := modelNode 100 [inner, pair]
  let first := modelNode 102 [inner, ai, pairAss, bi]
  let second := modelNode 103 [inner, bi, pairAss, ai]
  let inst := modelNode 113 [inner, implication.value ![ai, negValue bi], rootValue p, matrix, z]
  let negative := modelNode 108 [inner, negValue bi, inst, first]
  let contradiction := modelNode 110 [inner, modelNode 3 [], second, negative]
  let existsAss := modelNode 100 [ext, existential]
  let eliminated := modelNode 116 [ext, modelNode 3 [], existsAss, contradiction, conjunction, zeroValue M]
  modelNode 109 [gamma, negValue existential, eliminated, existential]

theorem checked_negativeExistentialRecord (E : Program 2) (p a b : M)
    (hp : Certified E p (modelNode 7 [implication.value ![a, negValue b] ]))
    (ha : FormulaBound 1 a) (hb : FormulaBound 1 b)
    (hai : NamedFormulaBound 0 (instantiate.value ![a, modelNode 8 [zeroValue M] ]))
    (hbi : NamedFormulaBound 0 (instantiate.value ![b, modelNode 8 [zeroValue M] ]))
    (hfa : occursAux.value ![zeroValue M, a] = zeroValue M)
    (hfb : occursAux.value ![zeroValue M, b] = zeroValue M) :
    Checked (negativeExistentialRecord p a b) (contextValue (rootValue p))
      (negValue (exValue (andValue a b))) := by
  let matrix := implication.value ![a, negValue b]
  let conjunction := andValue a b
  let existential := exValue conjunction
  let gamma := contextValue (rootValue p)
  let ext := listCons.value ![existential, gamma]
  let z := modelNode 8 [zeroValue M]
  let ai := instantiate.value ![a, z]
  let bi := instantiate.value ![b, z]
  let pair := andValue ai bi
  let inner := listCons.value ![pair, ext]
  let pairAss := modelNode 100 [inner, pair]
  let first := modelNode 102 [inner, ai, pairAss, bi]
  let second := modelNode 103 [inner, bi, pairAss, ai]
  let inst := modelNode 113 [inner, implication.value ![ai, negValue bi], rootValue p, matrix, z]
  let negative := modelNode 108 [inner, negValue bi, inst, first]
  let contradiction := modelNode 110 [inner, modelNode 3 [], second, negative]
  let existsAss := modelNode 100 [ext, existential]
  let eliminated := modelNode 116 [ext, modelNode 3 [], existsAss, contradiction, conjunction, zeroValue M]
  obtain ⟨_, hd, hc, _, _, _⟩ := (certified_iff E p _).mp hp
  have hroot : Checked (rootValue p) gamma (modelNode 7 [matrix]) := ⟨hd, rfl, hc⟩
  have hgamma := checked_context _ _ _ hroot
  have hex := pure_existential (bounded_conjunction ha hb)
  have hexform := isSentence_namedForm _ hex.sentence
  have hnexform := isSentence_namedForm _ (pure_negation hex).sentence
  have haiform : namedForm.value ![zeroValue M, ai] = numeralValue M 1 := by
    simpa only [numeral_value_zero] using hai.namedForm
  have hbiform : namedForm.value ![zeroValue M, bi] = numeralValue M 1 := by
    simpa only [numeral_value_zero] using hbi.namedForm
  have hpairform : namedForm.value ![zeroValue M, pair] = numeralValue M 1 := by
    simpa only [numeral_value_zero] using (named_conjunction hai hbi).namedForm
  have hnegform : namedForm.value ![zeroValue M, negValue bi] = numeralValue M 1 := by
    simpa only [numeral_value_zero] using (named_negation hbi).namedForm
  have hbot := isSentence_namedForm _ (PureFormula.bottom (M := M)).sentence
  have hext : formList.value ![zeroValue M, ext] = numeralValue M 1 :=
    (formList_cons_one_iff _ _ _).mpr ⟨hexform, hgamma⟩
  have hinner : formList.value ![zeroValue M, inner] = numeralValue M 1 :=
    (formList_cons_one_iff _ _ _).mpr ⟨hpairform, hext⟩
  have hass : Checked pairAss inner pair := checked_assumption inner pair hpairform hinner
    ((listMember_cons_one_iff _ _ _).mpr (Or.inl rfl))
  have hfirst : Checked first inner ai := checked_andLeft _ _ _ _ hass haiform hbiform
  have hsecond : Checked second inner bi := checked_andRight _ _ _ _ hass haiform hbiform
  have hgin : contextIncluded.value ![gamma, inner] = numeralValue M 1 :=
    contextIncluded_trans_value gamma ext inner (contextIncluded_under_cons gamma existential)
      (contextIncluded_under_cons ext pair)
  have hinst : instantiate.value ![matrix, z] = implication.value ![ai, negValue bi] := by
    rw [instantiate_implication ha (negation_bound hb) aux_zero_namedTerm,
      instantiate_negation hb aux_zero_namedTerm]
  have hinstform : namedForm.value ![zeroValue M, instantiate.value ![matrix, z] ] = numeralValue M 1 := by
    rw [hinst]
    simpa only [numeral_value_zero] using (named_implication hai (named_negation hbi)).namedForm
  have hforall := checked_forallElimination_into (rootValue p) gamma inner matrix z hroot hgin
    (bounded_implication ha (negation_bound hb)).namedForm aux_zero_namedTerm hinstform hinner
  have hforall' : Checked inst inner (implication.value ![ai, negValue bi]) := by
    simpa only [hinst] using hforall
  have hnegative : Checked negative inner (negValue bi) :=
    checked_modusPonens_into _ _ inner inner inner ai (negValue bi) hforall' hfirst
      (contextIncluded_refl_value inner) (contextIncluded_refl_value inner) hnegform hinner
  have hcontra : Checked contradiction inner (modelNode 3 []) :=
    checked_notElim _ _ inner bi hsecond hnegative hbot hinner
  have hexass : Checked existsAss ext existential := checked_assumption ext existential hexform hext
    ((listMember_cons_one_iff _ _ _).mpr (Or.inl rfl))
  have hconjfresh : occursAux.value ![zeroValue M, conjunction] = zeroValue M :=
    occurs_conjunction_zero _ _ _ hfa hfb
  have hexfresh : occursAux.value ![zeroValue M, existential] = zeroValue M :=
    occurs_existential_zero _ _ hconjfresh
  have hbotfresh : occursAux.value ![zeroValue M, modelNode 3 ([] : List M)] = zeroValue M := by
    apply occursAux_modelNode_zero _ 3 [] (by decide)
    simp
  have hextfresh : contextFresh.value ![zeroValue M, ext] = numeralValue M 1 :=
    (contextFresh_cons_one_iff _ _ _).mpr
      ⟨hexfresh, certified_contextFresh E (zeroValue M) p _ hp⟩
  have hconjinst : instantiate.value ![conjunction, z] = pair :=
    instantiate_conjunction ha hb aux_zero_namedTerm
  have helim : Checked eliminated ext (modelNode 3 []) := by
    apply checked_native_node 116 ext _ [existsAss, contradiction, conjunction, zeroValue M] hbot hext
    apply (localRule_exElim_one_iff _ _ _ _ _ _ _).mpr
    refine ⟨(bounded_conjunction ha hb).namedForm,
      holds_checked_child 116 _ existsAss _ _ hexass (by simp), ?_, hconjfresh, hbotfresh, hextfresh⟩
    rw [hconjinst]
    exact holds_checked_child 116 _ contradiction _ _ hcontra (by simp)
  exact checked_notIntro eliminated gamma existential helim hexform hnexform hgamma

theorem universalNegativeToNegativeExistential_value (p a b : M) :
    universalNegativeToNegativeExistential.value ![p, a, b] =
      modelList [negativeExistentialRecord p a b, witnessesValue p] := by
  simp only [universalNegativeToNegativeExistential, retainWitnesses, certificateAt,
    list_cons_value, list_nil_value, syntaxNode_model_value, List.map_cons, List.map_nil,
    root_program_value, context_program_value, witnesses_program_value,
    impCode, binary_value, negCode_value, andCode_value, exCode_value,
    bottom_value, constant_value, numeral_value_zero, Program.value_proj,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, negativeExistentialRecord,
    modelList_cons, modelList_nil]

theorem certified_universalNegativeToNegativeExistential (E : Program 2) (p a b : M)
    (hp : Certified E p (modelNode 7 [implication.value ![a, negValue b] ]))
    (ha : FormulaBound 1 a) (hb : FormulaBound 1 b)
    (hai : NamedFormulaBound 0 (instantiate.value ![a, modelNode 8 [zeroValue M] ]))
    (hbi : NamedFormulaBound 0 (instantiate.value ![b, modelNode 8 [zeroValue M] ]))
    (hfa : occursAux.value ![zeroValue M, a] = zeroValue M)
    (hfb : occursAux.value ![zeroValue M, b] = zeroValue M) :
    Certified E (universalNegativeToNegativeExistential.value ![p, a, b])
      (negValue (exValue (andValue a b))) := by
  rw [universalNegativeToNegativeExistential_value]
  have hout := (pure_negation (pure_existential (bounded_conjunction ha hb))).sentence
  exact certified_retain_witnesses E p _ (negativeExistentialRecord p a b) _ hp
    (checked_negativeExistentialRecord E p a b hp ha hb hai hbi hfa hfb) hout

end Internal
end
end Lemmatheca.ProofTheory.PAComputations.ProofPrograms.CheckerPrograms.BoundedExistentialNegation
