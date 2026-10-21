import Lemmatheca.BoundedArithmeticProofs.PAProofFiniteCases
import Lemmatheca.PaListsAndSyntax.PAFixedFormulaCorrectness

open Lemmatheca.MathematicalLogic Lemmatheca.ModelTheory Lemmatheca.ComputabilityTheory

/-! Concrete native certificate programs for the signed implication step.
Their contexts are extended only during assumption discharge, and the original
axiom witnesses are retained verbatim. -/
namespace Lemmatheca.ProofTheory.PAComputations.ProofPrograms.CheckerPrograms.LogicalProofs
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic ArithmeticTheories ArithmeticRepresentability
open SyntaxPrograms FixedSyntaxPrograms
noncomputable section
universe u

def implicationFromConsequent : Program 3 :=
  let p : Program 3 := .proj 0
  let a : Program 3 := .proj 1
  let b : Program 3 := .proj 2
  retainWitnesses p (syntaxNode 107 [context (root p), impCode a b, root p, a])

def implicationFromNegative : Program 3 :=
  let p : Program 3 := .proj 0
  let a : Program 3 := .proj 1
  let b : Program 3 := .proj 2
  let gamma := context (root p)
  let ext := binary listCons a gamma
  let assumption := syntaxNode 100 [ext, a]
  let contradiction := syntaxNode 110 [ext, bottom, assumption, root p]
  let explosion := syntaxNode 111 [ext, b, contradiction]
  retainWitnesses p (syntaxNode 107 [gamma, impCode a b, explosion, a])

def negativeImplication : Program 4 :=
  let p : Program 4 := .proj 0
  let q : Program 4 := .proj 1
  let a : Program 4 := .proj 2
  let b : Program 4 := .proj 3
  let gamma := binary listAppend (context (root p)) (context (root q))
  let antecedent := impCode a b
  let ext := binary listCons antecedent gamma
  let assumption := syntaxNode 100 [ext, antecedent]
  let consequence := syntaxNode 108 [ext, b, assumption, root p]
  let contradiction := syntaxNode 110 [ext, bottom, consequence, root q]
  certificateAt (syntaxNode 109 [gamma, negCode antecedent, contradiction, antecedent])
    (binary listAppend (witnesses p) (witnesses q))

def bottomNegative {r : ℕ} : Program r :=
  let gamma : Program r := constant 0
  let ext := list [bottom]
  certificateAt (syntaxNode 107 [gamma, negCode bottom,
    syntaxNode 100 [ext, bottom], bottom]) gamma

section Internal
variable {M : Type u} [language.Structure M] [M ⊨ PA]

theorem implication_node (a b : M) : implication.value ![a, b] = modelNode 6 [a, b] :=
  implication_value a b

theorem pure_implication {a b : M} (ha : PureFormula a) (hb : PureFormula b) :
    PureFormula (implication.value ![a, b]) := by
  rw [implication_node]
  exact ha.imp hb

theorem pure_negation {a : M} (ha : PureFormula a) : PureFormula (negValue a) :=
  pure_implication ha PureFormula.bottom

theorem pure_existential {b : M} (hb : FormulaBound 1 b) : PureFormula (exValue b) := by
  have hn : FormulaBound 1 (negValue b) := by
    rw [negValue, implication_node]
    exact hb.imp (FormulaBound.bottom 1)
  exact pure_negation hn.all.pure

theorem bottomNegative_value {r : ℕ} (x : Fin r → M) :
    (bottomNegative : Program r).value x =
      modelList [modelNode 107 [zeroValue M, negValue (modelNode 3 []),
        modelNode 100 [modelList [modelNode 3 [] ], modelNode 3 [] ], modelNode 3 [] ], zeroValue M] := by
  simp only [bottomNegative, certificateAt, syntaxNode_value, list_cons_value, list_nil_value,
    bottom_value, negCode_value, constant_value, numeral_value_zero,
    modelNode, modelList_cons, modelList_nil]

theorem certified_bottomNegative (E : Program 2) {r : ℕ} (x : Fin r → M) :
    Certified E ((bottomNegative : Program r).value x) (negValue (modelNode 3 [])) := by
  have hb : isSentence.value ![modelNode 3 ([] : List M)] = numeralValue M 1 :=
    PureFormula.bottom.sentence
  have hn := (pure_negation (PureFormula.bottom (M := M))).sentence
  have hc : formList.value ![zeroValue M, zeroValue M] = numeralValue M 1 :=
    listAll_zero_value _ _
  have hext : formList.value ![zeroValue M, modelList [modelNode 3 [] ] ] = numeralValue M 1 :=
    (formList_cons_one_iff _ _ _).mpr ⟨isSentence_namedForm _ hb, hc⟩
  have hass := checked_assumption (modelList [modelNode 3 [] ]) (modelNode 3 [])
    (isSentence_namedForm _ hb) hext
    ((listMember_cons_one_iff _ _ _).mpr (Or.inl rfl))
  have hd := checked_impIntro _ (zeroValue M) (modelNode 3 []) (modelNode 3 [])
    hass (isSentence_namedForm _ hb) (isSentence_namedForm _ hn) hc
  rw [bottomNegative_value]
  exact certified_empty_context E _ _ hd hn

theorem implicationFromConsequent_value (p a b : M) :
    implicationFromConsequent.value ![p, a, b] =
      modelList [modelNode 107 [contextValue (rootValue p), implication.value ![a, b],
        rootValue p, a], witnessesValue p] := by
  simp only [implicationFromConsequent, retainWitnesses, certificateAt, syntaxNode_value,
    list_cons_value, list_nil_value, impCode, binary_value, root, context, witnesses,
    unary_value, Program.value_proj, constant_value, numeral_value_zero,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, rootValue, contextValue, witnessesValue,
    modelNode, modelList_cons, modelList_nil]

theorem certified_implicationFromConsequent (E : Program 2) (p a b : M)
    (hp : Certified E p b) (ha : PureFormula a) (hb : PureFormula b) :
    Certified E (implicationFromConsequent.value ![p, a, b]) (implication.value ![a, b]) := by
  obtain ⟨_, hd, hc, _, _, _⟩ := (certified_iff E p b).mp hp
  have hd' : Checked (rootValue p) (contextValue (rootValue p)) b := ⟨hd, rfl, hc⟩
  have hout := (pure_implication ha hb).sentence
  have hnew := checked_impIntro_included (rootValue p) (contextValue (rootValue p))
    (contextValue (rootValue p)) a b hd'
    (contextIncluded_under_cons _ _)
    (isSentence_namedForm _ ha.sentence) (isSentence_namedForm _ hout)
    (checked_context _ _ _ hd')
  rw [implicationFromConsequent_value]
  exact certified_retain_witnesses E p _ _ _ hp hnew hout

def implicationNegativeValue (p a b : M) : M :=
  let gamma := contextValue (rootValue p)
  let ext := listCons.value ![a, gamma]
  let assumption := modelNode 100 [ext, a]
  let contradiction := modelNode 110 [ext, modelNode 3 [], assumption, rootValue p]
  let explosion := modelNode 111 [ext, b, contradiction]
  modelNode 107 [gamma, implication.value ![a, b], explosion, a]

theorem implicationFromNegative_value (p a b : M) :
    implicationFromNegative.value ![p, a, b] =
      modelList [implicationNegativeValue p a b, witnessesValue p] := by
  simp only [implicationFromNegative, retainWitnesses, certificateAt, syntaxNode_value,
    list_cons_value, list_nil_value, impCode, binary_value, root, context, witnesses,
    unary_value, bottom_value, Program.value_proj, constant_value, numeral_value_zero,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, rootValue, contextValue, witnessesValue,
    implicationNegativeValue, modelNode, modelList_cons, modelList_nil]

theorem checked_implicationFromNegative (p a b : M)
    (hd : Checked (rootValue p) (contextValue (rootValue p)) (negValue a))
    (ha : PureFormula a) (hb : PureFormula b) :
    Checked (implicationNegativeValue p a b) (contextValue (rootValue p))
      (implication.value ![a, b]) := by
  let gamma := contextValue (rootValue p)
  let ext := listCons.value ![a, gamma]
  have hgamma := checked_context _ _ _ hd
  have hext : formList.value ![zeroValue M, ext] = numeralValue M 1 :=
    (formList_cons_one_iff _ _ _).mpr ⟨isSentence_namedForm _ ha.sentence, hgamma⟩
  have hass := checked_assumption ext a (isSentence_namedForm _ ha.sentence) hext
    ((listMember_cons_one_iff _ _ _).mpr (Or.inl rfl))
  have hcontra := checked_notElim_into (modelNode 100 [ext, a]) (rootValue p)
    ext gamma ext a hass hd (contextIncluded_refl_value _)
    (contextIncluded_under_cons _ _) (isSentence_namedForm _ PureFormula.bottom.sentence) hext
  have hexplode := checked_falseElim _ ext b hcontra (isSentence_namedForm _ hb.sentence) hext
  exact checked_impIntro _ gamma a b hexplode (isSentence_namedForm _ ha.sentence)
    (isSentence_namedForm _ (pure_implication ha hb).sentence) hgamma

theorem certified_implicationFromNegative (E : Program 2) (p a b : M)
    (hp : Certified E p (negValue a)) (ha : PureFormula a) (hb : PureFormula b) :
    Certified E (implicationFromNegative.value ![p, a, b]) (implication.value ![a, b]) := by
  obtain ⟨_, hd, hc, _, _, _⟩ := (certified_iff E p _).mp hp
  have hnew := checked_implicationFromNegative p a b ⟨hd, rfl, hc⟩ ha hb
  rw [implicationFromNegative_value]
  exact certified_retain_witnesses E p _ _ _ hp hnew (pure_implication ha hb).sentence

def negativeImplicationValue (p q a b : M) : M :=
  let gamma := listAppend.value ![contextValue (rootValue p), contextValue (rootValue q)]
  let antecedent := implication.value ![a, b]
  let ext := listCons.value ![antecedent, gamma]
  let assumption := modelNode 100 [ext, antecedent]
  let consequence := modelNode 108 [ext, b, assumption, rootValue p]
  let contradiction := modelNode 110 [ext, modelNode 3 [], consequence, rootValue q]
  modelNode 109 [gamma, negValue antecedent, contradiction, antecedent]

theorem negativeImplication_value (p q a b : M) :
    negativeImplication.value ![p, q, a, b] =
      modelList [negativeImplicationValue p q a b,
        listAppend.value ![witnessesValue p, witnessesValue q] ] := by
  simp only [negativeImplication, certificateAt, syntaxNode_value,
    list_cons_value, list_nil_value, impCode, binary_value, root, context, witnesses,
    unary_value, bottom_value, negCode_value, Program.value_proj, constant_value,
    numeral_value_zero, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, rootValue, contextValue,
    witnessesValue, negativeImplicationValue, modelNode, modelList_cons, modelList_nil]

theorem checked_negativeImplication (p q a b : M)
    (hp : Checked (rootValue p) (contextValue (rootValue p)) a)
    (hq : Checked (rootValue q) (contextValue (rootValue q)) (negValue b))
    (ha : PureFormula a) (hb : PureFormula b) :
    Checked (negativeImplicationValue p q a b)
      (listAppend.value ![contextValue (rootValue p), contextValue (rootValue q)])
      (negValue (implication.value ![a, b])) := by
  let gamma := listAppend.value ![contextValue (rootValue p), contextValue (rootValue q)]
  let antecedent := implication.value ![a, b]
  let ext := listCons.value ![antecedent, gamma]
  have hant : PureFormula antecedent := pure_implication ha hb
  have hgamma : formList.value ![zeroValue M, gamma] = numeralValue M 1 := by
    rw [formList_append_value, checked_context _ _ _ hp, checked_context _ _ _ hq,
      numeral_one_mul_model]
  have hext : formList.value ![zeroValue M, ext] = numeralValue M 1 :=
    (formList_cons_one_iff _ _ _).mpr ⟨isSentence_namedForm _ hant.sentence, hgamma⟩
  have hass := checked_assumption ext antecedent (isSentence_namedForm _ hant.sentence) hext
    ((listMember_cons_one_iff _ _ _).mpr (Or.inl rfl))
  have hip : contextIncluded.value ![contextValue (rootValue p), ext] = numeralValue M 1 :=
    contextIncluded_trans_value _ gamma ext (contextIncluded_append_left_value _ _)
      (contextIncluded_under_cons _ _)
  have hiq : contextIncluded.value ![contextValue (rootValue q), ext] = numeralValue M 1 :=
    contextIncluded_trans_value _ gamma ext (contextIncluded_append_right_value _ _)
      (contextIncluded_under_cons _ _)
  have hconseq := checked_modusPonens_into (modelNode 100 [ext, antecedent]) (rootValue p)
    ext (contextValue (rootValue p)) ext a b hass hp
    (contextIncluded_refl_value _) hip (isSentence_namedForm _ hb.sentence) hext
  have hcontra := checked_notElim_into _ (rootValue q) ext (contextValue (rootValue q)) ext b
    hconseq hq (contextIncluded_refl_value _) hiq
    (isSentence_namedForm _ PureFormula.bottom.sentence) hext
  exact checked_notIntro _ gamma antecedent hcontra (isSentence_namedForm _ hant.sentence)
    (isSentence_namedForm _ (pure_negation hant).sentence) hgamma

theorem certified_negativeImplication (E : Program 2) (p q a b : M)
    (hp : Certified E p a) (hq : Certified E q (negValue b))
    (ha : PureFormula a) (hb : PureFormula b) :
    Certified E (negativeImplication.value ![p, q, a, b])
      (negValue (implication.value ![a, b])) := by
  obtain ⟨_, hpd, hpc, _, _, _⟩ := (certified_iff E p _).mp hp
  obtain ⟨_, hqd, hqc, _, _, _⟩ := (certified_iff E q _).mp hq
  have hd := checked_negativeImplication p q a b ⟨hpd, rfl, hpc⟩ ⟨hqd, rfl, hqc⟩ ha hb
  rw [negativeImplication_value]
  exact certified_merge_contexts E p q _ _ _ _ hp hq hd
    (pure_negation (pure_implication ha hb)).sentence

end Internal
end
end Lemmatheca.ProofTheory.PAComputations.ProofPrograms.CheckerPrograms.LogicalProofs
