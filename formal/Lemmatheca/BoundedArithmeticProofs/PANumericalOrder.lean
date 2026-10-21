import Lemmatheca.PaListsAndSyntax.PAModelSyntaxCorrectness
import Lemmatheca.BoundedArithmeticProofs.PANativeLogicalProofs
import Lemmatheca.BoundedArithmeticProofs.PANumericalProofPrograms
import Lemmatheca.BoundedArithmeticProofs.PANumeralArithmeticProofs
import Lemmatheca.BoundedArithmeticProofs.PANativeEqualityLogic
import Lemmatheca.BoundedArithmeticProofs.PANumericalAxiomInstances
import Lemmatheca.BoundedArithmeticProofs.PATermEvaluationProofs

open Lemmatheca.MathematicalLogic Lemmatheca.ModelTheory Lemmatheca.ComputabilityTheory

/-! Native order formulas and numerical order certificates. -/
namespace Lemmatheca.ProofTheory.PAComputations.ProofPrograms.CheckerPrograms.NumericalProofs
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic ArithmeticTheories ArithmeticRepresentability FirstOrderProofs
open SyntaxPrograms FixedSyntaxPrograms LogicalProofs
noncomputable section
universe u

def strictAdditionComparison : language.Formula (Fin 2) :=
  (leFormula (succTerm (addTerm (.var 0) (.var 1))) (.var 0)).not

theorem strictAdditionComparison_derives : Derives PA (close strictAdditionComparison) := by
  apply HenkinCompleteness.deductive_completeness
  apply Theory.models_sentence_iff.mpr
  intro M
  rw [realize_close]
  intro v
  simp only [strictAdditionComparison, Formula.realize_not, realize_leFormula,
    realize_succTerm, realize_addTerm, Term.realize_var]
  intro hle
  have h := ((successor_le_iff_lt _ _).mp hle).2
  exact h ⟨v 1, add_comm_value _ _⟩

def orderBodyCode {r : ℕ} (a b : Program r) : Program r :=
  equalCode (addCode boundZero a) b

def orderCode {r : ℕ} (a b : Program r) : Program r := exCode (orderBodyCode a b)

def numeralLeBuilder : Program 2 :=
  let m : Program 2 := .proj 0
  let n : Program 2 := .proj 1
  let difference := binary subtraction n m
  ternary existentialIntroductionCertificate (binary additionBuilder difference m)
    (orderBodyCode (num m) (num n)) (num difference)

def orderAtOneCode {r : ℕ} (a b : Program r) : Program r :=
  exCode (equalCode (addCode (syntaxNode 1 [constant 1]) a) b)

def differenceTerm : language.Term (Fin 2) := succTerm (addTerm (.var 0) (.var 1))

def differenceTail : Program 2 := unary predecessor (binary subtraction (.proj 0) (.proj 1))

def differenceTermProof : Program 2 :=
  .comp (termBuilder differenceTerm) ![.proj 1, differenceTail]

def comparisonInstance : Program 2 := instanceTwo strictAdditionComparison
  strictAdditionComparison_derives (num (.proj 1)) (num differenceTail)

def numeralNotLeBuilder : Program 2 :=
  let normalTerm := succCode (addCode (num (.proj 1)) (num differenceTail))
  .comp equalitySubstitutionCertificate ![differenceTermProof, comparisonInstance,
    negCode (orderAtOneCode boundZero (num (.proj 1))), normalTerm, num (.proj 0)]

section Internal
variable {M : Type u} [language.Structure M] [M ⊨ PA]

theorem successor_difference_identity (m n : M) (h : ¬leValue M m n) :
    succValue M (addValue M n (predecessor.value ![subtraction.value ![m, n] ])) = m := by
  have hdiff : subtraction.value ![m, n] ≠ zeroValue M :=
    fun hz => h ((subtraction_zero_iff m n).mp hz)
  obtain ⟨d, hd⟩ := PAComputations.predecessor (subtraction.value ![m, n]) hdiff
  have hp : predecessor.value ![subtraction.value ![m, n] ] = d := by
    rw [hd, predecessor_successor]
  have hnm : leValue M n m := (le_total_value m n).resolve_left h
  have he := (subtraction_spec m n).1 hnm
  rw [hd, successor_add_value, add_comm_value] at he
  rw [hp]
  exact he

def orderBodyValue (a b : M) : M :=
  modelNode 4 [modelNode 2 [numeralValue M 2, modelNode 1 [zeroValue M], a], b]

def orderValue (a b : M) : M := exValue (orderBodyValue a b)

def orderAtOneValue (a b : M) : M := exValue
  (modelNode 4 [modelNode 2 [numeralValue M 2, modelNode 1 [numeralValue M 1], a], b])

theorem modelFormulaCodeAt_equal {α : Type*} (name : α → M) (offset : ℕ)
    (s t : language.Term α) :
    modelFormulaCodeAt name offset (s.equal t) =
      modelNode 4 [modelTermCode name s, modelTermCode name t] := by
  simp only [Term.equal, Term.bdEqual, modelFormulaCodeAt, modelTermCode_relabel,
    Function.comp_def, Sum.elim_inl]

theorem modelFormulaCodeAt_le {α : Type*} (name : α → M)
    (s t : language.Term α) :
    modelFormulaCodeAt name 0 (leFormula s t) =
      orderValue (modelTermCode name s) (modelTermCode name t) := by
  rw [leFormula, modelFormulaCodeAt_iExs_unit]
  simp only [modelFormulaCodeAt_equal, modelTermCode_relabel, Function.comp_def,
    Sum.elim_inl, Sum.elim_inr, modelTermCode, addTerm, CodingFormalProofs.arithFunctionCode,
    List.ofFn_succ, List.ofFn_zero, Fin.succ_zero_eq_one, numeral_value_zero,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  simp only [orderValue, exValue, negValue, implication_node]
  rfl

theorem orderBodyCode_value {r : ℕ} (a b : Program r) (x : Fin r → M) :
    (orderBodyCode a b).value x = orderBodyValue (a.value x) (b.value x) := by
  simp only [orderBodyCode, equalCode_value, addCode, syntaxNode_value, list_cons_value,
    list_nil_value, boundZero, constant_value, numeral_value_zero,
    orderBodyValue, modelNode, modelList_cons, modelList_nil]

theorem orderCode_value {r : ℕ} (a b : Program r) (x : Fin r → M) :
    (orderCode a b).value x = orderValue (a.value x) (b.value x) := by
  rw [orderCode, exCode_value, orderBodyCode_value]
  rfl

theorem orderAtOneCode_value {r : ℕ} (a b : Program r) (x : Fin r → M) :
    (orderAtOneCode a b).value x = orderAtOneValue (a.value x) (b.value x) := by
  simp only [orderAtOneCode, exCode_value, equalCode_value, addCode, syntaxNode_value,
    list_cons_value, list_nil_value, constant_value, orderAtOneValue,
    modelNode, modelList_cons, modelList_nil]

theorem orderBody_bound {a b : M} (ha : PureTerm a) (hb : PureTerm b) :
    FormulaBound 1 (orderBodyValue a b) := by
  apply FormulaBound.equal
  · apply TermBound.binary 2 (Or.inl rfl)
    · simpa only [Fin.val_zero, numeral_value_zero] using TermBound.bound (M := M) 1 (0 : Fin 1)
    · exact ha.termBound 1
  · exact hb.termBound 1

theorem orderValue_pure {a b : M} (ha : PureTerm a) (hb : PureTerm b) :
    PureFormula (orderValue a b) := pure_existential (orderBody_bound ha hb)

theorem orderAtOneHole_bound {b : M} (hb : PureTerm b) :
    FormulaBound 1 (orderAtOneValue (modelNode 1 [zeroValue M]) b) := by
  have hleft : TermBound 2 (modelNode 1 [numeralValue M 1]) := TermBound.bound 2 (1 : Fin 2)
  have hright : TermBound 2 (modelNode 1 [zeroValue M]) := by
    simpa only [Fin.val_zero, numeral_value_zero] using TermBound.bound (M := M) 2 (0 : Fin 2)
  have heq := FormulaBound.equal (TermBound.binary 2 (Or.inl rfl) hleft hright) (hb.termBound 2)
  exact negation_bound (negation_bound heq).all

theorem rewrite_orderAtOneHole {b t : M} (hb : PureTerm b) :
    rewrite.value ![numeralValue M 2, zeroValue M, t,
      orderAtOneValue (modelNode 1 [zeroValue M]) b] = orderValue t b := by
  have hbot : rewrite.value ![numeralValue M 2, zeroValue M, t, modelNode 3 [] ] =
      modelNode 3 ([] : List M) := by
    rw [rewrite_slot_nonleaf_value 3 (by decide) (by decide) (by decide)]
    rfl
  have hbound : rewrite.value ![numeralValue M 2, zeroValue M, t,
      modelNode 1 [numeralValue M 1] ] = modelNode 1 [zeroValue M] := by
    have hn : numeralValue M 1 = succValue M (zeroValue M) := by
      rw [numeral_value_succ, numeral_value_zero]
    rw [hn, rewrite_slot_bound_successor_value]
  simp only [orderAtOneValue, exValue, negValue, implication_node]
  rw [rewrite_slot_imp_value, rewrite_slot_all_value, rewrite_slot_imp_value,
    rewrite_slot_equal_value,
    rewrite_slot_nonleaf_value 2 (by decide) (by decide) (by decide)]
  change modelNode 6 [modelNode 7 [modelNode 6 [modelNode 4
    [modelNode 2 [numeralValue M 2,
      rewrite.value ![numeralValue M 2, zeroValue M, t, modelNode 1 [numeralValue M 1] ],
      rewrite.value ![numeralValue M 2, zeroValue M, t, modelNode 1 [zeroValue M] ] ],
      rewrite.value ![numeralValue M 2, zeroValue M, t, b] ],
      rewrite.value ![numeralValue M 2, zeroValue M, t, modelNode 3 [] ] ] ],
      rewrite.value ![numeralValue M 2, zeroValue M, t, modelNode 3 [] ] ] = _
  rw [hbound, rewrite_slot_bound_zero_value, hb.2, hbot]
  simp only [orderValue, orderBodyValue, exValue, negValue, implication_node]

theorem instantiate_negated_orderHole {b t : M} (hb : PureTerm b) (ht : PureTerm t) :
    instantiate.value ![negValue (orderAtOneValue (modelNode 1 [zeroValue M]) b), t] =
      negValue (orderValue t b) := by
  rw [instantiate_value_of_tests _ _ (negation_bound (orderAtOneHole_bound hb)).namedForm ht.namedTerm]
  simp only [negValue, implication_node]
  rw [rewrite_slot_imp_value, rewrite_orderAtOneHole hb,
    rewrite_slot_nonleaf_value 3 (by decide) (by decide) (by decide)]
  rfl

theorem instantiate_orderBody {a b t : M} (ha : PureTerm a) (hb : PureTerm b) (ht : PureTerm t) :
    instantiate.value ![orderBodyValue a b, t] =
      modelNode 4 [modelNode 2 [numeralValue M 2, t, a], b] := by
  rw [instantiate_value_of_tests _ _ (orderBody_bound ha hb).namedForm ht.namedTerm]
  rw [orderBodyValue, rewrite_slot_equal_value,
    rewrite_slot_nonleaf_value 2 (by decide) (by decide) (by decide)]
  change modelNode 4 [modelNode 2 [numeralValue M 2,
    rewrite.value ![numeralValue M 2, zeroValue M, t, modelNode 1 [zeroValue M] ],
    rewrite.value ![numeralValue M 2, zeroValue M, t, a] ],
    rewrite.value ![numeralValue M 2, zeroValue M, t, b] ] = _
  rw [rewrite_slot_bound_zero_value, ha.2, hb.2]

theorem certified_order_witness (E : Program 2) (p a b t : M)
    (ha : PureTerm a) (hb : PureTerm b) (ht : PureTerm t)
    (hp : Certified E p (modelNode 4 [modelNode 2 [numeralValue M 2, t, a], b])) :
    Certified E (existentialIntroductionCertificate.value ![p, orderBodyValue a b, t])
      (orderValue a b) := by
  have hinst := instantiate_orderBody ha hb ht
  have hp' : Certified E p (instantiate.value ![orderBodyValue a b, t]) := hinst.symm ▸ hp
  exact certified_exIntro E p _ t hp' (orderBody_bound ha hb).namedForm ht.namedTerm
    (orderValue_pure ha hb).sentence

theorem numeralLeBuilder_value (m n : M) :
    numeralLeBuilder.value ![m, n] = existentialIntroductionCertificate.value
      ![additionBuilder.value ![subtraction.value ![n, m], m],
        orderBodyValue (ProofPrograms.numeral.value ![m]) (ProofPrograms.numeral.value ![n]),
        ProofPrograms.numeral.value ![subtraction.value ![n, m] ] ] := by
  simp only [numeralLeBuilder, ternary_value, binary_value, unary_value, num,
    orderBodyCode_value, Program.value_proj, Matrix.cons_val_zero, Matrix.cons_val_one]

theorem certified_numeralLeBuilder {N : Type} [language.Structure N] [N ⊨ PA]
    (m n : N) (hle : leValue N m n) :
    Certified axiomVerifier (numeralLeBuilder.value ![m, n])
      (orderValue (ProofPrograms.numeral.value ![m]) (ProofPrograms.numeral.value ![n])) := by
  rw [numeralLeBuilder_value]
  apply certified_order_witness axiomVerifier _ _ _ _
    (PureTerm.numeral m) (PureTerm.numeral n) (PureTerm.numeral _)
  have hp := certified_additionBuilder (subtraction.value ![n, m]) m
  have hsum : addValue N (subtraction.value ![n, m]) m = n :=
    (subtraction_spec n m).1 hle
  rw [hsum] at hp
  exact hp

end Internal

section InternalZero
variable {M : Type} [language.Structure M] [M ⊨ PA]

theorem differenceTermProof_value (m n : M) :
    differenceTermProof.value ![m, n] =
      (termBuilder differenceTerm).value ![n, predecessor.value ![subtraction.value ![m, n] ] ] := by
  rw [differenceTermProof, Program.value_comp]
  congr 1
  funext i
  fin_cases i <;> simp [Program.value_proj, differenceTail, unary_value, binary_value]

theorem differenceTerm_instance (n d : M) :
    (termInstance differenceTerm).value ![n, d] =
      successorSyntax (additionSyntax (numeralSyntax n) (numeralSyntax d)) := by
  rw [termInstance_model_value]
  simp only [differenceTerm, succTerm, addTerm, modelTermCode,
    CodingFormalProofs.arithFunctionCode, List.ofFn_succ, List.ofFn_zero,
    Matrix.cons_val_zero, Matrix.cons_val_one, Fin.succ_zero_eq_one,
    successorSyntax, additionSyntax]

theorem certified_differenceTermProof {N : Type} [language.Structure N] [N ⊨ PA]
    (m n : N) (h : ¬leValue N m n) :
    Certified axiomVerifier (differenceTermProof.value ![m, n])
      (modelNode 4 [successorSyntax (additionSyntax (numeralSyntax n)
        (numeralSyntax (predecessor.value ![subtraction.value ![m, n] ]))), numeralSyntax m]) := by
  rw [differenceTermProof_value]
  have hp := certified_termBuilder differenceTerm
    (![n, predecessor.value ![subtraction.value ![m, n] ] ] : Fin 2 → N)
  rw [termEquationCode_model_value, differenceTerm_instance, termValue_value] at hp
  simp only [differenceTerm, realize_succTerm, realize_addTerm, Term.realize_var,
    Matrix.cons_val_zero, Matrix.cons_val_one] at hp
  rw [successor_difference_identity m n h] at hp
  exact hp

theorem strictAdditionComparison_model (a b : M) :
    modelFormulaCodeAt (![a, b] : Fin 2 → M) 0 strictAdditionComparison =
      negValue (orderValue (successorSyntax (additionSyntax a b)) a) := by
  change modelNode 6 [modelFormulaCodeAt (![a, b] : Fin 2 → M) 0
    (leFormula (succTerm (addTerm (.var 0) (.var 1))) (.var 0)), modelNode 3 [] ] = _
  rw [modelFormulaCodeAt_le]
  simp only [modelTermCode, succTerm, addTerm, CodingFormalProofs.arithFunctionCode,
    List.ofFn_succ, List.ofFn_zero, Matrix.cons_val_zero, Matrix.cons_val_one,
    Fin.succ_zero_eq_one, successorSyntax, additionSyntax, negValue, implication_node]

theorem certified_comparisonInstance {N : Type} [language.Structure N] [N ⊨ PA]
    (m n : N) :
    Certified axiomVerifier (comparisonInstance.value ![m, n])
      (negValue (orderValue (successorSyntax (additionSyntax (numeralSyntax n)
        (numeralSyntax (predecessor.value ![subtraction.value ![m, n] ])))) (numeralSyntax n))) := by
  have hp := certified_instanceTwo strictAdditionComparison strictAdditionComparison_derives
    (num (Program.proj (1 : Fin 2))) (num differenceTail) (![m, n] : Fin 2 → N)
    (by simpa only [num_model_value, Program.value_proj, Matrix.cons_val_one, Matrix.cons_val_zero,
        numeralSyntax] using
      PureTerm.numeral (M := N) n)
    (by rw [num_model_value]; exact PureTerm.numeral _)
  rw [strictAdditionComparison_model] at hp
  simpa only [comparisonInstance, num_model_value, Program.value_proj,
    Matrix.cons_val_zero, Matrix.cons_val_one, differenceTail, unary_value, binary_value] using hp

theorem numeralNotLeBuilder_value (m n : M) :
    numeralNotLeBuilder.value ![m, n] = equalitySubstitutionCertificate.value
      ![differenceTermProof.value ![m, n], comparisonInstance.value ![m, n],
        negValue (orderAtOneValue (modelNode 1 [zeroValue M]) (numeralSyntax n)),
        successorSyntax (additionSyntax (numeralSyntax n)
          (numeralSyntax (predecessor.value ![subtraction.value ![m, n] ]))), numeralSyntax m] := by
  rw [numeralNotLeBuilder, Program.value_comp]
  congr 1
  funext i
  fin_cases i <;>
    simp [Program.value_proj, negCode_value, orderAtOneCode_value, boundZero,
      syntaxNode_value, list_cons_value, list_nil_value, constant_value, numeral_value_zero,
      num_model_value, succCode_model_value, addCode_model_value, differenceTail,
      unary_value, binary_value, modelNode, modelList_cons, modelList_nil]

theorem certified_numeralNotLeBuilder {N : Type} [language.Structure N] [N ⊨ PA]
    (m n : N) (h : ¬leValue N m n) :
    Certified axiomVerifier (numeralNotLeBuilder.value ![m, n])
      (negValue (orderValue (numeralSyntax m) (numeralSyntax n))) := by
  let normal := successorSyntax (additionSyntax (numeralSyntax n)
    (numeralSyntax (predecessor.value ![subtraction.value ![m, n] ])))
  have hn : PureTerm (numeralSyntax n) := PureTerm.numeral n
  have hm : PureTerm (numeralSyntax m) := PureTerm.numeral m
  have hnormal : PureTerm normal :=
    (PureTerm.binary 2 (Or.inl rfl) hn (PureTerm.numeral _)).succ
  let body := negValue (orderAtOneValue (modelNode 1 [zeroValue N]) (numeralSyntax n))
  have hsrc : instantiate.value ![body, normal] = negValue (orderValue normal (numeralSyntax n)) :=
    instantiate_negated_orderHole hn hnormal
  have htgt : instantiate.value ![body, numeralSyntax m] =
      negValue (orderValue (numeralSyntax m) (numeralSyntax n)) := instantiate_negated_orderHole hn hm
  have hq := certified_comparisonInstance m n
  have hq' : Certified axiomVerifier (comparisonInstance.value ![m, n])
      (instantiate.value ![body, normal]) := hsrc.symm ▸ hq
  have hout : isSentence.value ![instantiate.value ![body, numeralSyntax m] ] =
      numeralValue N 1 := by
    rw [htgt]
    exact (pure_negation (orderValue_pure hm hn)).sentence
  rw [numeralNotLeBuilder_value]
  have hc := certified_equalitySubstitution axiomVerifier
    (differenceTermProof.value ![m, n]) (comparisonInstance.value ![m, n]) body normal (numeralSyntax m)
    (certified_differenceTermProof m n h) hq'
    (negation_bound (orderAtOneHole_bound hn)).namedForm hnormal.namedTerm hm.namedTerm hout
  simpa only [htgt] using hc

end InternalZero
end
end Lemmatheca.ProofTheory.PAComputations.ProofPrograms.CheckerPrograms.NumericalProofs
