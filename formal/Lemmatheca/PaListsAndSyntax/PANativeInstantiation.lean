import Lemmatheca.PaListsAndSyntax.PANativeSyntaxCorrectness
import Lemmatheca.PaListsAndSyntax.PANumeralSyntax
import Lemmatheca.PaListsAndSyntax.PAProofOccurrence

open Lemmatheca.MathematicalLogic Lemmatheca.ModelTheory Lemmatheca.ComputabilityTheory

/-! The actual bound-slot instantiation program, including numeral invariance
and the syntax tests needed by the native proof constructors. -/
namespace Lemmatheca.ProofTheory.PAComputations.ProofPrograms
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic ArithmeticTheories ArithmeticRepresentability
noncomputable section
universe u
variable {M : Type u} [language.Structure M] [M ⊨ PA]
local instance nativeInstantiationLocalInstance1 : DecidableEq M := Classical.decEq M
local instance nativeInstantiationLocalInstance2 (P : Prop) : Decidable P := Classical.propDecidable P

namespace SyntaxPrograms

theorem rewriteStep_slot_value (i t e hist : M) :
    rewriteStep.value ![numeralValue M 2, i, t, e, hist] =
      if e = zeroValue M then zeroValue M else
      if tag.value ![e] = numeralValue M 0 then e else
      if tag.value ![e] = numeralValue M 8 then e else
      if tag.value ![e] = numeralValue M 1 then
        (if listHead.value ![args.value ![e] ] = zeroValue M then t else
          modelNode 1 [predecessor.value ![listHead.value ![args.value ![e] ] ] ]) else
      listCons.value ![tag.value ![e],
        if tag.value ![e] = numeralValue M 2 ∨ tag.value ![e] = numeralValue M 5 then
          listCons.value ![listHead.value ![args.value ![e] ],
            (listMap listEntry).value ![hist, listTail.value ![args.value ![e] ] ] ]
        else (listMap listEntry).value ![hist, args.value ![e] ] ] := by
  simp only [rewriteStep, ternary_value, binary_value, unary_value,
    Program.value_proj, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, constant_value,
    equalTest_truthValue, multiplication_value, multiplication_truthValue,
    disjoin_truthValue, numeral_eq_iff_model, Nat.reduceEqDiff,
    ↓reduceIte, false_and, select_value, truthValue_eq_zero_iff, ite_not]
  simp only [numeral_value_zero, modelNode, modelList_cons, modelList_nil]
  rfl

theorem rewrite_slot_free_name_value (i t a : M) :
    rewrite.value ![numeralValue M 2, i, t, modelNode 0 [a] ] = modelNode 0 [a] := by
  rw [rewrite_equation_value, rewriteStep_slot_value]
  simp only [modelNode_ne_zero, tag_modelNode_value, ↓reduceIte]

theorem rewrite_slot_aux_name_value (i t a : M) :
    rewrite.value ![numeralValue M 2, i, t, modelNode 8 [a] ] = modelNode 8 [a] := by
  rw [rewrite_equation_value, rewriteStep_slot_value]
  simp only [modelNode_ne_zero, tag_modelNode_value, numeral_eq_iff_model,
    Nat.reduceEqDiff, ↓reduceIte]

theorem rewrite_slot_bound_name_value (i t a : M) :
    rewrite.value ![numeralValue M 2, i, t, modelNode 1 [a] ] =
      if a = zeroValue M then t else modelNode 1 [predecessor.value ![a] ] := by
  rw [rewrite_equation_value, rewriteStep_slot_value]
  simp only [modelNode_ne_zero, tag_modelNode_value, args_modelNode_value,
    modelList_cons, head_cons_value, numeral_eq_iff_model, Nat.reduceEqDiff, ↓reduceIte]

theorem rewrite_slot_bound_zero_value (i t : M) :
    rewrite.value ![numeralValue M 2, i, t, modelNode 1 [zeroValue M] ] = t := by
  rw [rewrite_slot_bound_name_value, ite_eq_left rfl]

theorem rewrite_slot_bound_successor_value (i t a : M) :
    rewrite.value ![numeralValue M 2, i, t, modelNode 1 [succValue M a] ] = modelNode 1 [a] := by
  rw [rewrite_slot_bound_name_value, ite_eq_right (successor_ne_zero a), predecessor_successor]

theorem rewrite_slot_nonleaf_value (k : ℕ) (hk0 : k ≠ 0) (hk1 : k ≠ 1) (hk8 : k ≠ 8)
    (i t : M) (xs : List M) :
    rewrite.value ![numeralValue M 2, i, t, modelNode k xs] =
      modelNode k (if k = 2 ∨ k = 5 then
        xs.headD (zeroValue M) :: xs.tail.map (fun a => rewrite.value ![numeralValue M 2, i, t, a])
      else xs.map (fun a => rewrite.value ![numeralValue M 2, i, t, a])) := by
  let hist := (history rewriteStep).value ![numeralValue M 2, i, t, modelNode k xs]
  have hmap : (listMap listEntry).value ![hist, modelList xs] =
      modelList (xs.map (fun a => rewrite.value ![numeralValue M 2, i, t, a])) :=
    listMap_rewrite_history_value _ _ _ _ _ (modelNode_child_smaller k xs)
  have hmaptail : (listMap listEntry).value ![hist, modelList xs.tail] =
      modelList (xs.tail.map (fun a => rewrite.value ![numeralValue M 2, i, t, a])) :=
    listMap_rewrite_history_value _ _ _ _ _
      (fun a ha => modelNode_child_smaller k xs a (List.mem_of_mem_tail ha))
  rw [rewrite_equation_value, rewriteStep_slot_value]
  simp only [modelNode_ne_zero, tag_modelNode_value, args_modelNode_value,
    numeral_eq_iff_model, hk0, hk1, hk8, ↓reduceIte,
    modelList_head_value, modelList_tail_value]
  change listCons.value ![numeralValue M k,
    (if k = 2 ∨ k = 5 then listCons.value ![xs.headD (zeroValue M),
      (listMap listEntry).value ![hist, modelList xs.tail] ]
    else (listMap listEntry).value ![hist, modelList xs])] = _
  rw [hmaptail, hmap]
  split_ifs <;> rfl

theorem rewrite_slot_numeral_value (i t n : M) :
    rewrite.value ![numeralValue M 2, i, t, ProofPrograms.numeral.value ![n] ] =
      ProofPrograms.numeral.value ![n] := by
  apply definable_induction
    (fun n => rewrite.value ![numeralValue M 2, i, t, ProofPrograms.numeral.value ![n] ] =
      ProofPrograms.numeral.value ![n])
  · change DPred (fun v : Fin 1 → M =>
      rewrite.value ![numeralValue M 2, i, t, ProofPrograms.numeral.value ![v 0] ] =
        ProofPrograms.numeral.value ![v 0])
    pa_definable
  · rw [numeral_zero_modelNode_value, rewrite_slot_nonleaf_value 2 (by decide) (by decide) (by decide)]
    rfl
  · intro n hn
    rw [numeral_successor_modelNode_value,
      rewrite_slot_nonleaf_value 2 (by decide) (by decide) (by decide)]
    change modelNode 2 [numeralValue M 1,
      rewrite.value ![numeralValue M 2, i, t, ProofPrograms.numeral.value ![n] ] ] = _
    rw [hn]

theorem rewrite_slot_equal_value (i t a b : M) :
    rewrite.value ![numeralValue M 2, i, t, modelNode 4 [a, b] ] =
      modelNode 4 [rewrite.value ![numeralValue M 2, i, t, a],
        rewrite.value ![numeralValue M 2, i, t, b] ] := by
  rw [rewrite_slot_nonleaf_value 4 (by decide) (by decide) (by decide)]
  rfl

theorem rewrite_slot_imp_value (i t a b : M) :
    rewrite.value ![numeralValue M 2, i, t, modelNode 6 [a, b] ] =
      modelNode 6 [rewrite.value ![numeralValue M 2, i, t, a],
        rewrite.value ![numeralValue M 2, i, t, b] ] := by
  rw [rewrite_slot_nonleaf_value 6 (by decide) (by decide) (by decide)]
  rfl

theorem rewrite_slot_all_value (i t a : M) :
    rewrite.value ![numeralValue M 2, i, t, modelNode 7 [a] ] =
      modelNode 7 [rewrite.value ![numeralValue M 2, i, t, a] ] := by
  rw [rewrite_slot_nonleaf_value 7 (by decide) (by decide) (by decide)]
  rfl

end SyntaxPrograms

namespace CheckerPrograms
open SyntaxPrograms

theorem instantiate_value_of_tests (b t : M)
    (hb : namedForm.value ![numeralValue M 1, b] = numeralValue M 1)
    (ht : namedTerm.value ![t] = numeralValue M 1) :
    instantiate.value ![b, t] = rewrite.value ![numeralValue M 2, zeroValue M, t, b] := by
  simp only [instantiate, ternary_value, binary_value, unary_value, Program.value_proj,
    Matrix.cons_val_zero, Matrix.cons_val_one, constant_value, hb, ht,
    multiplication_value, numeral_one_mul_model, select_value,
    numeral_eq_zero_iff_model, Nat.one_ne_zero, ↓reduceIte, Program.value_comp,
    numeral_value_zero]
  congr 1
  funext i
  fin_cases i <;> simp [Program.value_proj, constant_value]

theorem namedTerm_value (e : M) :
    namedTerm.value ![e] = truthValue (M := M)
      ((termDepth e ≠ zeroValue M ∧ leValue M (termDepth e) (succValue M (zeroValue M))) ∧
        (part 2).value ![stats.value ![e] ] = zeroValue M) := by
  simp only [namedTerm, binary_value, unary_value, Program.value_proj,
    Matrix.cons_val_zero, isTerm_value, booleanNot_value,
    multiplication_value, constant_value, numeral_value_zero]
  change mulValue M (truthValue _) (truthValue _) = _
  exact multiplication_truthValue _ _

theorem namedTerm_of_stats (e av : M)
    (hs : stats.value ![e] = modelSummary (numeralValue M 1) (zeroValue M) (zeroValue M) av) :
    namedTerm.value ![e] = numeralValue M 1 := by
  rw [namedTerm_value]
  apply (truthValue_eq_one_iff (M := M) _).mpr
  simp only [termDepth, hs, modelSummary_part_value,
    Matrix.cons_val_zero, Matrix.cons_val_two, numeral_value_succ, numeral_value_zero]
  exact ⟨⟨successor_ne_zero _, le_refl_value _⟩, rfl⟩

theorem namedForm_of_stats (n e fd av : M)
    (hs : stats.value ![e] = modelSummary (zeroValue M) fd (zeroValue M) av)
    (hfd : fd ≠ zeroValue M) (hb : leValue M fd (succValue M n)) :
    namedForm.value ![n, e] = numeralValue M 1 := by
  rw [namedForm_value]
  apply (truthValue_eq_one_iff (M := M) _).mpr
  have hFD : formDepth e = fd := by
    simp only [formDepth, hs, modelSummary_part_value, Matrix.cons_val_one, Matrix.cons_val_zero]
  have hFV : (part 2).value ![stats.value ![e] ] = zeroValue M := by
    simp only [hs, modelSummary_part_value, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  exact ⟨⟨by rwa [hFD], by rwa [hFD]⟩, hFV⟩

theorem isSentence_value (e : M) :
    isSentence.value ![e] = truthValue (M := M)
      (((formDepth e ≠ zeroValue M ∧ leValue M (formDepth e) (succValue M (zeroValue M))) ∧
        (part 2).value ![stats.value ![e] ] = zeroValue M) ∧
        (part 3).value ![stats.value ![e] ] = zeroValue M) := by
  simp only [isSentence, binary_value, unary_value, Program.value_proj,
    Matrix.cons_val_zero, namedForm_value, booleanNot_value,
    multiplication_value, constant_value, numeral_value_zero]
  change mulValue M (truthValue _) (truthValue _) = _
  exact multiplication_truthValue _ _

theorem isSentence_of_stats (e : M)
    (hs : stats.value ![e] = modelSummary (zeroValue M) (numeralValue M 1)
      (zeroValue M) (zeroValue M)) :
    isSentence.value ![e] = numeralValue M 1 := by
  rw [isSentence_value]
  apply (truthValue_eq_one_iff (M := M) _).mpr
  simp only [formDepth, hs, modelSummary_part_value,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    numeral_value_succ, numeral_value_zero]
  exact ⟨⟨⟨successor_ne_zero _, le_refl_value _⟩, rfl⟩, rfl⟩

theorem namedForm_mono (n m e : M) (hnm : leValue M n m)
    (he : namedForm.value ![n, e] = numeralValue M 1) :
    namedForm.value ![m, e] = numeralValue M 1 := by
  rw [namedForm_value] at he ⊢
  have hp := (truthValue_eq_one_iff (M := M) _).mp he
  apply (truthValue_eq_one_iff (M := M) _).mpr
  exact ⟨⟨hp.1.1, le_trans_value hp.1.2
    ((successor_le_successor_value_iff _ _).mpr hnm)⟩, hp.2⟩

theorem isSentence_namedForm_any (n e : M)
    (he : isSentence.value ![e] = numeralValue M 1) :
    namedForm.value ![n, e] = numeralValue M 1 :=
  namedForm_mono _ _ _ (zero_le_value n) (isSentence_namedForm e he)

theorem namedTerm_isTerm (e : M) (he : namedTerm.value ![e] = numeralValue M 1) :
    isTerm.value ![zeroValue M, e] = numeralValue M 1 := by
  rw [namedTerm_value] at he
  have hp := (truthValue_eq_one_iff (M := M) _).mp he
  rw [isTerm_value]
  exact (truthValue_eq_one_iff (M := M) _).mpr hp.1

end CheckerPrograms
end
end Lemmatheca.ProofTheory.PAComputations.ProofPrograms
