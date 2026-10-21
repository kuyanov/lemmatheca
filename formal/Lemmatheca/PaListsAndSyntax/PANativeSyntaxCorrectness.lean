import Lemmatheca.PaListsAndSyntax.PANativeSyntaxRecurrences
import Lemmatheca.PaListsAndSyntax.PANativeSyntaxRecognition

open Lemmatheca.MathematicalLogic Lemmatheca.ModelTheory Lemmatheca.ComputabilityTheory

/-! Substitution preservation for the actual arithmetic syntax programs, at
all codes of arbitrary PA models.  The induction predicates are definable and
the recursive calls are justified by strict bounds on numerical child codes. -/
namespace Lemmatheca.ProofTheory.PAComputations.ProofPrograms.SyntaxPrograms
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic ArithmeticTheories ArithmeticRepresentability
noncomputable section
universe u
variable {M : Type u} [language.Structure M] [M ⊨ PA]
local instance nativeSyntaxCorrectnessLocalInstance1 : DecidableEq M := Classical.decEq M
local instance nativeSyntaxCorrectnessLocalInstance2 (P : Prop) : Decidable P := Classical.propDecidable P

theorem listMap_rewrite_history_value (mode i t e : M) (xs : List M)
    (hxs : ∀ a ∈ xs, leValue M (succValue M a) e) :
    (listMap listEntry).value ![(history rewriteStep).value ![mode, i, t, e], modelList xs] =
      modelList (xs.map (fun a => rewrite.value ![mode, i, t, a])) := by
  induction xs with
  | nil => rw [modelList_nil, listMap_zero_value]; rfl
  | cons a xs ih =>
      rw [modelList_cons, listMap_cons_value,
        rewrite_history_entry_value mode i t e a (hxs a (List.mem_cons_self)),
        ih (fun b hb => hxs b (List.mem_cons_of_mem _ hb))]
      rfl

theorem rewriteStep_free_value (i t e hist : M) :
    rewriteStep.value ![zeroValue M, i, t, e, hist] =
      if e = zeroValue M then zeroValue M else
      if tag.value ![e] = numeralValue M 0 then
        (if listHead.value ![args.value ![e] ] = i then t else e) else
      if tag.value ![e] = numeralValue M 8 then e else
      if tag.value ![e] = numeralValue M 1 then e else
      listCons.value ![tag.value ![e],
        if tag.value ![e] = numeralValue M 2 ∨ tag.value ![e] = numeralValue M 5 then
          listCons.value ![listHead.value ![args.value ![e] ],
            (listMap listEntry).value ![hist, listTail.value ![args.value ![e] ] ] ]
        else (listMap listEntry).value ![hist, args.value ![e] ] ] := by
  simp only [rewriteStep, ternary_value, binary_value, unary_value,
    Program.value_proj, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, constant_value,
    equalTest_truthValue, multiplication_value, multiplication_truthValue,
    disjoin_truthValue, numeral_value_zero,
    zero_eq_numeral_iff_model, Nat.one_ne_zero, ↓reduceIte, false_and, true_and,
    select_value, truthValue_eq_zero_iff, ite_not]
  simp only [show (2 : ℕ) ≠ 0 from by decide, ↓reduceIte]
  rfl

theorem rewrite_free_name_value (i t a : M) :
    rewrite.value ![zeroValue M, i, t, modelNode 0 [a] ] =
      if a = i then t else modelNode 0 [a] := by
  have htag : tag.value ![modelNode 0 [a] ] = numeralValue M 0 := tag_node_value _ _
  have hargs : args.value ![modelNode 0 [a] ] = modelList [a] := args_node_value _ _
  rw [rewrite_equation_value, rewriteStep_free_value]
  simp only [modelNode_ne_zero, htag, hargs,
    ↓reduceIte, modelList_cons, head_cons_value]

theorem rewrite_bound_name_value (i t a : M) :
    rewrite.value ![zeroValue M, i, t, modelNode 1 [a] ] = modelNode 1 [a] := by
  have htag : tag.value ![modelNode 1 [a] ] = numeralValue M 1 := tag_node_value _ _
  rw [rewrite_equation_value, rewriteStep_free_value]
  simp only [modelNode_ne_zero, htag, numeral_eq_iff_model, ↓reduceIte]
  rfl

theorem rewrite_aux_name_value (i t a : M) :
    rewrite.value ![zeroValue M, i, t, modelNode 8 [a] ] = modelNode 8 [a] := by
  have htag : tag.value ![modelNode 8 [a] ] = numeralValue M 8 := tag_node_value _ _
  rw [rewrite_equation_value, rewriteStep_free_value]
  simp only [modelNode_ne_zero, htag, numeral_eq_iff_model, ↓reduceIte]
  rfl

theorem rewrite_nonleaf_value (k : ℕ) (hk0 : k ≠ 0) (hk1 : k ≠ 1) (hk8 : k ≠ 8)
    (i t : M) (xs : List M) :
    rewrite.value ![zeroValue M, i, t, modelNode k xs] =
      modelNode k (if k = 2 ∨ k = 5 then
        xs.headD (zeroValue M) :: xs.tail.map (fun a => rewrite.value ![zeroValue M, i, t, a])
      else xs.map (fun a => rewrite.value ![zeroValue M, i, t, a])) := by
  let hist := (history rewriteStep).value ![zeroValue M, i, t, modelNode k xs]
  have htag : tag.value ![modelNode k xs] = numeralValue M k := tag_node_value _ _
  have hargs : args.value ![modelNode k xs] = modelList xs := args_node_value _ _
  have hhead : listHead.value ![modelList xs] = xs.headD (zeroValue M) := by
    cases xs with
    | nil => exact head_zero_value
    | cons a xs => exact head_cons_value a _
  have htail : listTail.value ![modelList xs] = modelList xs.tail := by
    cases xs with
    | nil => exact tail_zero_value
    | cons a xs => exact tail_cons_value a _
  have hmap : (listMap listEntry).value ![hist, modelList xs] =
      modelList (xs.map (fun a => rewrite.value ![zeroValue M, i, t, a])) :=
    listMap_rewrite_history_value _ _ _ _ _ (modelNode_child_smaller k xs)
  have hmaptail : (listMap listEntry).value ![hist, modelList xs.tail] =
      modelList (xs.tail.map (fun a => rewrite.value ![zeroValue M, i, t, a])) :=
    listMap_rewrite_history_value _ _ _ _ _
      (fun a ha => modelNode_child_smaller k xs a (List.mem_of_mem_tail ha))
  rw [rewrite_equation_value, rewriteStep_free_value]
  simp only [modelNode_ne_zero, htag, hargs, numeral_eq_iff_model, hk0, hk1, hk8,
    ↓reduceIte, hhead, htail]
  change listCons.value ![numeralValue M k,
    (if k = 2 ∨ k = 5 then listCons.value ![xs.headD (zeroValue M),
      (listMap listEntry).value ![hist, modelList xs.tail] ]
    else (listMap listEntry).value ![hist, modelList xs])] = _
  rw [hmaptail, hmap]
  split_ifs <;> rfl

theorem substitute_value_of_tests (n e i t : M)
    (he : isForm.value ![n, e] = numeralValue M 1)
    (ht : isTerm.value ![zeroValue M, t] = numeralValue M 1) :
    substitute.value ![n, e, i, t] = rewrite.value ![zeroValue M, i, t, e] := by
  have hv : (Program.comp rewrite ![constant 0, Program.proj (2 : Fin 4),
      Program.proj 3, Program.proj 1]).value ![n, e, i, t] =
        rewrite.value ![zeroValue M, i, t, e] := by
    rw [Program.value_comp]
    congr 1
    funext j
    fin_cases j
    · change (constant 0 : Program 4).value ![n, e, i, t] = zeroValue M
      rw [constant_value, numeral_value_zero]
    · change (Program.proj (2 : Fin 4)).value ![n, e, i, t] = i
      exact Program.value_proj _ _
    · change (Program.proj (3 : Fin 4)).value ![n, e, i, t] = t
      exact Program.value_proj _ _
    · change (Program.proj (1 : Fin 4)).value ![n, e, i, t] = e
      exact Program.value_proj _ _
  simp only [substitute, ternary_value, binary_value, Program.value_proj,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons, constant_value, numeral_value_zero, multiplication_value,
    he, ht, numeral_one_mul_model, select_value, numeral_eq_zero_iff_model,
    Nat.one_ne_zero, ↓reduceIte, hv]

theorem substitute_preserves_of_depth_equation (n e i t : M)
    (he : isForm.value ![n, e] = numeralValue M 1)
    (ht : isTerm.value ![zeroValue M, t] = numeralValue M 1)
    (hdepth : formDepth (rewrite.value ![zeroValue M, i, t, e]) = formDepth e) :
    isForm.value ![n, substitute.value ![n, e, i, t] ] = numeralValue M 1 := by
  rw [substitute_value_of_tests n e i t he ht, isForm_value, hdepth]
  rwa [isForm_value] at he

theorem rewrite_succ_depth_value (i t a : M)
    (ha : termDepth (rewrite.value ![zeroValue M, i, t, a]) = termDepth a) :
    termDepth (rewrite.value ![zeroValue M, i, t, modelNode 2 [numeralValue M 1, a] ]) =
      termDepth (modelNode 2 [numeralValue M 1, a]) := by
  have hr : rewrite.value ![zeroValue M, i, t, modelNode 2 [numeralValue M 1, a] ] =
      modelNode 2 [numeralValue M 1, rewrite.value ![zeroValue M, i, t, a] ] := by
    rw [rewrite_nonleaf_value 2 (by decide) (by decide) (by decide)]
    rfl
  rw [hr, termDepth_succ_modelNode_value, termDepth_succ_modelNode_value, ha]

theorem rewrite_binary_depth_value (f : ℕ) (hf : f = 2 ∨ f = 3) (i t a b : M)
    (ha : termDepth (rewrite.value ![zeroValue M, i, t, a]) = termDepth a)
    (hb : termDepth (rewrite.value ![zeroValue M, i, t, b]) = termDepth b) :
    termDepth (rewrite.value ![zeroValue M, i, t, modelNode 2 [numeralValue M f, a, b] ]) =
      termDepth (modelNode 2 [numeralValue M f, a, b]) := by
  have hr : rewrite.value ![zeroValue M, i, t, modelNode 2 [numeralValue M f, a, b] ] =
      modelNode 2 [numeralValue M f, rewrite.value ![zeroValue M, i, t, a],
        rewrite.value ![zeroValue M, i, t, b] ] := by
    rw [rewrite_nonleaf_value 2 (by decide) (by decide) (by decide)]
    rfl
  rw [hr, termDepth_binary_modelNode_value f hf, termDepth_binary_modelNode_value f hf, ha, hb]

theorem rewrite_equal_depth_value (i t a b : M)
    (ha : termDepth (rewrite.value ![zeroValue M, i, t, a]) = termDepth a)
    (hb : termDepth (rewrite.value ![zeroValue M, i, t, b]) = termDepth b) :
    formDepth (rewrite.value ![zeroValue M, i, t, modelNode 4 [a, b] ]) =
      formDepth (modelNode 4 [a, b]) := by
  have hr : rewrite.value ![zeroValue M, i, t, modelNode 4 [a, b] ] =
      modelNode 4 [rewrite.value ![zeroValue M, i, t, a], rewrite.value ![zeroValue M, i, t, b] ] := by
    rw [rewrite_nonleaf_value 4 (by decide) (by decide) (by decide)]
    rfl
  rw [hr, formDepth_equal_modelNode_value, formDepth_equal_modelNode_value, ha, hb]

theorem rewrite_imp_depth_value (i t a b : M)
    (ha : formDepth (rewrite.value ![zeroValue M, i, t, a]) = formDepth a)
    (hb : formDepth (rewrite.value ![zeroValue M, i, t, b]) = formDepth b) :
    formDepth (rewrite.value ![zeroValue M, i, t, modelNode 6 [a, b] ]) =
      formDepth (modelNode 6 [a, b]) := by
  have hr : rewrite.value ![zeroValue M, i, t, modelNode 6 [a, b] ] =
      modelNode 6 [rewrite.value ![zeroValue M, i, t, a], rewrite.value ![zeroValue M, i, t, b] ] := by
    rw [rewrite_nonleaf_value 6 (by decide) (by decide) (by decide)]
    rfl
  rw [hr, formDepth_imp_modelNode_value, formDepth_imp_modelNode_value, ha, hb]

theorem rewrite_all_depth_value (i t a : M)
    (ha : formDepth (rewrite.value ![zeroValue M, i, t, a]) = formDepth a) :
    formDepth (rewrite.value ![zeroValue M, i, t, modelNode 7 [a] ]) =
      formDepth (modelNode 7 [a]) := by
  have hr : rewrite.value ![zeroValue M, i, t, modelNode 7 [a] ] =
      modelNode 7 [rewrite.value ![zeroValue M, i, t, a] ] := by
    rw [rewrite_nonleaf_value 7 (by decide) (by decide) (by decide)]
    rfl
  rw [hr, formDepth_all_modelNode_value, formDepth_all_modelNode_value, ha]

/-- Simultaneous preservation of the two positive depth coordinates under
free-name substitution.  The recursive calls concern strictly smaller actual
codes, including in nonstandard PA models. -/
theorem rewrite_preserves_positive_depth (i t : M)
    (ht : termDepth t = numeralValue M 1) (e : M) :
    (termDepth e ≠ zeroValue M →
      termDepth (rewrite.value ![zeroValue M, i, t, e]) = termDepth e) ∧
    (formDepth e ≠ zeroValue M →
      formDepth (rewrite.value ![zeroValue M, i, t, e]) = formDepth e) := by
  have hall : ∀ e : M,
      (termDepth e ≠ zeroValue M →
        termDepth (rewrite.value ![zeroValue M, i, t, e]) = termDepth e) ∧
      (formDepth e ≠ zeroValue M →
        formDepth (rewrite.value ![zeroValue M, i, t, e]) = formDepth e) := by
    apply definable_strong_induction
      (fun e =>
        (termDepth e ≠ zeroValue M →
          termDepth (rewrite.value ![zeroValue M, i, t, e]) = termDepth e) ∧
        (formDepth e ≠ zeroValue M →
          formDepth (rewrite.value ![zeroValue M, i, t, e]) = formDepth e))
    · change DPred (fun v : Fin 1 → M =>
        (termDepth (v 0) ≠ zeroValue M →
          termDepth (rewrite.value ![zeroValue M, i, t, v 0]) = termDepth (v 0)) ∧
        (formDepth (v 0) ≠ zeroValue M →
          formDepth (rewrite.value ![zeroValue M, i, t, v 0]) = formDepth (v 0)))
      pa_definable
    · intro e ih
      constructor
      · intro he
        rcases termDepth_cases e he with ⟨a, rfl⟩ | ⟨a, rfl⟩ | ⟨a, rfl⟩ | rfl |
          ⟨a, rfl, ha⟩ | ⟨f, hf, a, b, rfl, ha, hb⟩
        · rw [rewrite_free_name_value]
          split_ifs
          · simpa only [termDepth, stats_free_modelNode_value,
              modelSummary_part_value, Matrix.cons_val_zero] using ht
          · rfl
        · rw [rewrite_bound_name_value]
        · rw [rewrite_aux_name_value]
        · have hr : rewrite.value ![zeroValue M, i, t, modelNode 2 [numeralValue M 0] ] =
              modelNode 2 [numeralValue M 0] := by
            rw [rewrite_nonleaf_value 2 (by decide) (by decide) (by decide)]
            rfl
          rw [hr]
        · exact rewrite_succ_depth_value i t a
            ((ih a (modelNode_child_smaller 2 [numeralValue M 1, a] a (by simp))).1 ha)
        · exact rewrite_binary_depth_value f hf i t a b
            ((ih a (modelNode_child_smaller 2 [numeralValue M f, a, b] a (by simp))).1 ha)
            ((ih b (modelNode_child_smaller 2 [numeralValue M f, a, b] b (by simp))).1 hb)
      · intro he
        rcases formDepth_cases e he with rfl | ⟨a, b, rfl, ha, hb⟩ |
          ⟨a, b, rfl, ha, hb⟩ | ⟨a, rfl, ha⟩
        · have hr : rewrite.value ![zeroValue M, i, t, modelNode 3 ([] : List M)] =
              modelNode 3 ([] : List M) := by
            rw [rewrite_nonleaf_value 3 (by decide) (by decide) (by decide)]
            rfl
          rw [hr]
        · exact rewrite_equal_depth_value i t a b
            ((ih a (modelNode_child_smaller 4 [a, b] a (by simp))).1 ha)
            ((ih b (modelNode_child_smaller 4 [a, b] b (by simp))).1 hb)
        · exact rewrite_imp_depth_value i t a b
            ((ih a (modelNode_child_smaller 6 [a, b] a (by simp))).2 ha)
            ((ih b (modelNode_child_smaller 6 [a, b] b (by simp))).2 hb)
        · exact rewrite_all_depth_value i t a
            ((ih a (modelNode_child_smaller 7 [a] a (by simp))).2 ha)
  exact hall e

theorem substitute_preserves (n e i t : M)
    (he : isForm.value ![n, e] = numeralValue M 1)
    (ht : isTerm.value ![zeroValue M, t] = numeralValue M 1) :
    isForm.value ![n, substitute.value ![n, e, i, t] ] = numeralValue M 1 := by
  apply substitute_preserves_of_depth_equation n e i t he ht
  apply (rewrite_preserves_positive_depth i t ((isTerm_closed_iff t).mp ht) e).2
  rw [isForm_value, truthValue_eq_one_iff] at he
  exact he.1

end
end Lemmatheca.ProofTheory.PAComputations.ProofPrograms.SyntaxPrograms
