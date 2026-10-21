import Lemmatheca.PaListsAndSyntax.PANativeSyntaxValues
import Lemmatheca.PaListsAndSyntax.PAHistoryLookup

open Lemmatheca.MathematicalLogic Lemmatheca.ModelTheory Lemmatheca.ComputabilityTheory

/-! Internal constructor equations for the concrete shared-syntax programs.
Every history lookup below has an explicit smaller-code hypothesis. -/
namespace Lemmatheca.ProofTheory.PAComputations.ProofPrograms
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic ArithmeticTheories ArithmeticRepresentability
noncomputable section
universe u
variable {M : Type u} [language.Structure M] [M ⊨ PA]
local instance nativeSyntaxRecurrencesLocalInstance1 : DecidableEq M := Classical.decEq M

theorem foldCons_reverse_value (c : M) :
    (foldInto listCons).value ![(foldInto listCons).value ![c, zeroValue M], zeroValue M] = c := by
  apply list_code_induction
    (fun c => (foldInto listCons).value
      ![(foldInto listCons).value ![c, zeroValue M], zeroValue M] = c)
  · change DPred (fun v : Fin 1 → M => (foldInto listCons).value
      ![(foldInto listCons).value ![v 0, zeroValue M], zeroValue M] = v 0)
    pa_definable
  · rw [foldInto_zero_value, foldInto_zero_value]
  · intro a c ih
    rw [foldInto_cons_value, foldCons_fusion_value, foldInto_cons_value,
      foldInto_zero_value, ih]

theorem listReverse_zero_value : listReverse.value ![zeroValue M] = zeroValue M := by
  rw [listReverse_value, foldInto_zero_value]

theorem listReverse_cons_value (a c : M) :
    listReverse.value ![listCons.value ![a, c] ] =
      listAppend.value ![listReverse.value ![c], listCons.value ![a, zeroValue M] ] := by
  rw [listReverse_value, foldInto_cons_value, listAppend_value, listReverse_value,
    foldCons_reverse_value]

theorem paramFold_append_value (h : Program 3) (p c d z : M) :
    (paramFold h).value ![p, listAppend.value ![c, d], z] =
      (paramFold h).value ![p, d, (paramFold h).value ![p, c, z] ] := by
  have hs : ∀ c : M, ∀ p d z : M,
      (paramFold h).value ![p, listAppend.value ![c, d], z] =
        (paramFold h).value ![p, d, (paramFold h).value ![p, c, z] ] := by
    apply list_code_induction
    · change DPred (fun v : Fin 1 → M => ∀ p d z : M,
        (paramFold h).value ![p, listAppend.value ![v 0, d], z] =
          (paramFold h).value ![p, d, (paramFold h).value ![p, v 0, z] ])
      pa_definable
    · intro p d z
      rw [listAppend_zero_value, paramFold_zero_value]
    · intro a c ih p d z
      rw [listAppend_cons_value, paramFold_cons_value, ih, paramFold_cons_value]
  exact hs c p d z

theorem listLength_zero_iff_value (c : M) :
    listLength.value ![c] = zeroValue M ↔ c = zeroValue M := by
  constructor
  · intro hl
    by_contra hc
    have hd := congrArg (fun d => listLength.value ![d]) (cons_head_tail_value c hc)
    rw [listLength_cons_value, hl] at hd
    exact successor_ne_zero _ hd
  · intro hc
    rw [hc, listLength_zero_value]

theorem listLength_successor_decompose_value (c n : M)
    (hl : listLength.value ![c] = succValue M n) :
    ∃ a t : M, c = listCons.value ![a, t] ∧ listLength.value ![t] = n := by
  have hc : c ≠ zeroValue M := by
    intro hc
    rw [hc, listLength_zero_value] at hl
    exact successor_ne_zero n hl.symm
  have hd := cons_head_tail_value c hc
  refine ⟨listHead.value ![c], listTail.value ![c], hd.symm, ?_⟩
  have ht := congrArg (fun d => listLength.value ![d]) hd
  rw [listLength_cons_value, hl] at ht
  exact successor_injective ht

theorem listLength_one_shape_value (c : M)
    (hl : listLength.value ![c] = numeralValue M 1) :
    c = listCons.value ![listHead.value ![c], zeroValue M] := by
  rw [numeral_value_succ, numeral_value_zero] at hl
  have hc : c ≠ zeroValue M := by
    intro hc
    rw [hc, listLength_zero_value] at hl
    exact successor_ne_zero (zeroValue M) hl.symm
  have hd := cons_head_tail_value c hc
  have ht := congrArg (fun d => listLength.value ![d]) hd
  rw [listLength_cons_value, hl] at ht
  have htz : listLength.value ![listTail.value ![c] ] = zeroValue M := successor_injective ht
  rw [(listLength_zero_iff_value _).mp htz] at hd
  exact hd.symm

theorem listLength_two_shape_value (c : M)
    (hl : listLength.value ![c] = numeralValue M 2) :
    c = listCons.value ![listHead.value ![c],
      listCons.value ![listHead.value ![listTail.value ![c] ], zeroValue M] ] := by
  rw [numeral_value_succ] at hl
  have hc : c ≠ zeroValue M := by
    intro hc
    rw [hc, listLength_zero_value] at hl
    exact successor_ne_zero (numeralValue M 1) hl.symm
  have hd := cons_head_tail_value c hc
  have ht := congrArg (fun d => listLength.value ![d]) hd
  rw [listLength_cons_value, hl] at ht
  have htl : listLength.value ![listTail.value ![c] ] = numeralValue M 1 := successor_injective ht
  rw [listLength_one_shape_value _ htl] at hd
  exact hd.symm

theorem squarePair_left_le_value (a b : M) : leValue M a (squarePair.value ![a, b]) := by
  rw [squarePair_value]
  split_ifs
  · exact ⟨mulValue M b b, rfl⟩
  · refine ⟨addValue M (mulValue M a a) b, ?_⟩
    rw [add_assoc_value, add_comm_value b a, ← add_assoc_value]

theorem head_smaller_value (c : M) (hc : c ≠ zeroValue M) :
    leValue M (succValue M (listHead.value ![c])) c := by
  have hs := (successor_le_successor_value_iff _ _).mpr
    (squarePair_left_le_value (listHead.value ![c]) (listTail.value ![c]))
  rwa [← listCons_value, cons_head_tail_value c hc] at hs

theorem listEntry_smaller_value (c i : M)
    (hi : leValue M (succValue M i) (listLength.value ![c])) :
    leValue M (succValue M (listEntry.value ![c, i])) c := by
  have hs : ∀ c : M, ∀ i : M,
      leValue M (succValue M i) (listLength.value ![c]) →
        leValue M (succValue M (listEntry.value ![c, i])) c := by
    apply list_code_induction
    · change DPred (fun v : Fin 1 → M => ∀ i : M,
        leValue M (succValue M i) (listLength.value ![v 0]) →
          leValue M (succValue M (listEntry.value ![v 0, i])) (v 0))
      pa_definable
    · intro i hi
      rw [listLength_zero_value] at hi
      exact False.elim (((successor_le_iff_lt i _).mp hi).2 (zero_le_value i))
    · intro a c ih i hi
      have hcn : listCons.value ![a, c] ≠ zeroValue M := by
        rw [listCons_value]
        exact successor_ne_zero _
      by_cases hiz : i = zeroValue M
      · rw [hiz, listEntry_cons_zero_value]
        have hh := head_smaller_value (listCons.value ![a, c]) hcn
        rwa [head_cons_value] at hh
      · obtain ⟨j, rfl⟩ := PAComputations.predecessor i hiz
        rw [listLength_cons_value] at hi
        rw [listEntry_cons_successor_value]
        have ht := tail_smaller_value (listCons.value ![a, c]) hcn
        rw [tail_cons_value] at ht
        exact le_trans_value (ih j ((successor_le_successor_value_iff _ _).mp hi))
          (le_trans_value (le_successor_value c) ht)
  exact hs c i hi

theorem node_child_smaller_value (t c i : M)
    (hi : leValue M (succValue M i) (listLength.value ![c])) :
    leValue M (succValue M (listEntry.value ![c, i])) (listCons.value ![t, c]) := by
  have hcn : listCons.value ![t, c] ≠ zeroValue M := by
    rw [listCons_value]
    exact successor_ne_zero _
  have ht := tail_smaller_value (listCons.value ![t, c]) hcn
  rw [tail_cons_value] at ht
  exact le_trans_value (listEntry_smaller_value c i hi)
    (le_trans_value (le_successor_value c) ht)

namespace SyntaxPrograms

theorem mapStep_value (h : Program 2) (p a z : M) :
    (mapStep h).value ![p, a, z] = listCons.value ![h.value ![p, a], z] := by
  simp only [mapStep, binary_value, Program.value_proj, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]

theorem listMap_value (h : Program 2) (p c : M) :
    (listMap h).value ![p, c] =
      (paramFold (mapStep h)).value ![p, listReverse.value ![c], zeroValue M] := by
  simp only [listMap, ternary_value, unary_value, Program.value_proj,
    Matrix.cons_val_zero, Matrix.cons_val_one, constant_value, numeral_value_zero]

theorem listMap_zero_value (h : Program 2) (p : M) :
    (listMap h).value ![p, zeroValue M] = zeroValue M := by
  rw [listMap_value, listReverse_zero_value, paramFold_zero_value]

theorem listMap_cons_value (h : Program 2) (p a c : M) :
    (listMap h).value ![p, listCons.value ![a, c] ] =
      listCons.value ![h.value ![p, a], (listMap h).value ![p, c] ] := by
  rw [listMap_value, listReverse_cons_value, paramFold_append_value,
    paramFold_cons_value, paramFold_zero_value, mapStep_value, ← listMap_value]

theorem tag_node_value (t c : M) : tag.value ![listCons.value ![t, c] ] = t := by
  simp only [tag, unary_value, listCons_value, predecessor_successor, unpairLeft_pair_value]

theorem args_node_value (t c : M) : args.value ![listCons.value ![t, c] ] = c := by
  simp only [args, unary_value, listCons_value, predecessor_successor, unpairRight_pair_value]

theorem node_reconstruction_value (e : M) (he : e ≠ zeroValue M) :
    listCons.value ![tag.value ![e], args.value ![e] ] = e := by
  obtain ⟨d, rfl⟩ := PAComputations.predecessor e he
  simp only [tag, args, unary_value, predecessor_successor,
    listCons_value, pair_unpair_value]

theorem stats_equation_value (e : M) :
    stats.value ![e] = summaryStep.value ![e, (history summaryStep).value ![e] ] := by
  have he := courseValue_value summaryStep (Fin.elim0 : Fin 0 → M) e
  have hv (a : M) : Fin.snoc (Fin.elim0 : Fin 0 → M) a = ![a] := by
    funext i
    fin_cases i
    rfl
  have hv2 (a b : M) : Fin.snoc (![a] : Fin 1 → M) b = ![a, b] := by
    funext j
    fin_cases j <;> rfl
  simpa only [stats, hv, hv2] using he

theorem stats_history_entry_value (e i : M) (hi : leValue M (succValue M i) e) :
    listEntry.value ![(history summaryStep).value ![e], i] = stats.value ![i] := by
  have he := history_entry_value summaryStep (Fin.elim0 : Fin 0 → M) e i hi
  have hv (a : M) : Fin.snoc (Fin.elim0 : Fin 0 → M) a = ![a] := by
    funext j
    fin_cases j
    rfl
  simpa only [stats, hv] using he

theorem rewrite_equation_value (mode i t e : M) :
    rewrite.value ![mode, i, t, e] =
      rewriteStep.value ![mode, i, t, e, (history rewriteStep).value ![mode, i, t, e] ] := by
  have he := courseValue_value rewriteStep (![mode, i, t] : Fin 3 → M) e
  have hv (a : M) : Fin.snoc (![mode, i, t] : Fin 3 → M) a = ![mode, i, t, a] := by
    funext j
    fin_cases j <;> rfl
  have hv5 (a b : M) : Fin.snoc (![mode, i, t, a] : Fin 4 → M) b = ![mode, i, t, a, b] := by
    funext j
    fin_cases j <;> rfl
  simpa only [rewrite, hv, hv5] using he

theorem rewrite_history_entry_value (mode i t e c : M)
    (hc : leValue M (succValue M c) e) :
    listEntry.value ![(history rewriteStep).value ![mode, i, t, e], c] =
      rewrite.value ![mode, i, t, c] := by
  have he := history_entry_value rewriteStep (![mode, i, t] : Fin 3 → M) e c hc
  have hv (a : M) : Fin.snoc (![mode, i, t] : Fin 3 → M) a = ![mode, i, t, a] := by
    funext j
    fin_cases j <;> rfl
  simpa only [rewrite, hv] using he

theorem modelList_length_value (xs : List M) :
    listLength.value ![modelList xs] = numeralValue M xs.length := by
  induction xs with
  | nil => simp only [modelList_nil, listLength_zero_value, List.length_nil, numeral_value_zero]
  | cons a xs ih =>
      simp only [modelList_cons, listLength_cons_value, List.length_cons, numeral_value_succ, ih]

theorem modelList_head_value (xs : List M) :
    listHead.value ![modelList xs] = xs.headD (zeroValue M) := by
  cases xs with
  | nil => exact head_zero_value
  | cons a xs => exact head_cons_value a _

theorem modelList_tail_value (xs : List M) :
    listTail.value ![modelList xs] = modelList xs.tail := by
  cases xs with
  | nil => exact tail_zero_value
  | cons a xs => exact tail_cons_value a _

theorem tag_modelNode_value (k : ℕ) (xs : List M) :
    tag.value ![modelNode k xs] = numeralValue M k := tag_node_value _ _

theorem args_modelNode_value (k : ℕ) (xs : List M) :
    args.value ![modelNode k xs] = modelList xs := args_node_value _ _

theorem children_modelNode_value (k : ℕ) (xs : List M) :
    children.value ![modelNode k xs] = modelList (if k = 2 ∨ k = 5 then xs.tail else xs) := by
  simp only [children, ternary_value, binary_value, unary_value, constant_value,
    tag_modelNode_value, args_modelNode_value, equalTest_truthValue,
    disjoin_truthValue, select_value, truthValue_eq_zero_iff, numeral_eq_iff_model,
    modelList_tail_value, ite_not]
  split_ifs <;> rfl

theorem modelList_member_smaller (xs : List M) (a : M) (ha : a ∈ xs) :
    leValue M (succValue M a) (modelList xs) := by
  induction xs with
  | nil => exact False.elim (List.not_mem_nil ha)
  | cons b xs ih =>
      rcases List.mem_cons.mp ha with rfl | ha
      · have hh := head_smaller_value (listCons.value ![a, modelList xs]) (by
          rw [listCons_value]
          exact successor_ne_zero _)
        simpa only [head_cons_value, modelList_cons] using hh
      · have ht := tail_smaller_value (listCons.value ![b, modelList xs]) (by
          rw [listCons_value]
          exact successor_ne_zero _)
        rw [tail_cons_value] at ht
        exact le_trans_value (ih ha) (le_trans_value (le_successor_value _) ht)

theorem modelNode_child_smaller (k : ℕ) (xs : List M) (a : M) (ha : a ∈ xs) :
    leValue M (succValue M a) (modelNode k xs) := by
  have ht := tail_smaller_value (modelNode k xs) (modelNode_ne_zero k xs)
  change leValue M (succValue M (listTail.value ![listCons.value ![numeralValue M k, modelList xs] ]))
    (modelNode k xs) at ht
  rw [tail_cons_value] at ht
  exact le_trans_value (modelList_member_smaller xs a ha)
    (le_trans_value (le_successor_value _) ht)

theorem paramFold_modelList_value (h : Program 3) (p z : M) (xs : List M) :
    (paramFold h).value ![p, modelList xs, z] =
      xs.foldl (fun acc a => h.value ![p, a, acc]) z := by
  induction xs generalizing z with
  | nil => exact paramFold_zero_value h p z
  | cons a xs ih => rw [modelList_cons, paramFold_cons_value, List.foldl_cons, ih]

theorem foldSummary_value (h : Program 3) (initial : ℕ) (e hist : M) :
    (foldSummary h initial).value ![e, hist] =
      (paramFold h).value ![hist, children.value ![e], numeralValue M initial] := by
  simp only [foldSummary, ternary_value, unary_value, Program.value_proj,
    Matrix.cons_val_zero, Matrix.cons_val_one, constant_value]

theorem maxSummary_value (i : Fin 4) (hist a z : M) :
    (maxSummary i).value ![hist, a, z] =
      maximum.value ![z, (part i).value ![listEntry.value ![hist, a] ] ] := by
  simp only [maxSummary, binary_value, unary_value, Program.value_proj,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]

theorem goodSummary_value (i : Fin 4) (hist a z : M) :
    (goodSummary i).value ![hist, a, z] =
      mulValue M z (sign.value ![(part i).value ![listEntry.value ![hist, a] ] ]) := by
  simp only [goodSummary, binary_value, unary_value, Program.value_proj,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, multiplication_value]

def modelSummary (td fd fv av : M) : M :=
  squarePair.value ![td, squarePair.value ![fd, squarePair.value ![fv, av] ] ]

theorem modelSummary_part_value (i : Fin 4) (td fd fv av : M) :
    (part i).value ![modelSummary td fd fv av] = ![td, fd, fv, av] i :=
  part_quad_value i td fd fv av

private theorem successor_eq_iff_value (a b : M) :
    succValue M a = succValue M b ↔ a = b := successor_injective.eq_iff

private theorem zero_ne_successor_value (a : M) : zeroValue M ≠ succValue M a :=
  (successor_ne_zero a).symm

attribute [local simp] unary_value binary_value ternary_value quad_value
  Program.value_proj constant_value select_value equalTest_truthValue
  disjoin_truthValue multiplication_truthValue arithmeticFunctionTest_value
  Program.value_succ addition_value multiplication_value
  modelList_length_value modelList_head_value modelList_tail_value
  tag_modelNode_value args_modelNode_value children_modelNode_value
  modelNode_ne_zero foldSummary_value paramFold_modelList_value
  maxSummary_value goodSummary_value part_quad_value
  Matrix.head_cons Matrix.tail_cons listLength_zero_value listLength_cons_value
  head_zero_value head_cons_value tail_zero_value tail_cons_value
  paramFold_zero_value paramFold_cons_value successor_eq_iff_value
  successor_ne_zero zero_ne_successor_value part_zero_value modelSummary_part_value
  one_mul_value mul_one_value
  zero_mul_value mul_zero_value zero_add_value add_zero_value

theorem summaryStep_free_modelNode_value (a hist : M) :
    summaryStep.value ![modelNode 0 [a] , hist] =
      modelSummary (numeralValue M 1) (zeroValue M) (numeralValue M 1) (zeroValue M) := by
  simp [summaryStep, modelSummary]

theorem stats_free_modelNode_value (a : M) :
    stats.value ![modelNode 0 [a] ] =
      modelSummary (numeralValue M 1) (zeroValue M) (numeralValue M 1) (zeroValue M) := by
  rw [stats_equation_value, summaryStep_free_modelNode_value]

theorem summaryStep_bound_modelNode_value (a hist : M) :
    summaryStep.value ![modelNode 1 [a] , hist] =
      modelSummary (addValue M a (numeralValue M 2)) (zeroValue M) (zeroValue M) (zeroValue M) := by
  simp [summaryStep, modelSummary]

theorem stats_bound_modelNode_value (a : M) :
    stats.value ![modelNode 1 [a] ] =
      modelSummary (addValue M a (numeralValue M 2)) (zeroValue M) (zeroValue M) (zeroValue M) := by
  rw [stats_equation_value, summaryStep_bound_modelNode_value]

theorem summaryStep_aux_modelNode_value (a hist : M) :
    summaryStep.value ![modelNode 8 [a] , hist] =
      modelSummary (numeralValue M 1) (zeroValue M) (zeroValue M)
        (addValue M a (numeralValue M 1)) := by
  simp [summaryStep, modelSummary]

theorem stats_aux_modelNode_value (a : M) :
    stats.value ![modelNode 8 [a] ] =
      modelSummary (numeralValue M 1) (zeroValue M) (zeroValue M)
        (addValue M a (numeralValue M 1)) := by
  rw [stats_equation_value, summaryStep_aux_modelNode_value]

theorem summaryStep_bot_modelNode_value (hist : M) :
    summaryStep.value ![modelNode 3 ([] : List M), hist] =
      modelSummary (zeroValue M) (numeralValue M 1) (zeroValue M) (zeroValue M) := by
  simp [summaryStep, modelSummary]

theorem stats_bot_modelNode_value :
    stats.value ![modelNode 3 ([] : List M)] =
      modelSummary (zeroValue M) (numeralValue M 1) (zeroValue M) (zeroValue M) := by
  rw [stats_equation_value, summaryStep_bot_modelNode_value]

theorem summaryStep_zero_modelNode_value (hist : M) :
    summaryStep.value ![modelNode 2 [numeralValue M 0] , hist] =
      modelSummary (numeralValue M 1) (zeroValue M) (zeroValue M) (zeroValue M) := by
  simp [summaryStep, modelSummary, predecessor_successor, sign_value, truthValue]

theorem stats_zero_modelNode_value :
    stats.value ![modelNode 2 [numeralValue M 0] ] =
      modelSummary (numeralValue M 1) (zeroValue M) (zeroValue M) (zeroValue M) := by
  rw [stats_equation_value, summaryStep_zero_modelNode_value]

def historyPart (i : Fin 4) (hist a : M) : M :=
  (part i).value ![listEntry.value ![hist, a] ]

theorem summaryStep_succ_modelNode_value (a hist : M) :
    summaryStep.value ![modelNode 2 [numeralValue M 1, a], hist] =
      if historyPart 0 hist a = zeroValue M then zeroValue M else
        modelSummary (maximum.value ![numeralValue M 1, historyPart 0 hist a]) (zeroValue M) (maximum.value ![zeroValue M, historyPart 2 hist a]) (maximum.value ![zeroValue M, historyPart 3 hist a]) := by
  by_cases ha : historyPart 0 hist a = zeroValue M <;>
    simp only [historyPart] at ha <;>
    simp [summaryStep, modelSummary, historyPart, predecessor_successor, sign_value, truthValue, ha]

theorem summaryStep_binary_modelNode_value (f : ℕ) (hf : f = 2 ∨ f = 3) (a b hist : M) :
    summaryStep.value ![modelNode 2 [numeralValue M f, a, b], hist] =
      if historyPart 0 hist a = zeroValue M ∨ historyPart 0 hist b = zeroValue M then zeroValue M else
        modelSummary (maximum.value ![maximum.value ![numeralValue M 1, historyPart 0 hist a], historyPart 0 hist b]) (zeroValue M) (maximum.value ![maximum.value ![zeroValue M, historyPart 2 hist a], historyPart 2 hist b]) (maximum.value ![maximum.value ![zeroValue M, historyPart 3 hist a], historyPart 3 hist b]) := by
  rcases hf with rfl | rfl
  all_goals
    by_cases ha : historyPart 0 hist a = zeroValue M <;>
      by_cases hb : historyPart 0 hist b = zeroValue M <;>
        simp only [historyPart] at ha hb <;>
        simp [summaryStep, modelSummary, historyPart, predecessor_successor, sign_value, truthValue, ha, hb]

theorem summaryStep_equal_modelNode_value (a b hist : M) :
    summaryStep.value ![modelNode 4 [a, b], hist] =
      if historyPart 0 hist a = zeroValue M ∨ historyPart 0 hist b = zeroValue M then zeroValue M else
        modelSummary (zeroValue M) (maximum.value ![maximum.value ![numeralValue M 1, historyPart 0 hist a], historyPart 0 hist b]) (maximum.value ![maximum.value ![zeroValue M, historyPart 2 hist a], historyPart 2 hist b]) (maximum.value ![maximum.value ![zeroValue M, historyPart 3 hist a], historyPart 3 hist b]) := by
  by_cases ha : historyPart 0 hist a = zeroValue M <;>
    by_cases hb : historyPart 0 hist b = zeroValue M <;>
      simp only [historyPart] at ha hb <;>
      simp [summaryStep, modelSummary, historyPart, predecessor_successor, sign_value, truthValue, ha, hb]

theorem summaryStep_imp_modelNode_value (a b hist : M) :
    summaryStep.value ![modelNode 6 [a, b], hist] =
      if historyPart 1 hist a = zeroValue M ∨ historyPart 1 hist b = zeroValue M then zeroValue M else
        modelSummary (zeroValue M) (maximum.value ![maximum.value ![numeralValue M 1, historyPart 1 hist a], historyPart 1 hist b]) (maximum.value ![maximum.value ![zeroValue M, historyPart 2 hist a], historyPart 2 hist b]) (maximum.value ![maximum.value ![zeroValue M, historyPart 3 hist a], historyPart 3 hist b]) := by
  by_cases ha : historyPart 1 hist a = zeroValue M <;>
    by_cases hb : historyPart 1 hist b = zeroValue M <;>
      simp only [historyPart] at ha hb <;>
      simp [summaryStep, modelSummary, historyPart, predecessor_successor, sign_value, truthValue, ha, hb]

theorem summaryStep_all_modelNode_value (a hist : M) :
    summaryStep.value ![modelNode 7 [a], hist] =
      if historyPart 1 hist a = zeroValue M then zeroValue M else
        modelSummary (zeroValue M) (maximum.value ![numeralValue M 1, predecessor.value ![maximum.value ![numeralValue M 1, historyPart 1 hist a] ] ]) (maximum.value ![zeroValue M, historyPart 2 hist a]) (maximum.value ![zeroValue M, historyPart 3 hist a]) := by
  by_cases ha : historyPart 1 hist a = zeroValue M <;>
    simp only [historyPart] at ha <;>
    simp [summaryStep, modelSummary, historyPart, predecessor_successor, sign_value, truthValue, ha]


def statsPart (i : Fin 4) (a : M) : M := (part i).value ![stats.value ![a] ]

theorem historyPart_modelNode_value (i : Fin 4) (k : ℕ) (xs : List M) (a : M)
    (ha : a ∈ xs) :
    historyPart i ((history summaryStep).value ![modelNode k xs]) a = statsPart i a := by
  rw [historyPart, stats_history_entry_value _ _ (modelNode_child_smaller k xs a ha)]
  rfl

theorem stats_succ_modelNode_value (a : M) :
    stats.value ![modelNode 2 [numeralValue M 1, a] ] =
      if statsPart 0 a = zeroValue M then zeroValue M else
        modelSummary (maximum.value ![numeralValue M 1, statsPart 0 a]) (zeroValue M) (maximum.value ![zeroValue M, statsPart 2 a]) (maximum.value ![zeroValue M, statsPart 3 a]) := by
  rw [stats_equation_value, summaryStep_succ_modelNode_value]
  have ha (i : Fin 4) : historyPart i ((history summaryStep).value ![modelNode 2 [numeralValue M 1, a] ]) a = statsPart i a :=
    historyPart_modelNode_value i 2 [numeralValue M 1, a] a (by simp)
  simp only [ha]

theorem stats_binary_modelNode_value (f : ℕ) (hf : f = 2 ∨ f = 3) (a b : M) :
    stats.value ![modelNode 2 [numeralValue M f, a, b] ] =
      if statsPart 0 a = zeroValue M ∨ statsPart 0 b = zeroValue M then zeroValue M else
        modelSummary (maximum.value ![maximum.value ![numeralValue M 1, statsPart 0 a], statsPart 0 b]) (zeroValue M) (maximum.value ![maximum.value ![zeroValue M, statsPart 2 a], statsPart 2 b]) (maximum.value ![maximum.value ![zeroValue M, statsPart 3 a], statsPart 3 b]) := by
  rw [stats_equation_value, summaryStep_binary_modelNode_value f hf]
  have ha (i : Fin 4) : historyPart i ((history summaryStep).value ![modelNode 2 [numeralValue M f, a, b] ]) a = statsPart i a :=
    historyPart_modelNode_value i 2 [numeralValue M f, a, b] a (by simp)
  have hb (i : Fin 4) : historyPart i ((history summaryStep).value ![modelNode 2 [numeralValue M f, a, b] ]) b = statsPart i b :=
    historyPart_modelNode_value i 2 [numeralValue M f, a, b] b (by simp)
  simp only [ha, hb]

theorem stats_equal_modelNode_value (a b : M) :
    stats.value ![modelNode 4 [a, b] ] =
      if statsPart 0 a = zeroValue M ∨ statsPart 0 b = zeroValue M then zeroValue M else
        modelSummary (zeroValue M) (maximum.value ![maximum.value ![numeralValue M 1, statsPart 0 a], statsPart 0 b]) (maximum.value ![maximum.value ![zeroValue M, statsPart 2 a], statsPart 2 b]) (maximum.value ![maximum.value ![zeroValue M, statsPart 3 a], statsPart 3 b]) := by
  rw [stats_equation_value, summaryStep_equal_modelNode_value]
  have ha (i : Fin 4) : historyPart i ((history summaryStep).value ![modelNode 4 [a, b] ]) a = statsPart i a :=
    historyPart_modelNode_value i 4 [a, b] a (by simp)
  have hb (i : Fin 4) : historyPart i ((history summaryStep).value ![modelNode 4 [a, b] ]) b = statsPart i b :=
    historyPart_modelNode_value i 4 [a, b] b (by simp)
  simp only [ha, hb]

theorem stats_imp_modelNode_value (a b : M) :
    stats.value ![modelNode 6 [a, b] ] =
      if statsPart 1 a = zeroValue M ∨ statsPart 1 b = zeroValue M then zeroValue M else
        modelSummary (zeroValue M) (maximum.value ![maximum.value ![numeralValue M 1, statsPart 1 a], statsPart 1 b]) (maximum.value ![maximum.value ![zeroValue M, statsPart 2 a], statsPart 2 b]) (maximum.value ![maximum.value ![zeroValue M, statsPart 3 a], statsPart 3 b]) := by
  rw [stats_equation_value, summaryStep_imp_modelNode_value]
  have ha (i : Fin 4) : historyPart i ((history summaryStep).value ![modelNode 6 [a, b] ]) a = statsPart i a :=
    historyPart_modelNode_value i 6 [a, b] a (by simp)
  have hb (i : Fin 4) : historyPart i ((history summaryStep).value ![modelNode 6 [a, b] ]) b = statsPart i b :=
    historyPart_modelNode_value i 6 [a, b] b (by simp)
  simp only [ha, hb]

theorem stats_all_modelNode_value (a : M) :
    stats.value ![modelNode 7 [a] ] =
      if statsPart 1 a = zeroValue M then zeroValue M else
        modelSummary (zeroValue M) (maximum.value ![numeralValue M 1, predecessor.value ![maximum.value ![numeralValue M 1, statsPart 1 a] ] ]) (maximum.value ![zeroValue M, statsPart 2 a]) (maximum.value ![zeroValue M, statsPart 3 a]) := by
  rw [stats_equation_value, summaryStep_all_modelNode_value]
  have ha (i : Fin 4) : historyPart i ((history summaryStep).value ![modelNode 7 [a] ]) a = statsPart i a :=
    historyPart_modelNode_value i 7 [a] a (by simp)
  simp only [ha]

theorem termDepth_succ_modelNode_value (a : M) :
    termDepth (modelNode 2 [numeralValue M 1, a]) =
      if termDepth a = zeroValue M then zeroValue M else maximum.value ![numeralValue M 1, termDepth a] := by
  simp only [termDepth, stats_succ_modelNode_value, statsPart]
  split_ifs
  all_goals simp_all

theorem formDepth_succ_modelNode_value (a : M) :
    formDepth (modelNode 2 [numeralValue M 1, a]) =
      zeroValue M := by
  simp only [formDepth, stats_succ_modelNode_value, statsPart]
  split_ifs
  all_goals simp_all

theorem termDepth_binary_modelNode_value (f : ℕ) (hf : f = 2 ∨ f = 3) (a b : M) :
    termDepth (modelNode 2 [numeralValue M f, a, b]) =
      if termDepth a = zeroValue M ∨ termDepth b = zeroValue M then zeroValue M else maximum.value ![maximum.value ![numeralValue M 1, termDepth a], termDepth b] := by
  simp only [termDepth, stats_binary_modelNode_value f hf, statsPart]
  split_ifs
  all_goals simp_all

theorem formDepth_binary_modelNode_value (f : ℕ) (hf : f = 2 ∨ f = 3) (a b : M) :
    formDepth (modelNode 2 [numeralValue M f, a, b]) =
      zeroValue M := by
  simp only [formDepth, stats_binary_modelNode_value f hf, statsPart]
  split_ifs
  all_goals simp_all

theorem termDepth_equal_modelNode_value (a b : M) :
    termDepth (modelNode 4 [a, b]) =
      zeroValue M := by
  simp only [termDepth, stats_equal_modelNode_value, statsPart]
  split_ifs
  all_goals simp_all

theorem formDepth_equal_modelNode_value (a b : M) :
    formDepth (modelNode 4 [a, b]) =
      if termDepth a = zeroValue M ∨ termDepth b = zeroValue M then zeroValue M else maximum.value ![maximum.value ![numeralValue M 1, termDepth a], termDepth b] := by
  simp only [termDepth, formDepth, stats_equal_modelNode_value, statsPart]
  split_ifs
  all_goals simp_all

theorem termDepth_imp_modelNode_value (a b : M) :
    termDepth (modelNode 6 [a, b]) =
      zeroValue M := by
  simp only [termDepth, stats_imp_modelNode_value, statsPart]
  split_ifs
  all_goals simp_all

theorem formDepth_imp_modelNode_value (a b : M) :
    formDepth (modelNode 6 [a, b]) =
      if formDepth a = zeroValue M ∨ formDepth b = zeroValue M then zeroValue M else maximum.value ![maximum.value ![numeralValue M 1, formDepth a], formDepth b] := by
  simp only [formDepth, stats_imp_modelNode_value, statsPart]
  split_ifs
  all_goals simp_all

theorem termDepth_all_modelNode_value (a : M) :
    termDepth (modelNode 7 [a]) =
      zeroValue M := by
  simp only [termDepth, stats_all_modelNode_value, statsPart]
  split_ifs
  all_goals simp_all

theorem formDepth_all_modelNode_value (a : M) :
    formDepth (modelNode 7 [a]) =
      if formDepth a = zeroValue M then zeroValue M else maximum.value ![numeralValue M 1, predecessor.value ![maximum.value ![numeralValue M 1, formDepth a] ] ] := by
  simp only [formDepth, stats_all_modelNode_value, statsPart]
  split_ifs
  all_goals simp_all


end SyntaxPrograms
end
end Lemmatheca.ProofTheory.PAComputations.ProofPrograms
