import Lemmatheca.PaListsAndSyntax.PANativeSyntaxRecurrences

open Lemmatheca.MathematicalLogic Lemmatheca.ModelTheory Lemmatheca.ComputabilityTheory

/-! Positive depth recognizers decompose actual internal codes into the finite
arities of the arithmetic language, with positive recognized children. -/
namespace Lemmatheca.ProofTheory.PAComputations.ProofPrograms.SyntaxPrograms
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic ArithmeticTheories ArithmeticRepresentability
noncomputable section
universe u
variable {M : Type u} [language.Structure M] [M ⊨ PA]

local instance nativeSyntaxRecognitionLocalInstance1 : DecidableEq M := Classical.decEq M

attribute [local simp] part_zero_value part_quad_value

theorem part_ite_value (i : Fin 4) (P : Prop) [Decidable P] (a b : M) :
    (part i).value ![if P then a else b] =
      if P then (part i).value ![a] else (part i).value ![b] := by
  by_cases h : P <;> simp only [h, ↓reduceIte]

private theorem term_root_cases (e hist : M)
    (he : (part 0).value ![summaryStep.value ![e, hist] ] ≠ zeroValue M) :
    e ≠ zeroValue M ∧ ((tag.value ![e] = numeralValue M 0 ∧
      listLength.value ![args.value ![e] ] = numeralValue M 1) ∨
    (tag.value ![e] = numeralValue M 1 ∧
      listLength.value ![args.value ![e] ] = numeralValue M 1) ∨
    (tag.value ![e] = numeralValue M 8 ∧
      listLength.value ![args.value ![e] ] = numeralValue M 1) ∨
    (tag.value ![e] = numeralValue M 2 ∧
      mulValue M (sign.value ![listLength.value ![args.value ![e] ] ])
        (mulValue M
          (arithmeticFunctionTest.value ![listHead.value ![args.value ![e] ],
            predecessor.value ![listLength.value ![args.value ![e] ] ] ])
          ((foldSummary (goodSummary 0) 1).value ![e, hist])) ≠ zeroValue M)) := by
  simp only [summaryStep, ternary_value, binary_value, unary_value, quad_value,
    Program.value_proj,
    constant_value, select_value, equalTest_truthValue, truthValue_eq_zero_iff,
    ite_not, multiplication_value, part_ite_value,
    part_quad_value, Matrix.cons_val_zero] at he
  simp only [numeral_value_zero, part_zero_value, ite_self] at he ⊢
  by_cases hz : e = zeroValue M
  · simp only [hz, ite_true, not_true_eq_false, ne_eq] at he
  simp only [hz, ite_false] at he
  refine ⟨hz, ?_⟩
  by_cases h0 : tag.value ![e] = zeroValue M
  · by_cases hl : listLength.value ![args.value ![e] ] = numeralValue M 1
    · exact Or.inl ⟨h0, hl⟩
    · simp only [h0, hl, ite_true, ite_false, ne_eq, not_true_eq_false] at he
  simp only [h0, ite_false] at he
  by_cases h1 : tag.value ![e] = numeralValue M 1
  · by_cases hl : listLength.value ![args.value ![e] ] = numeralValue M 1
    · exact Or.inr (Or.inl ⟨h1, hl⟩)
    · simp only [h1, hl, ite_true, ite_false, ne_eq, not_true_eq_false] at he
  simp only [h1, ite_false] at he
  by_cases h2 : tag.value ![e] = numeralValue M 2
  · simp only [h2, ite_true] at he
    have hn : mulValue M (sign.value ![listLength.value ![args.value ![e] ] ])
        (mulValue M
          (arithmeticFunctionTest.value ![listHead.value ![args.value ![e] ],
            predecessor.value ![listLength.value ![args.value ![e] ] ] ])
          ((foldSummary (goodSummary 0) 1).value ![e, hist])) ≠ zeroValue M := by
      intro hh
      simp only [hh, ite_true, ne_eq, not_true_eq_false] at he
    exact Or.inr (Or.inr (Or.inr ⟨h2, hn⟩))
  simp only [h2, ite_false] at he
  by_cases h8 : tag.value ![e] = numeralValue M 8
  · by_cases hl : listLength.value ![args.value ![e] ] = numeralValue M 1
    · exact Or.inr (Or.inr (Or.inl ⟨h8, hl⟩))
    · simp only [h8, hl, ite_false, ite_self, ne_eq, not_true_eq_false] at he
  simp only [h8, ite_false, ite_self, ne_eq, not_true_eq_false] at he

private theorem term_node_shape_one (e : M) (k : ℕ) (hne : e ≠ zeroValue M)
    (ht : tag.value ![e] = numeralValue M k)
    (hl : listLength.value ![args.value ![e] ] = numeralValue M 1) :
    ∃ a : M, e = modelNode k [a] := by
  have hd := node_reconstruction_value e hne
  rw [ht, listLength_one_shape_value _ hl] at hd
  refine ⟨listHead.value ![args.value ![e] ], ?_⟩
  simpa only [modelNode, modelList_cons, modelList_nil] using hd.symm

theorem termDepth_cases (e : M) (he : termDepth e ≠ zeroValue M) :
    (∃ a : M, e = modelNode 0 [a]) ∨
    (∃ a : M, e = modelNode 1 [a]) ∨
    (∃ a : M, e = modelNode 8 [a]) ∨
    e = modelNode 2 [numeralValue M 0] ∨
    (∃ a : M, e = modelNode 2 [numeralValue M 1, a] ∧ termDepth a ≠ zeroValue M) ∨
    (∃ f : ℕ, (f = 2 ∨ f = 3) ∧ ∃ a b : M,
      e = modelNode 2 [numeralValue M f, a, b] ∧
        termDepth a ≠ zeroValue M ∧ termDepth b ≠ zeroValue M) := by
  have hr : (part 0).value
      ![summaryStep.value ![e, (history summaryStep).value ![e] ] ] ≠ zeroValue M := by
    rw [← stats_equation_value]
    exact he
  obtain ⟨hne, h0 | h1 | h8 | h2⟩ := term_root_cases e _ hr
  · obtain ⟨a, ha⟩ := term_node_shape_one e 0 hne h0.1 h0.2
    exact Or.inl ⟨a, ha⟩
  · obtain ⟨a, ha⟩ := term_node_shape_one e 1 hne h1.1 h1.2
    exact Or.inr (Or.inl ⟨a, ha⟩)
  · obtain ⟨a, ha⟩ := term_node_shape_one e 8 hne h8.1 h8.2
    exact Or.inr (Or.inr (Or.inl ⟨a, ha⟩))
  · let A : M := args.value ![e]
    let L : M := listLength.value ![A]
    let F : M := listHead.value ![A]
    have htest := h2.2
    change mulValue M (sign.value ![L])
      (mulValue M (arithmeticFunctionTest.value ![F, predecessor.value ![L] ])
        ((foldSummary (goodSummary 0) 1).value
          ![e, (history summaryStep).value ![e] ])) ≠ zeroValue M at htest
    have hL : L ≠ zeroValue M := by
      intro hz
      apply htest
      rw [hz, sign_zero_value, zero_mul_value]
    have hfun : arithmeticFunctionTest.value ![F, predecessor.value ![L] ] ≠ zeroValue M := by
      intro hz
      apply htest
      rw [hz, zero_mul_value, mul_zero_value]
    simp only [ne_eq, arithmeticFunctionTest_value, truthValue_eq_zero_iff, not_not] at hfun
    have hLp : succValue M (predecessor.value ![L]) = L := by
      obtain ⟨d, hd⟩ := PAComputations.predecessor L hL
      rw [hd, predecessor_successor]
    have hlen (n : ℕ) (hp : predecessor.value ![L] = numeralValue M n) :
        L = numeralValue M (n + 1) := by
      rw [numeral_value_succ, ← hp]
      exact hLp.symm
    have hd := node_reconstruction_value e hne
    change listCons.value ![tag.value ![e], A] = e at hd
    rw [h2.1] at hd
    rcases hfun with hf0 | hf1 | hf23
    · have hshape := listLength_one_shape_value A (hlen 0 hf0.2)
      have hF : listHead.value ![A] = numeralValue M 0 := hf0.1
      rw [hshape, hF] at hd
      have heq : e = modelNode 2 [numeralValue M 0] := by
        simpa only [modelNode, modelList_cons, modelList_nil] using hd.symm
      exact Or.inr (Or.inr (Or.inr (Or.inl heq)))
    · have hshape := listLength_two_shape_value A (hlen 1 hf1.2)
      let a : M := listHead.value ![listTail.value ![A] ]
      have hF : listHead.value ![A] = numeralValue M 1 := hf1.1
      rw [hshape, hF] at hd
      have heq : e = modelNode 2 [numeralValue M 1, a] := by
        simpa only [modelNode, modelList_cons, modelList_nil] using hd.symm
      have ha : termDepth a ≠ zeroValue M := by
        intro hz
        apply he
        rw [heq, termDepth_succ_modelNode_value, ite_eq_left hz]
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨a, heq, ha⟩))))
    · obtain ⟨f, hf, hF⟩ : ∃ f : ℕ, (f = 2 ∨ f = 3) ∧ F = numeralValue M f := by
        rcases hf23.1 with hf2 | hf3
        · exact ⟨2, Or.inl rfl, hf2⟩
        · exact ⟨3, Or.inr rfl, hf3⟩
      have hls : listLength.value ![A] = succValue M (numeralValue M 2) := by
        rw [← numeral_value_succ]
        exact hlen 2 hf23.2
      obtain ⟨f', t, hA, ht⟩ := listLength_successor_decompose_value A (numeralValue M 2) hls
      have hf' : f' = numeralValue M f := by
        simpa only [F, hA, head_cons_value] using hF
      have htshape := listLength_two_shape_value t ht
      let a : M := listHead.value ![t]
      let b : M := listHead.value ![listTail.value ![t] ]
      rw [hA, htshape, hf'] at hd
      have heq : e = modelNode 2 [numeralValue M f, a, b] := by
        simpa only [modelNode, modelList_cons, modelList_nil] using hd.symm
      have ha : termDepth a ≠ zeroValue M := by
        intro hz
        apply he
        rw [heq, termDepth_binary_modelNode_value f hf, ite_eq_left (Or.inl hz)]
      have hb : termDepth b ≠ zeroValue M := by
        intro hz
        apply he
        rw [heq, termDepth_binary_modelNode_value f hf, ite_eq_left (Or.inr hz)]
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨f, hf, a, b, heq, ha, hb⟩))))

set_option maxHeartbeats 4000000 in
private theorem form_summary_root (e hist : M)
    (he : (part 1).value ![summaryStep.value ![e, hist] ] ≠ zeroValue M) :
    e ≠ zeroValue M ∧ (
    (tag.value ![e] = numeralValue M 3 ∧
      listLength.value ![args.value ![e] ] = numeralValue M 0) ∨
    (tag.value ![e] = numeralValue M 4 ∧
      listLength.value ![args.value ![e] ] = numeralValue M 2) ∨
    (tag.value ![e] = numeralValue M 6 ∧
      listLength.value ![args.value ![e] ] = numeralValue M 2) ∨
    (tag.value ![e] = numeralValue M 7 ∧
      listLength.value ![args.value ![e] ] = numeralValue M 1)) := by
  classical
  simp (config := { maxSteps := 300000 }) only [summaryStep, ternary_value, binary_value, unary_value, quad_value,
    Program.value_proj, Matrix.cons_val_zero, constant_value,
    select_value, equalTest_truthValue, truthValue_eq_zero_iff, ite_not, multiplication_value,
    part_ite_value, part_quad_value, Matrix.cons_val_one, numeral_value_zero,
    part_zero_value, ite_self] at he
  by_cases he0 : e = zeroValue M
  · simp only [he0, ↓reduceIte] at he
    exact False.elim (he rfl)
  refine ⟨he0, ?_⟩
  by_cases h0 : tag.value ![e] = numeralValue M 0
  · simp only [numeral_value_zero] at h0
    simp only [he0, h0, ↓reduceIte] at he
    exact False.elim (he rfl)
  by_cases h1 : tag.value ![e] = numeralValue M 1
  · simp only [numeral_value_zero] at h0
    simp only [he0, h1, numeral_eq_zero_iff_model, ↓reduceIte, ite_self] at he
    exact False.elim (he rfl)
  by_cases h2 : tag.value ![e] = numeralValue M 2
  · simp only [numeral_value_zero] at h0
    simp only [he0, h2, numeral_eq_zero_iff_model, numeral_eq_iff_model, ↓reduceIte, ite_self] at he
    exact False.elim (he rfl)
  by_cases h3 : tag.value ![e] = numeralValue M 3
  · by_cases hl : listLength.value ![args.value ![e] ] = numeralValue M 0
    · exact Or.inl ⟨h3, hl⟩
    · simp only [numeral_value_zero] at h0 hl
      simp only [he0, h3, numeral_eq_zero_iff_model, numeral_eq_iff_model, hl, ↓reduceIte] at he
      exact False.elim (he rfl)
  by_cases h4 : tag.value ![e] = numeralValue M 4
  · by_cases hl : listLength.value ![args.value ![e] ] = numeralValue M 2
    · exact Or.inr (Or.inl ⟨h4, hl⟩)
    · simp only [numeral_value_zero] at h0
      simp only [he0, h4, numeral_eq_zero_iff_model, numeral_eq_iff_model, hl, truthValue,
        ↓reduceIte, zero_mul_value] at he
      exact False.elim (he rfl)
  by_cases h6 : tag.value ![e] = numeralValue M 6
  · by_cases hl : listLength.value ![args.value ![e] ] = numeralValue M 2
    · exact Or.inr (Or.inr (Or.inl ⟨h6, hl⟩))
    · simp only [numeral_value_zero] at h0
      simp only [he0, h6, numeral_eq_zero_iff_model, numeral_eq_iff_model, hl, truthValue,
        ↓reduceIte, zero_mul_value] at he
      exact False.elim (he rfl)
  by_cases h7 : tag.value ![e] = numeralValue M 7
  · by_cases hl : listLength.value ![args.value ![e] ] = numeralValue M 1
    · exact Or.inr (Or.inr (Or.inr ⟨h7, hl⟩))
    · simp only [numeral_value_zero] at h0
      simp only [he0, h7, numeral_eq_zero_iff_model, numeral_eq_iff_model, hl, truthValue,
        ↓reduceIte, zero_mul_value] at he
      exact False.elim (he rfl)
  simp only [numeral_value_zero] at h0
  simp only [he0, h0, h1, h2, h3, h4, h6, h7, ↓reduceIte] at he
  exact False.elim (he rfl)

theorem formDepth_cases (e : M) (he : formDepth e ≠ zeroValue M) :
    e = modelNode 3 [] ∨
    (∃ a b : M, e = modelNode 4 [a, b] ∧
      termDepth a ≠ zeroValue M ∧ termDepth b ≠ zeroValue M) ∨
    (∃ a b : M, e = modelNode 6 [a, b] ∧
      formDepth a ≠ zeroValue M ∧ formDepth b ≠ zeroValue M) ∨
    (∃ a : M, e = modelNode 7 [a] ∧ formDepth a ≠ zeroValue M) := by
  have hsummary : (part 1).value ![summaryStep.value ![e, (history summaryStep).value ![e] ] ] ≠
      zeroValue M := by
    simpa only [formDepth, stats_equation_value] using he
  obtain ⟨hne, hroot⟩ := form_summary_root e _ hsummary
  have hnode := node_reconstruction_value e hne
  have node_of_shape (k : ℕ) (xs : List M)
      (htag : tag.value ![e] = numeralValue M k)
      (hargs : args.value ![e] = modelList xs) : e = modelNode k xs := by
    calc
      e = listCons.value ![tag.value ![e], args.value ![e] ] := hnode.symm
      _ = modelNode k xs := by rw [htag, hargs]; rfl
  rcases hroot with ⟨htag, hlen⟩ | ⟨htag, hlen⟩ | ⟨htag, hlen⟩ | ⟨htag, hlen⟩
  · apply Or.inl
    apply node_of_shape 3 [] htag
    apply (listLength_zero_iff_value _).mp
    simpa only [numeral_value_zero] using hlen
  · let a := listHead.value ![args.value ![e] ]
    let b := listHead.value ![listTail.value ![args.value ![e] ] ]
    have hshape : args.value ![e] = modelList [a, b] :=
      listLength_two_shape_value _ hlen
    have hn := node_of_shape 4 [a, b] htag hshape
    have hpos : formDepth (modelNode 4 [a, b]) ≠ zeroValue M := hn ▸ he
    have hp : ¬ (termDepth a = zeroValue M ∨ termDepth b = zeroValue M) := by
      intro hzero
      apply hpos
      rw [formDepth_equal_modelNode_value, ite_eq_left hzero]
    exact Or.inr (Or.inl ⟨a, b, hn, fun hz => hp (Or.inl hz), fun hz => hp (Or.inr hz)⟩)
  · let a := listHead.value ![args.value ![e] ]
    let b := listHead.value ![listTail.value ![args.value ![e] ] ]
    have hshape : args.value ![e] = modelList [a, b] :=
      listLength_two_shape_value _ hlen
    have hn := node_of_shape 6 [a, b] htag hshape
    have hpos : formDepth (modelNode 6 [a, b]) ≠ zeroValue M := hn ▸ he
    have hp : ¬ (formDepth a = zeroValue M ∨ formDepth b = zeroValue M) := by
      intro hzero
      apply hpos
      rw [formDepth_imp_modelNode_value, ite_eq_left hzero]
    exact Or.inr (Or.inr (Or.inl
      ⟨a, b, hn, fun hz => hp (Or.inl hz), fun hz => hp (Or.inr hz)⟩))
  · let a := listHead.value ![args.value ![e] ]
    have hshape : args.value ![e] = modelList [a] :=
      listLength_one_shape_value _ hlen
    have hn := node_of_shape 7 [a] htag hshape
    have hpos : formDepth (modelNode 7 [a]) ≠ zeroValue M := hn ▸ he
    have hp : formDepth a ≠ zeroValue M := by
      intro hzero
      apply hpos
      rw [formDepth_all_modelNode_value, ite_eq_left hzero]
    exact Or.inr (Or.inr (Or.inr ⟨a, hn, hp⟩))

end
end Lemmatheca.ProofTheory.PAComputations.ProofPrograms.SyntaxPrograms
