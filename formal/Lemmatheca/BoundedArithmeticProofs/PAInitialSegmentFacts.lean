import Lemmatheca.BoundedArithmeticProofs.PAInitialSegmentProofs

open Lemmatheca.MathematicalLogic Lemmatheca.ModelTheory Lemmatheca.ComputabilityTheory

namespace Lemmatheca.ProofTheory.PAComputations.ProofPrograms.InitialSegmentPrograms
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic ArithmeticTheories ArithmeticRepresentability
open SyntaxPrograms CheckerPrograms FixedSyntaxPrograms
noncomputable section
universe u
variable {M : Type u} [language.Structure M] [M ⊨ PA]

theorem implication_node_value (a b : M) :
    implication.value ![a, b] = modelNode 6 [a, b] := implication_value a b

theorem formulaCodeAt_model_value {α : Type*} {r k : ℕ} (name : α → Program r)
    (offset : ℕ) (A : language.BoundedFormula α k) (x : Fin r → M) :
    (formulaCodeAt name offset A).value x =
      modelFormulaCodeAt (fun a => (name a).value x) offset A := by
  have hn (k : ℕ) :
      (fun i : α ⊕ Fin k =>
        (Sum.elim name (fun i => syntaxNode 1 [constant (offset + i.val)]) i).value x) =
      Sum.elim (fun a => (name a).value x)
        (fun i => modelNode 1 [numeralValue M (offset + i.val)]) := by
    funext i
    cases i with
    | inl i => rfl
    | inr i => simp only [Sum.elim_inr, syntaxNode_value, list_cons_value, constant_value,
        list_nil_value, modelNode, modelList_cons, modelList_nil]
  induction A with
  | falsum => simp only [formulaCodeAt, bottom_value, modelFormulaCodeAt]
  | equal s t => simp only [formulaCodeAt, equalCode_value,
      termCode_model_value, hn, modelFormulaCodeAt]
  | rel e _ => exact e.elim
  | imp a b ha hb =>
    simp only [formulaCodeAt, impCode, binary_value, ha, hb, modelFormulaCodeAt,
      implication_node_value]
  | all a ha => simp only [formulaCodeAt, allCode_value, ha, modelFormulaCodeAt]

theorem statsPart_summary (e td fd fv av : M)
    (he : stats.value ![e] = modelSummary td fd fv av) (i : Fin 4) :
    statsPart i e = ![td, fd, fv, av] i := by
  simp only [statsPart, he, modelSummary_part_value]

theorem equal_numeral_stats (z td av n : M)
    (hz : stats.value ![z] = modelSummary td (zeroValue M) (zeroValue M) av)
    (htd : leValue M (numeralValue M 1) td) :
    stats.value ![modelNode 4 [z, ProofPrograms.numeral.value ![n] ] ] =
      modelSummary (zeroValue M) td (zeroValue M) av := by
  let := modelLinearOrder M
  have ht' : numeralValue M 1 ≤ td := htd
  have hav : zeroValue M ≤ av := zero_le_value av
  have hn := numeral_stats_value (M := M) n
  have ht0 : td ≠ zeroValue M := by
    intro h
    have hh := le_antisymm_value (h ▸ htd) (zero_le_value (numeralValue M 1))
    exact (by decide : (1 : ℕ) ≠ 0) ((numeral_eq_zero_iff_model 1).mp hh)
  rw [stats_equal_modelNode_value]
  simp only [statsPart_summary _ _ _ _ _ hz, statsPart_summary _ _ _ _ _ hn,
    Matrix.cons_val_zero, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons, ht0, numeral_eq_zero_iff_model, Nat.one_ne_zero,
    false_or, ↓reduceIte, maximum_value, max_eq_right ht', max_eq_left ht',
    max_self, max_eq_right hav, max_eq_left hav]

theorem imp_stats_same (a b fd av : M)
    (ha : stats.value ![a] = modelSummary (zeroValue M) fd (zeroValue M) av)
    (hb : stats.value ![b] = modelSummary (zeroValue M) fd (zeroValue M) av)
    (hfd : leValue M (numeralValue M 1) fd) :
    stats.value ![implication.value ![a, b] ] =
      modelSummary (zeroValue M) fd (zeroValue M) av := by
  let := modelLinearOrder M
  have hf' : numeralValue M 1 ≤ fd := hfd
  have hav : zeroValue M ≤ av := zero_le_value av
  have hf0 : fd ≠ zeroValue M := by
    intro h
    have hh := le_antisymm_value (h ▸ hfd) (zero_le_value (numeralValue M 1))
    exact (by decide : (1 : ℕ) ≠ 0) ((numeral_eq_zero_iff_model 1).mp hh)
  rw [implication_node_value]
  rw [stats_imp_modelNode_value]
  simp only [statsPart_summary _ _ _ _ _ ha, statsPart_summary _ _ _ _ _ hb,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons, hf0, or_self, ↓reduceIte,
    maximum_value, max_eq_right hf', max_self, max_eq_right hav]

theorem neg_stats (a fd av : M)
    (ha : stats.value ![a] = modelSummary (zeroValue M) fd (zeroValue M) av)
    (hfd : leValue M (numeralValue M 1) fd) :
    stats.value ![negValue a] = modelSummary (zeroValue M) fd (zeroValue M) av := by
  let := modelLinearOrder M
  have hf' : numeralValue M 1 ≤ fd := hfd
  have hav : zeroValue M ≤ av := zero_le_value av
  have hf0 : fd ≠ zeroValue M := by
    intro h
    have hh := le_antisymm_value (h ▸ hfd) (zero_le_value (numeralValue M 1))
    exact (by decide : (1 : ℕ) ≠ 0) ((numeral_eq_zero_iff_model 1).mp hh)
  rw [negValue, implication_node_value]
  rw [stats_imp_modelNode_value]
  simp only [statsPart_summary _ _ _ _ _ ha,
    statsPart_summary _ _ _ _ _ stats_bot_modelNode_value,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons, hf0, numeral_eq_zero_iff_model, Nat.one_ne_zero,
    false_or, ↓reduceIte, maximum_value, max_eq_right hf', max_eq_left hf',
    max_self, max_eq_right hav, max_eq_left hav]

theorem or_stats_same (a b fd av : M)
    (ha : stats.value ![a] = modelSummary (zeroValue M) fd (zeroValue M) av)
    (hb : stats.value ![b] = modelSummary (zeroValue M) fd (zeroValue M) av)
    (hfd : leValue M (numeralValue M 1) fd) :
    stats.value ![orValue a b] = modelSummary (zeroValue M) fd (zeroValue M) av :=
  imp_stats_same _ _ fd av (neg_stats a fd av ha hfd) hb hfd

theorem segmentDisjunction_stats (z td av : M)
    (hz : stats.value ![z] = modelSummary td (zeroValue M) (zeroValue M) av)
    (htd : leValue M (numeralValue M 1) td) (n : M) :
    stats.value ![segmentDisjunction.value ![z, n] ] =
      modelSummary (zeroValue M) td (zeroValue M) av := by
  apply definable_induction
    (fun n => stats.value ![segmentDisjunction.value ![z, n] ] =
      modelSummary (zeroValue M) td (zeroValue M) av)
  · change DPred (fun v : Fin 1 → M => stats.value ![segmentDisjunction.value ![z, v 0] ] =
      modelSummary (zeroValue M) td (zeroValue M) av)
    pa_definable
  · rw [segmentDisjunction_zero_value]
    exact equal_numeral_stats z td av _ hz htd
  · intro k hk
    rw [segmentDisjunction_successor_value]
    exact or_stats_same _ _ td av hk (equal_numeral_stats z td av _ hz htd) htd

theorem rewrite_slot_neg_value (i t a : M) :
    rewrite.value ![numeralValue M 2, i, t, negValue a] =
      negValue (rewrite.value ![numeralValue M 2, i, t, a]) := by
  simp only [negValue, implication_node_value]
  rw [rewrite_slot_imp_value, rewrite_slot_nonleaf_value 3 (by decide) (by decide) (by decide)]
  rfl

theorem rewrite_slot_or_value (i t a b : M) :
    rewrite.value ![numeralValue M 2, i, t, orValue a b] =
      orValue (rewrite.value ![numeralValue M 2, i, t, a])
        (rewrite.value ![numeralValue M 2, i, t, b]) := by
  rw [orValue, implication_node_value]
  rw [rewrite_slot_imp_value, rewrite_slot_neg_value]
  rw [orValue, implication_node_value]

theorem segmentDisjunction_rewrite (i t z n : M) :
    rewrite.value ![numeralValue M 2, i, t, segmentDisjunction.value ![z, n] ] =
      segmentDisjunction.value ![rewrite.value ![numeralValue M 2, i, t, z], n] := by
  apply definable_induction
    (fun n => rewrite.value ![numeralValue M 2, i, t, segmentDisjunction.value ![z, n] ] =
      segmentDisjunction.value ![rewrite.value ![numeralValue M 2, i, t, z], n])
  · change DPred (fun v : Fin 1 → M =>
      rewrite.value ![numeralValue M 2, i, t, segmentDisjunction.value ![z, v 0] ] =
        segmentDisjunction.value ![rewrite.value ![numeralValue M 2, i, t, z], v 0])
    pa_definable
  · rw [segmentDisjunction_zero_value, segmentDisjunction_zero_value,
      rewrite_slot_equal_value, rewrite_slot_numeral_value]
  · intro k hk
    rw [segmentDisjunction_successor_value, segmentDisjunction_successor_value,
      rewrite_slot_or_value, hk, rewrite_slot_equal_value, rewrite_slot_numeral_value]

theorem segmentDisjunction_occursAux_zero (j z : M)
    (hz : occursAux.value ![j, z] = zeroValue M) (n : M) :
    occursAux.value ![j, segmentDisjunction.value ![z, n] ] = zeroValue M := by
  have hneg (a : M) (ha : occursAux.value ![j, a] = zeroValue M) :
      occursAux.value ![j, negValue a] = zeroValue M := by
    rw [negValue, implication_node_value]
    apply occursAux_modelNode_zero j 6 _ (by decide)
    intro x hx
    simp only [Nat.reduceEqDiff, or_self, ↓reduceIte, List.mem_cons, List.not_mem_nil,
      or_false] at hx
    rcases hx with rfl | rfl
    · exact ha
    · apply occursAux_modelNode_zero j 3 _ (by decide)
      simp
  have heq (k : M) :
      occursAux.value ![j, modelNode 4 [z, ProofPrograms.numeral.value ![k] ] ] = zeroValue M := by
    apply occursAux_modelNode_zero j 4 _ (by decide)
    intro x hx
    simp only [Nat.reduceEqDiff, or_self, ↓reduceIte, List.mem_cons, List.not_mem_nil,
      or_false] at hx
    rcases hx with rfl | rfl
    · exact hz
    · exact numeral_occursAux_zero j k
  apply definable_induction
    (fun n => occursAux.value ![j, segmentDisjunction.value ![z, n] ] = zeroValue M)
  · change DPred (fun v : Fin 1 → M =>
      occursAux.value ![j, segmentDisjunction.value ![z, v 0] ] = zeroValue M)
    pa_definable
  · rw [segmentDisjunction_zero_value]
    exact heq _
  · intro k hk
    rw [segmentDisjunction_successor_value]
    rw [orValue, implication_node_value]
    apply occursAux_modelNode_zero j 6 _ (by decide)
    intro x hx
    simp only [Nat.reduceEqDiff, or_self, ↓reduceIte, List.mem_cons, List.not_mem_nil,
      or_false] at hx
    rcases hx with rfl | rfl
    · exact hneg _ hk
    · exact heq _

theorem modelTermCode_occursAux_zero {α : Type*} (j : M) (name : α → M)
    (t : language.Term α) (hn : ∀ i, occursAux.value ![j, name i] = zeroValue M) :
    occursAux.value ![j, modelTermCode name t] = zeroValue M := by
  induction t with
  | var i => exact hn i
  | @func n f ts ih =>
    rw [modelTermCode]
    apply occursAux_modelNode_zero j 2 _ (by decide)
    intro a ha
    simp only [Nat.reduceEqDiff, true_or, ↓reduceIte, List.tail_cons, List.mem_ofFn] at ha
    obtain ⟨i, rfl⟩ := ha
    exact ih i

theorem modelFormulaCodeAt_occursAux_zero {α : Type*} (j : M) (name : α → M)
    (offset : ℕ) {k : ℕ} (A : language.BoundedFormula α k)
    (hn : ∀ i, occursAux.value ![j, name i] = zeroValue M) :
    occursAux.value ![j, modelFormulaCodeAt name offset A] = zeroValue M := by
  have hnames (k : ℕ) (i : α ⊕ Fin k) : occursAux.value
      ![j, (Sum.elim name (fun i => modelNode 1 [numeralValue M (offset + i.val)])) i] =
        zeroValue M := by
    cases i with
    | inl i => exact hn i
    | inr i => exact occursAux_original_leaf_zero j 1 _ (Or.inr rfl)
  have hnode (tag : ℕ) (xs : List M) (ht : tag ≠ 8)
      (hx : ∀ a ∈ xs, occursAux.value ![j, a] = zeroValue M) :
      occursAux.value ![j, modelNode tag xs] = zeroValue M :=
    occursAux_modelNode_zero j tag xs ht (by
      intro a ha
      split_ifs at ha with h
      · exact hx a (List.mem_of_mem_tail ha)
      · exact hx a ha)
  induction A with
  | falsum => exact hnode 3 [] (by decide) (by simp)
  | equal s t =>
    apply hnode 4 _ (by decide)
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact modelTermCode_occursAux_zero j _ s (hnames _)
    · exact modelTermCode_occursAux_zero j _ t (hnames _)
  | rel e _ => exact e.elim
  | imp a b ha hb =>
    apply hnode 6 _ (by decide)
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact ha
    · exact hb
  | all a ha =>
    apply hnode 7 _ (by decide)
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    exact hx ▸ ha

end
end Lemmatheca.ProofTheory.PAComputations.ProofPrograms.InitialSegmentPrograms
