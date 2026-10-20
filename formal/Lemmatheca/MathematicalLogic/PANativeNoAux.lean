import Lemmatheca.MathematicalLogic.PANativeInstantiation
import Lemmatheca.MathematicalLogic.PANativeSyntaxRecognition
import Lemmatheca.MathematicalLogic.PAProofOccurrence

/-! A sentence accepted by the concrete recognizer contains no auxiliary
constant, even when its code is nonstandard. -/
namespace Lemmatheca.MathematicalLogic.PAComputations.ProofPrograms.CheckerPrograms
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic ArithmeticTheories ArithmeticRepresentability
open SyntaxPrograms
noncomputable section
universe u
variable {M : Type u} [language.Structure M] [M ⊨ PA]
local instance : DecidableEq M := Classical.decEq M

private theorem maximum_zero_left_value (a : M) :
    maximum.value ![zeroValue M, a] = a := by
  let := modelLinearOrder M
  rw [maximum_value]
  exact max_eq_right (zero_le_value a)

private theorem maximum_zero_iff (a b : M) :
    maximum.value ![a, b] = zeroValue M ↔ a = zeroValue M ∧ b = zeroValue M := by
  let := modelLinearOrder M
  rw [maximum_value]
  constructor
  · intro h
    exact ⟨le_antisymm (h ▸ le_max_left a b) (zero_le_value a),
      le_antisymm (h ▸ le_max_right a b) (zero_le_value b)⟩
  · rintro ⟨rfl, rfl⟩
    exact max_self _

private theorem occurs_leaf_zero (j a : M) (k : ℕ) (hk : k = 0 ∨ k = 1) :
    occursAux.value ![j, modelNode k [a] ] = zeroValue M := by
  rw [occurs_equation_value, occursStep_modelNode_value]
  have h8 : k ≠ 8 := by omega
  simp only [h8, hk, ↓reduceIte, sign_zero_value]

private theorem aux_succ_zero (a : M) (ha : termDepth a ≠ zeroValue M)
    (h : statsPart 3 (modelNode 2 [numeralValue M 1, a]) = zeroValue M) :
    statsPart 3 a = zeroValue M := by
  change (part 3).value ![stats.value ![modelNode 2 [numeralValue M 1, a] ] ] = _ at h
  change statsPart 0 a ≠ zeroValue M at ha
  rw [stats_succ_modelNode_value, ite_eq_right ha] at h
  simpa only [modelSummary_part_value, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, maximum_zero_left_value] using h

private theorem aux_binary_zero (k : ℕ) (hk : k = 2 ∨ k = 3)
    (a b : M) (ha : termDepth a ≠ zeroValue M) (hb : termDepth b ≠ zeroValue M)
    (h : statsPart 3 (modelNode 2 [numeralValue M k, a, b]) = zeroValue M) :
    statsPart 3 a = zeroValue M ∧ statsPart 3 b = zeroValue M := by
  change (part 3).value ![stats.value ![modelNode 2 [numeralValue M k, a, b] ] ] = _ at h
  have hn : ¬ (statsPart 0 a = zeroValue M ∨ statsPart 0 b = zeroValue M) :=
    not_or.mpr ⟨ha, hb⟩
  rw [stats_binary_modelNode_value k hk, ite_eq_right hn] at h
  apply (maximum_zero_iff _ _).mp
  simpa only [modelSummary_part_value, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, maximum_zero_left_value] using h

private theorem aux_equal_zero (a b : M)
    (ha : termDepth a ≠ zeroValue M) (hb : termDepth b ≠ zeroValue M)
    (h : statsPart 3 (modelNode 4 [a, b]) = zeroValue M) :
    statsPart 3 a = zeroValue M ∧ statsPart 3 b = zeroValue M := by
  change (part 3).value ![stats.value ![modelNode 4 [a, b] ] ] = _ at h
  have hn : ¬ (statsPart 0 a = zeroValue M ∨ statsPart 0 b = zeroValue M) :=
    not_or.mpr ⟨ha, hb⟩
  rw [stats_equal_modelNode_value, ite_eq_right hn] at h
  apply (maximum_zero_iff _ _).mp
  simpa only [modelSummary_part_value, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, maximum_zero_left_value] using h

private theorem aux_imp_zero (a b : M)
    (ha : formDepth a ≠ zeroValue M) (hb : formDepth b ≠ zeroValue M)
    (h : statsPart 3 (modelNode 6 [a, b]) = zeroValue M) :
    statsPart 3 a = zeroValue M ∧ statsPart 3 b = zeroValue M := by
  change (part 3).value ![stats.value ![modelNode 6 [a, b] ] ] = _ at h
  have hn : ¬ (statsPart 1 a = zeroValue M ∨ statsPart 1 b = zeroValue M) :=
    not_or.mpr ⟨ha, hb⟩
  rw [stats_imp_modelNode_value, ite_eq_right hn] at h
  apply (maximum_zero_iff _ _).mp
  simpa only [modelSummary_part_value, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, maximum_zero_left_value] using h

private theorem aux_all_zero (a : M) (ha : formDepth a ≠ zeroValue M)
    (h : statsPart 3 (modelNode 7 [a]) = zeroValue M) : statsPart 3 a = zeroValue M := by
  change (part 3).value ![stats.value ![modelNode 7 [a] ] ] = _ at h
  change statsPart 1 a ≠ zeroValue M at ha
  rw [stats_all_modelNode_value, ite_eq_right ha] at h
  simpa only [modelSummary_part_value, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, maximum_zero_left_value] using h

/-- Simultaneous strong induction on actual term and formula codes. -/
theorem recognized_noAux (j e : M) :
    (termDepth e ≠ zeroValue M → statsPart 3 e = zeroValue M →
      occursAux.value ![j, e] = zeroValue M) ∧
    (formDepth e ≠ zeroValue M → statsPart 3 e = zeroValue M →
      occursAux.value ![j, e] = zeroValue M) := by
  have hall : ∀ e : M,
      (termDepth e ≠ zeroValue M → statsPart 3 e = zeroValue M →
        occursAux.value ![j, e] = zeroValue M) ∧
      (formDepth e ≠ zeroValue M → statsPart 3 e = zeroValue M →
        occursAux.value ![j, e] = zeroValue M) := by
    apply definable_strong_induction
    · change DPred (fun v : Fin 1 → M =>
        (termDepth (v 0) ≠ zeroValue M → statsPart 3 (v 0) = zeroValue M →
          occursAux.value ![j, v 0] = zeroValue M) ∧
        (formDepth (v 0) ≠ zeroValue M → statsPart 3 (v 0) = zeroValue M →
          occursAux.value ![j, v 0] = zeroValue M))
      unfold termDepth formDepth statsPart
      pa_definable
    · intro e ih
      constructor
      · intro he haux
        rcases termDepth_cases e he with ⟨a, rfl⟩ | ⟨a, rfl⟩ | ⟨a, rfl⟩ | rfl |
          ⟨a, rfl, ha⟩ | ⟨f, hf, a, b, rfl, ha, hb⟩
        · exact occurs_leaf_zero j a 0 (Or.inl rfl)
        · exact occurs_leaf_zero j a 1 (Or.inr rfl)
        · have hz : addValue M a (numeralValue M 1) = zeroValue M := by
            simpa only [statsPart, stats_aux_modelNode_value, modelSummary_part_value,
              Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] using haux
          rw [numeral_value_succ, numeral_value_zero, add_one_value] at hz
          exact (successor_ne_zero a hz).elim
        · apply occursAux_modelNode_zero j 2 _ (by decide)
          simp only [Nat.reduceEqDiff, true_or, ↓reduceIte, List.tail_cons,
            List.not_mem_nil, IsEmpty.forall_iff, implies_true]
        · have hc := (ih a (modelNode_child_smaller 2 _ a (by simp))).1 ha
            (aux_succ_zero a ha haux)
          apply occursAux_modelNode_zero j 2 _ (by decide)
          simpa only [Nat.reduceEqDiff, ↓reduceIte, List.tail_cons,
            List.mem_cons, List.not_mem_nil, or_false, forall_eq] using hc
        · obtain ⟨hza, hzb⟩ := aux_binary_zero f hf a b ha hb haux
          have hca := (ih a (modelNode_child_smaller 2 _ a (by simp))).1 ha hza
          have hcb := (ih b (modelNode_child_smaller 2 _ b (by simp))).1 hb hzb
          apply occursAux_modelNode_zero j 2 _ (by decide)
          intro c hc
          simp only [Nat.reduceEqDiff, ↓reduceIte, List.tail_cons,
            List.mem_cons, List.not_mem_nil, or_false] at hc
          rcases hc with rfl | rfl
          · exact hca
          · exact hcb
      · intro he haux
        rcases formDepth_cases e he with rfl | ⟨a, b, rfl, ha, hb⟩ |
          ⟨a, b, rfl, ha, hb⟩ | ⟨a, rfl, ha⟩
        · apply occursAux_modelNode_zero j 3 _ (by decide)
          simp
        · obtain ⟨hza, hzb⟩ := aux_equal_zero a b ha hb haux
          have hca := (ih a (modelNode_child_smaller 4 _ a (by simp))).1 ha hza
          have hcb := (ih b (modelNode_child_smaller 4 _ b (by simp))).1 hb hzb
          apply occursAux_modelNode_zero j 4 _ (by decide)
          intro c hc
          simp only [Nat.reduceEqDiff, ↓reduceIte,
            List.mem_cons, List.not_mem_nil, or_false] at hc
          rcases hc with rfl | rfl
          · exact hca
          · exact hcb
        · obtain ⟨hza, hzb⟩ := aux_imp_zero a b ha hb haux
          have hca := (ih a (modelNode_child_smaller 6 _ a (by simp))).2 ha hza
          have hcb := (ih b (modelNode_child_smaller 6 _ b (by simp))).2 hb hzb
          apply occursAux_modelNode_zero j 6 _ (by decide)
          intro c hc
          simp only [Nat.reduceEqDiff, ↓reduceIte,
            List.mem_cons, List.not_mem_nil, or_false] at hc
          rcases hc with rfl | rfl
          · exact hca
          · exact hcb
        · have hc := (ih a (modelNode_child_smaller 7 _ a (by simp))).2 ha
            (aux_all_zero a ha haux)
          apply occursAux_modelNode_zero j 7 _ (by decide)
          simpa only [Nat.reduceEqDiff, ↓reduceIte, List.mem_cons,
            List.not_mem_nil, or_false, forall_eq] using hc
  exact hall e

theorem isSentence_occursAux_zero (j e : M)
    (he : isSentence.value ![e] = numeralValue M 1) :
    occursAux.value ![j, e] = zeroValue M := by
  rw [isSentence_value] at he
  have hs := (truthValue_eq_one_iff (M := M) _).mp he
  exact (recognized_noAux j e).2 hs.1.1.1 hs.2

end
end Lemmatheca.MathematicalLogic.PAComputations.ProofPrograms.CheckerPrograms
