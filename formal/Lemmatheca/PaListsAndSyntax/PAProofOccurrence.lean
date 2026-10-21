import Lemmatheca.PaListsAndSyntax.PASyntaxOperations
import Lemmatheca.PaListsAndSyntax.PANumeralSyntax

open Lemmatheca.MathematicalLogic Lemmatheca.ModelTheory Lemmatheca.ComputabilityTheory

namespace Lemmatheca.ProofTheory.PAComputations.ProofPrograms.CheckerPrograms
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic ArithmeticTheories ArithmeticRepresentability
open SyntaxPrograms
noncomputable section
universe u
variable {M : Type u} [language.Structure M] [M ⊨ PA]
local instance proofOccurrenceLocalInstance1 (P : Prop) : Decidable P := Classical.propDecidable P

def occursHistoryValue (j e : M) : M := (history occursStep).value ![j, e]

theorem occurs_equation_value (j e : M) :
    occursAux.value ![j, e] = sign.value ![occursStep.value ![j, e, occursHistoryValue j e] ] := by
  have hv (a : M) : Fin.snoc (![j] : Fin 1 → M) a = ![j, a] := by
    ext i; fin_cases i <;> rfl
  have hv3 (a b : M) : Fin.snoc (![j, a] : Fin 2 → M) b = ![j, a, b] := by
    ext i; fin_cases i <;> rfl
  have he := courseValue_value occursStep (![j] : Fin 1 → M) e
  simp only [hv, hv3] at he
  simp only [occursAux, unary_value, he, occursHistoryValue]

theorem occurs_history_entry_value (j e c : M) (hc : leValue M (succValue M c) e) :
    sign.value ![listEntry.value ![occursHistoryValue j e, c] ] = occursAux.value ![j, c] := by
  have hv (a : M) : Fin.snoc (![j] : Fin 1 → M) a = ![j, a] := by
    ext i; fin_cases i <;> rfl
  have he := history_entry_value occursStep (![j] : Fin 1 → M) e c hc
  simp only [hv] at he
  unfold occursHistoryValue
  rw [he]
  simp only [occursAux, unary_value]

theorem occurrenceChild_value (hist a z : M) :
    occurrenceChild.value ![hist, a, z] = disjoin.value ![z, sign.value ![listEntry.value ![hist, a] ] ] := by
  simp only [occurrenceChild, binary_value, unary_value, Program.value_proj,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.head_cons]

theorem occursStep_modelNode_value (j hist : M) (k : ℕ) (xs : List M) :
    occursStep.value ![j, modelNode k xs, hist] =
      if k = 8 then truthValue (M := M) (xs[0]?.getD (zeroValue M) = j)
      else if k = 0 ∨ k = 1 then zeroValue M
      else (paramFold occurrenceChild).value
        ![hist, modelList (if k = 2 ∨ k = 5 then xs.tail else xs), zeroValue M] := by
  simp only [occursStep, ternary_value, binary_value, unary_value, Program.value_proj,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.head_cons, tag_modelNode_value, argument_modelNode_value,
    children_modelNode_value, constant_value, equalTest_truthValue, disjoin_truthValue,
    numeral_eq_iff_model, select_truthValue, numeral_value_zero, numeral_eq_zero_iff_model]
  split_ifs <;> rfl

/-- An original-language constructor introduces no auxiliary name.  The
hypothesis mentions only actual child codes; a function-symbol header is skipped. -/
theorem occursAux_modelNode_zero (j : M) (k : ℕ) (xs : List M) (hk : k ≠ 8)
    (hall : ∀ a ∈ (if k = 2 ∨ k = 5 then xs.tail else xs),
      occursAux.value ![j, a] = zeroValue M) :
    occursAux.value ![j, modelNode k xs] = zeroValue M := by
  rw [occurs_equation_value, occursStep_modelNode_value]
  simp only [hk, ↓reduceIte]
  by_cases hleaf : k = 0 ∨ k = 1
  · simp only [hleaf, ↓reduceIte, sign_zero_value]
  · simp only [hleaf, ↓reduceIte]
    have hfold : (paramFold occurrenceChild).value
        ![occursHistoryValue j (modelNode k xs),
          modelList (if k = 2 ∨ k = 5 then xs.tail else xs), zeroValue M] = zeroValue M := by
      let ys := if k = 2 ∨ k = 5 then xs.tail else xs
      have hsub : ∀ a ∈ ys, a ∈ xs := by
        dsimp only [ys]
        split_ifs
        · exact fun _ h => List.mem_of_mem_tail h
        · exact fun _ h => h
      have haux : ∀ zs : List M, (∀ a ∈ zs, a ∈ xs) →
          (∀ a ∈ zs, occursAux.value ![j, a] = zeroValue M) →
          (paramFold occurrenceChild).value
            ![occursHistoryValue j (modelNode k xs), modelList zs, zeroValue M] = zeroValue M := by
        intro zs
        induction zs with
        | nil => intro _ _; rw [modelList_nil, paramFold_zero_value]
        | cons a zs ih =>
          intro hs hh
          rw [modelList_cons, paramFold_cons_value, occurrenceChild_value,
            occurs_history_entry_value j _ a (modelNode_child_smaller k xs a (hs a (by simp))),
            hh a (by simp), disjoin_value]
          simp only [and_self, ↓reduceIte]
          exact ih (fun b hb => hs b (by simp [hb])) (fun b hb => hh b (by simp [hb]))
      exact haux ys hsub hall
    rw [hfold, sign_zero_value]


theorem contextFresh_zero_value (j : M) :
    contextFresh.value ![j, zeroValue M] = numeralValue M 1 := listAll_zero_value _ _

theorem contextFresh_cons_one_iff (j a gamma : M) :
    contextFresh.value ![j, listCons.value ![a, gamma] ] = numeralValue M 1 ↔
      occursAux.value ![j, a] = zeroValue M ∧ contextFresh.value ![j, gamma] = numeralValue M 1 := by
  unfold contextFresh
  rw [listAll_cons_one_iff, booleanNot_value]
  simp only [ite_eq_left_iff, zero_eq_numeral_iff_model, Nat.one_ne_zero,
    imp_false, not_not]

theorem contextFresh_append_value (j gamma delta : M) :
    contextFresh.value ![j, listAppend.value ![gamma, delta] ] =
      mulValue M (contextFresh.value ![j, gamma]) (contextFresh.value ![j, delta]) :=
  listAll_append_value _ j gamma delta

theorem numeral_occursAux_zero (j n : M) :
    occursAux.value ![j, ProofPrograms.numeral.value ![n] ] = zeroValue M := by
  apply definable_induction
    (fun n => occursAux.value ![j, ProofPrograms.numeral.value ![n] ] = zeroValue M)
  · change DPred (fun v : Fin 1 → M =>
      occursAux.value ![j, ProofPrograms.numeral.value ![v 0] ] = zeroValue M)
    pa_definable
  · rw [numeral_zero_modelNode_value]
    apply occursAux_modelNode_zero j 2 _ (by decide)
    simp only [Nat.reduceEqDiff, true_or, ↓reduceIte, List.tail_cons, List.not_mem_nil,
      IsEmpty.forall_iff, implies_true]
  · intro k hk
    rw [numeral_successor_modelNode_value]
    apply occursAux_modelNode_zero j 2 _ (by decide)
    intro a ha
    simp only [Nat.reduceEqDiff, ↓reduceIte, List.tail_cons,
      List.mem_cons, List.not_mem_nil, or_false] at ha
    exact ha ▸ hk

theorem numeral_namedTerm (n : M) :
    namedTerm.value ![ProofPrograms.numeral.value ![n] ] = numeralValue M 1 := by
  simp only [namedTerm, binary_value, unary_value, Program.value_proj,
    Matrix.cons_val_zero, constant_value, numeral_value_zero, numeral_wellformed,
    booleanNot_value, numeral_stats_value, modelSummary_part_value,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, ↓reduceIte, multiplication_value, numeral_one_mul_model]


end
end Lemmatheca.ProofTheory.PAComputations.ProofPrograms.CheckerPrograms
