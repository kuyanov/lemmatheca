import Lemmatheca.PaDegrees.FiniteExtensions
import Lemmatheca.OracleProgramNumberings.Parameters

set_option autoImplicit false

namespace Lemmatheca.ComputabilityTheory.PaDegrees

open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic Lemmatheca.ModelTheory Lemmatheca.ProofTheory
open ArithmeticTheories FirstOrderProofs CodingFormalProofs Theories
open UniversalComputation TuringDegrees OracleComputation EffectivelyClosedClassesAndDnc
open BusyBeaverFunctions OracleProgramNumberings

noncomputable section
attribute [local irreducible] contradictionIndex

def stageSentence (n : ℕ) : language.Sentence :=
  if h : isSentence arithmeticSignature n = true then
    Classical.choose ((sentence_recognition_iff arithmeticSignature n).mp h)
  else ⊤

def stageCode (n : ℕ) : ℕ :=
  if isSentence arithmeticSignature n then n else sentenceCode arithmeticSignature ⊤

theorem stage_code_primitive : Primrec stageCode := by
  exact Primrec.ite
    (Primrec.eq.comp (primrec_isSentence arithmeticSignature) (Primrec.const true))
    Primrec.id (Primrec.const (sentenceCode arithmeticSignature ⊤))

theorem stage_sentence_code (n : ℕ) :
    sentenceCode arithmeticSignature (stageSentence n) = stageCode n := by
  unfold stageSentence stageCode
  split
  · exact Classical.choose_spec ((sentence_recognition_iff arithmeticSignature n).mp ‹_›)
  · rfl

theorem stage_sentence_at_code (A : language.Sentence) :
    stageSentence (sentenceCode arithmeticSignature A) = A := by
  apply sentence_code_injective arithmeticSignature
  rw [stage_sentence_code]
  simp only [stageCode, (sentence_recognition_iff arithmeticSignature _).mpr ⟨A, rfl⟩, ↓reduceIte]

def choiceBit (D : Set ℕ) (L n : ℕ) : ℕ :=
  indicator (fun e => e ∈ D) (contradictionIndex L (stageCode n))

def completionHistory (D : Set ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => appendSentence (completionHistory D n)
      (signedChoice (stageCode n) (choiceBit D (completionHistory D n) n))

def chosenTheory (D : Set ℕ) : language.Theory :=
  PA ∪ {A | ∃ n, sentenceCode arithmeticSignature A ∈ Seq.decode (completionHistory D n)}

def completedTheory (D : Set ℕ) : language.Theory := consequenceClosure (chosenTheory D)

private theorem decode_append_sentence (L a : ℕ) :
    Seq.decode (appendSentence L a) = Seq.decode L ++ [a] := by
  simp only [appendSentence, Seq.append, FiniteSequenceCoding.decode_code]

private theorem valid_signed_code (a b : ℕ) (ha : isSentence arithmeticSignature a = true) :
    isSentence arithmeticSignature (signedChoice a b) = true := by
  by_cases hb : b = 0
  · simpa only [signedChoice, hb, ↓reduceIte] using ha
  · obtain ⟨A, rfl⟩ := (sentence_recognition_iff arithmeticSignature a).mp ha
    simpa only [signedChoice, hb, ↓reduceIte, negation_code] using
      (sentence_recognition_iff arithmeticSignature _).mpr ⟨A.not, rfl⟩

private theorem chosen_at_stage (D : Set ℕ) (n : ℕ) :
    (if choiceBit D (completionHistory D n) n = 0 then stageSentence n else (stageSentence n).not) ∈
      chosenTheory D := by
  classical
  by_cases hb : choiceBit D (completionHistory D n) n = 0
  · simp only [hb, ↓reduceIte]
    refine Or.inr ⟨n + 1, ?_⟩
    rw [completionHistory, decode_append_sentence, signedChoice, ite_eq_left hb, stage_sentence_code]
    exact List.mem_append_right _ (by simp)
  · simp only [hb, ↓reduceIte]
    refine Or.inr ⟨n + 1, ?_⟩
    rw [completionHistory, decode_append_sentence, signedChoice, ite_eq_right hb,
      ← negation_code arithmeticSignature (stageSentence n), stage_sentence_code]
    exact List.mem_append_right _ (by simp)

theorem completion_history_invariant (D : Set ℕ) (hD : D ∈ binaryDNCClass) (n : ℕ) :
    ValidSentenceList (completionHistory D n) ∧
      (Seq.decode (completionHistory D n)).IsPrefix (Seq.decode (completionHistory D (n + 1))) ∧
      Consistent (finiteTheory (completionHistory D n)) := by
  have hp (k : ℕ) : (Seq.decode (completionHistory D k)).IsPrefix
      (Seq.decode (completionHistory D (k + 1))) := by
    rw [completionHistory, decode_append_sentence]
    exact ⟨_, rfl⟩
  have hi (k : ℕ) : ValidSentenceList (completionHistory D k) ∧
      Consistent (finiteTheory (completionHistory D k)) := by
    induction k with
    | zero =>
      refine ⟨?_, ?_⟩
      · simp [ValidSentenceList, completionHistory, Seq.decode]
      · simpa [completionHistory, finiteTheory, Seq.decode] using PA_consistent
    | succ k ih =>
      refine ⟨?_, ?_⟩
      · intro a ha
        rw [completionHistory, decode_append_sentence] at ha
        rcases List.mem_append.mp ha with h | h
        · exact ih.1 a h
        · have he : a = signedChoice (stageCode k) (choiceBit D (completionHistory D k) k) := by
            simpa only [List.mem_singleton] using h
          subst a
          apply valid_signed_code
          rw [← stage_sentence_code]
          exact (sentence_recognition_iff arithmeticSignature _).mpr ⟨stageSentence k, rfl⟩
      · simpa only [completionHistory, stage_sentence_code, choiceBit] using
          safe_choice D hD (completionHistory D k) ih.2 (stageSentence k)
  exact ⟨(hi n).1, hp n, (hi n).2⟩

theorem chosen_theory_consistent (D : Set ℕ) (hD : D ∈ binaryDNCClass) :
    Consistent (chosenTheory D) := by
  classical
  have hmon : Monotone (fun n => finiteTheory (completionHistory D n)) := by
    apply monotone_nat_of_le_succ
    intro n A hA
    rcases hA with hA | hA
    · exact Or.inl hA
    · exact Or.inr (((completion_history_invariant D hD n).2.1).subset hA)
  rintro ⟨Γ, hΓ, hproof⟩
  have heach (A : Γ) : ∃ n, A.val ∈ finiteTheory (completionHistory D n) := by
    rcases hΓ A.property with hA | ⟨n, hn⟩
    · exact ⟨0, Or.inl hA⟩
    · exact ⟨n, Or.inr hn⟩
  choose stage hstage using heach
  let N := Finset.univ.sup stage
  apply (completion_history_invariant D hD N).2.2
  refine ⟨Γ, ?_, hproof⟩
  intro A hA
  have hN : stage (⟨A, hA⟩ : Γ) ≤ N := Finset.le_sup (Finset.mem_univ _)
  exact hmon hN (hstage ⟨A, hA⟩)

theorem chosen_theory_decides (D : Set ℕ) (A : language.Sentence) :
    A ∈ chosenTheory D ∨ A.not ∈ chosenTheory D := by
  have h := chosen_at_stage D (sentenceCode arithmeticSignature A)
  rw [stage_sentence_at_code] at h
  split at h
  · exact Or.inl h
  · exact Or.inr h

theorem greedy_completion (D : Set ℕ) (hD : D ∈ binaryDNCClass) :
    PACompletion (completedTheory D) := by
  have hc : Consistent (completedTheory D) := by
    obtain ⟨M, hM, hne, _, hmodel⟩ :=
      Lemmatheca.MathematicalLogic.HenkinCompleteness.countable_model_existence
        (chosen_theory_consistent D hD)
    let := hM
    let := hne
    let := hmodel
    have hm : M ⊨ completedTheory D := (model_closure (chosenTheory D) M).mpr hmodel
    exact theory_consistent_of_model hm
  refine ⟨fun _ h => subset_closure _ (Or.inl h), hc, ?_, closure_idempotent (chosenTheory D)⟩
  apply (complete_iff_consistent_decides _).mpr
  refine ⟨hc, fun A => ?_⟩
  exact (chosen_theory_decides D A).imp
    (fun h => derives_assumption (subset_closure _ h))
    (fun h => derives_assumption (subset_closure _ h))

theorem completed_sentence_choice (D : Set ℕ) (hD : D ∈ binaryDNCClass)
    (A : language.Sentence) :
    A ∈ completedTheory D ↔
      choiceBit D (completionHistory D (sentenceCode arithmeticSignature A))
        (sentenceCode arithmeticSignature A) = 0 := by
  classical
  let n := sentenceCode arithmeticSignature A
  change A ∈ completedTheory D ↔ choiceBit D (completionHistory D n) n = 0
  have hs : stageSentence n = A := stage_sentence_at_code A
  by_cases hb : choiceBit D (completionHistory D n) n = 0
  · refine ⟨fun _ => hb, fun _ => ?_⟩
    have h := chosen_at_stage D n
    simp only [hb, ↓reduceIte, hs] at h
    exact subset_closure _ h
  · refine ⟨?_, fun h => False.elim (hb h)⟩
    intro hA
    have h := chosen_at_stage D n
    simp only [hb, ↓reduceIte, hs] at h
    have hn : A.not ∈ completedTheory D := subset_closure _ h
    exact False.elim ((completion_exactly_one _ (greedy_completion D hD) A).2 ⟨hA, hn⟩)

/-- A primitive-recursion step receives (parameter,(stage,previous list)). -/
private def historyQueryInput (z : ℕ) : ℕ :=
  contradictionIndex z.unpair.2.unpair.2 (stageCode z.unpair.2.unpair.1)

private def historyUpdate (w : ℕ) : ℕ :=
  appendSentence w.unpair.1.unpair.2.unpair.2
    (signedChoice (stageCode w.unpair.1.unpair.2.unpair.1) w.unpair.2)

private def finalQueryInput (z : ℕ) : ℕ := contradictionIndex z.unpair.2 (stageCode z.unpair.1)

private def syntaxBit (n : ℕ) : ℕ := if isSentence arithmeticSignature n then 1 else 0

private theorem history_query_input_computable : Computable historyQueryInput := by
  have hr : Primrec (fun z : ℕ => z.unpair.2) := Primrec.snd.comp Primrec.unpair
  have hn := (Primrec.fst.comp Primrec.unpair).comp hr
  have hL := hr.comp hr
  exact (contradiction_index_primitive.comp hL (stage_code_primitive.comp hn)).to_comp
private theorem history_update_computable : Computable historyUpdate := by
  have hl : Primrec (fun z : ℕ => z.unpair.1) := Primrec.fst.comp Primrec.unpair
  have hr : Primrec (fun z : ℕ => z.unpair.2) := Primrec.snd.comp Primrec.unpair
  have hn := hl.comp (hr.comp hl)
  have hL := hr.comp (hr.comp hl)
  exact (append_sentence_primitive.comp hL
    (signed_choice_primitive.comp (stage_code_primitive.comp hn) hr)).to_comp
private theorem final_query_input_computable : Computable finalQueryInput := by
  have hl : Primrec (fun z : ℕ => z.unpair.1) := Primrec.fst.comp Primrec.unpair
  have hr : Primrec (fun z : ℕ => z.unpair.2) := Primrec.snd.comp Primrec.unpair
  exact (contradiction_index_primitive.comp hr (stage_code_primitive.comp hl)).to_comp
private theorem syntax_bit_computable : Computable syntaxBit := by
  exact (Primrec.ite
    (Primrec.eq.comp (primrec_isSentence arithmeticSignature) (Primrec.const true))
    (Primrec.const 1) (Primrec.const 0)).to_comp
private theorem flip_bit_computable : Computable (fun n : ℕ => 1 - n) := by
  exact (Primrec.nat_sub.comp (Primrec.const 1) Primrec.id).to_comp

private def historyStepCode : OracleComputation.Code :=
  .comp (embed (ordinaryProgram historyUpdate history_update_computable))
    (.pair identityCode
      (.comp .query (embed (ordinaryProgram historyQueryInput history_query_input_computable))))

/-- One program computes the specified finite list for every supplied set oracle. -/
def historyProgram : OracleComputation.Code :=
  .comp (.prec .zero historyStepCode) (.pair .zero identityCode)

private def validCompletionProgram : OracleComputation.Code :=
  .comp (embed (ordinaryProgram (fun n : ℕ => 1 - n) flip_bit_computable))
    (.comp .query (.comp (embed (ordinaryProgram finalQueryInput final_query_input_computable))
      (.pair identityCode historyProgram)))

/-- The initial zero-or-one primitive recursion rejects malformed codes without querying. -/
def completionProgram : OracleComputation.Code :=
  .comp (.prec .zero (.comp validCompletionProgram .left))
    (.pair identityCode (embed (ordinaryProgram syntaxBit syntax_bit_computable)))

theorem history_program_eval (D : Set ℕ) (n : ℕ) :
    eval D historyProgram n = Part.some (completionHistory D n) := by
  have hs (k L : ℕ) : eval D historyStepCode (Nat.pair 0 (Nat.pair k L)) =
      Part.some (appendSentence L (signedChoice (stageCode k) (choiceBit D L k))) := by
    simp [historyStepCode, eval, identity_eval, eval_embed, ordinaryProgram_eval,
      historyQueryInput, historyUpdate, choiceBit]
  have hr (k : ℕ) : eval D (.prec .zero historyStepCode) (Nat.pair 0 k) =
      Part.some (completionHistory D k) := by
    induction k with
    | zero => simp [eval, completionHistory]
    | succ k ih =>
      rw [eval_prec_succ, ih, Part.bind_some]
      exact hs k (completionHistory D k)
  have hp : eval D (.pair .zero identityCode) n = Part.some (Nat.pair 0 n) := by
    simp [eval, identity_eval]
  change (eval D (.pair .zero identityCode) n).bind
    (eval D (.prec .zero historyStepCode)) = _
  rw [hp, Part.bind_some]
  exact hr n

theorem completion_program_eval (D : Set ℕ) (n : ℕ) :
    eval D completionProgram n = Part.some
      (if isSentence arithmeticSignature n then
        1 - choiceBit D (completionHistory D n) n else 0) := by
  have hv (x : ℕ) : eval D validCompletionProgram x =
      Part.some (1 - choiceBit D (completionHistory D x) x) := by
    simp [validCompletionProgram, eval, identity_eval, eval_embed, ordinaryProgram_eval,
      history_program_eval, finalQueryInput, choiceBit]
  have hp : eval D (.pair identityCode (embed (ordinaryProgram syntaxBit syntax_bit_computable))) n =
      Part.some (Nat.pair n (syntaxBit n)) := by
    simp [eval, identity_eval, eval_embed, ordinaryProgram_eval]
  change (eval D (.pair identityCode (embed (ordinaryProgram syntaxBit syntax_bit_computable))) n).bind
    (eval D (.prec .zero (.comp validCompletionProgram .left))) = _
  rw [hp, Part.bind_some]
  by_cases h : isSentence arithmeticSignature n = true
  · simp only [syntaxBit, h, ↓reduceIte]
    rw [eval_prec_succ, eval_prec_zero]
    simpa only [eval, Nat.unpair_pair, Part.bind_some] using hv n
  · have hz : syntaxBit n = 0 := by simp [syntaxBit, h]
    rw [hz, eval_prec_zero]
    simp only [ite_eq_right h, eval]

theorem completion_program_reduces (D : Set ℕ) (hD : D ∈ binaryDNCClass) :
    Reduces completionProgram (completionCodes (completedTheory D)) D := by
  classical
  intro n
  rw [completion_program_eval]
  apply congrArg Part.some
  by_cases hv : isSentence arithmeticSignature n = true
  · obtain ⟨A, rfl⟩ := (sentence_recognition_iff arithmeticSignature n).mp hv
    rw [ite_eq_left hv]
    have he : (sentenceCode arithmeticSignature A ∈ completionCodes (completedTheory D)) ↔
        choiceBit D (completionHistory D (sentenceCode arithmeticSignature A))
          (sentenceCode arithmeticSignature A) = 0 :=
      (completion_codes_sentence (completedTheory D) A).trans (completed_sentence_choice D hD A)
    have hb : choiceBit D (completionHistory D (sentenceCode arithmeticSignature A))
        (sentenceCode arithmeticSignature A) = 0 ∨
        choiceBit D (completionHistory D (sentenceCode arithmeticSignature A))
          (sentenceCode arithmeticSignature A) = 1 := by
      unfold choiceBit
      by_cases hq : contradictionIndex (completionHistory D (sentenceCode arithmeticSignature A))
          (stageCode (sentenceCode arithmeticSignature A)) ∈ D
      · exact Or.inr (by simp only [indicator, hq, ↓reduceIte])
      · exact Or.inl (by simp only [indicator, hq, ↓reduceIte])
    rcases hb with hb | hb
    · rw [hb, Nat.sub_zero]
      simp only [indicator, he.mpr hb, ↓reduceIte]
    · rw [hb, Nat.sub_self]
      have hn : sentenceCode arithmeticSignature A ∉ completionCodes (completedTheory D) :=
        fun h => Nat.one_ne_zero (hb.symm.trans (he.mp h))
      simp only [indicator, hn, ↓reduceIte]
  · have hn : n ∉ completionCodes (completedTheory D) :=
      completion_codes_malformed _ n (Bool.eq_false_iff.mpr hv)
    simp only [ite_eq_right hv, indicator, hn, ↓reduceIte]

end
end Lemmatheca.ComputabilityTheory.PaDegrees
