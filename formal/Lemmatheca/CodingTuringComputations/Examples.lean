import Lemmatheca.CodingTuringComputations.Simulation
import Lemmatheca.TuringMachines.Examples

namespace Lemmatheca.Entry.CodingTuringComputations

open Lemmatheca.ComputabilityTheory
open TapeCoding
open Lemmatheca.Entry.TuringMachines (binary successor SuccessorState)

private def successorStateLabels : SuccessorState ≃ Fin 3 where
  toFun
    | .scan => 0
    | .back => 1
    | .halt => 2
  invFun i := Fin.cases .scan (Fin.cases .back (fun _ => .halt)) i
  left_inv q := by cases q <;> rfl
  right_inv i := by fin_cases i <;> rfl

def successorLabels : Labeling successor where
  symbol := finTwoEquiv.symm.trans (finCongr (by decide))
  state := successorStateLabels.trans (finCongr (by decide))
  blank_zero := rfl
  mark_one := rfl
  initial_zero := rfl

private theorem represents_same_observations
    {Γ Q : Type*} {A : TuringMachines.Alphabet Γ} [Fintype Γ] [Fintype Q]
    {T : TuringMachines.Machine A Q} (L : Labeling T) (X : TuringMachines.Config A Q)
    (c d : ℕ) (hc : Represents L X c)
    (hq : stateCode d = stateCode c) (ha : currentCode d = currentCode c)
    (hl : ∀ i, FiniteSequenceCoding.entry (leftCode d) i = FiniteSequenceCoding.entry (leftCode c) i)
    (hr : ∀ i, FiniteSequenceCoding.entry (rightCode d) i = FiniteSequenceCoding.entry (rightCode c) i) :
    Represents L X d := by
  refine ⟨⟨?_, ?_, ?_, ?_⟩, hq.trans hc.2.1, ha.trans hc.2.2.1, ?_, ?_⟩
  · rw [hq]; exact hc.1.1
  · rw [ha]; exact hc.1.2.1
  · intro i _; rw [hl, hc.2.2.2.1]; exact Fin.isLt _
  · intro i _; rw [hr, hc.2.2.2.2]; exact Fin.isLt _
  · intro i; exact (hl i).trans (hc.2.2.2.1 i)
  · intro i; exact (hr i).trans (hc.2.2.2.2 i)

private theorem zero_list_entry (n i : ℕ) :
    FiniteSequenceCoding.entry (FiniteSequenceCoding.code (List.replicate n 0)) i = 0 := by
  by_cases hi : i < n <;> simp [FiniteSequenceCoding.entry_code, hi]

theorem padding_code_values :
    pack 0 1 0 0 = 4 ∧
    pack 0 1 (FiniteSequenceCoding.code [0]) (FiniteSequenceCoding.code [0, 0]) = 676 ∧
    (4 : ℕ) ≠ 676 := by
  norm_num [pack, FiniteSequenceCoding.code, Encodable.encode_list_cons, Nat.pair]

theorem padding_same_configuration {Γ Q : Type*} {A : TuringMachines.Alphabet Γ}
    [Fintype Γ] [Fintype Q] {T : TuringMachines.Machine A Q} (L : Labeling T) :
    Represents L (TuringMachines.input A T 1) 4 ∧
    Represents L (TuringMachines.input A T 1) 676 := by
  have h4 : Represents L (TuringMachines.input A T 1) 4 := by
    simpa only [initialCode, marks, padding_code_values.1] using input_represents L 1
  refine ⟨h4, represents_same_observations L _ 4 676 h4 (by norm_num [stateCode, Nat.unpair]) (by norm_num [currentCode, Nat.unpair]) ?_ ?_⟩
  · intro i
    have hl : leftCode 676 = FiniteSequenceCoding.code [0] := by norm_num [leftCode, Nat.unpair, FiniteSequenceCoding.code, Encodable.encode_list_cons, Nat.pair]
    rw [hl]
    have hz : leftCode 4 = 0 := by norm_num [leftCode, Nat.unpair]
    rw [hz]
    simpa only [FiniteSequenceCoding.entry, FiniteSequenceCoding.decode_zero, List.getElem?_nil, Option.getD_none, List.replicate_succ, List.replicate_zero] using zero_list_entry 1 i
  · intro i
    have hr : rightCode 676 = FiniteSequenceCoding.code [0, 0] := by norm_num [rightCode, Nat.unpair, FiniteSequenceCoding.code, Encodable.encode_list_cons, Nat.pair]
    rw [hr]
    have hz : rightCode 4 = 0 := by norm_num [rightCode, Nat.unpair]
    rw [hz]
    simpa only [FiniteSequenceCoding.entry, FiniteSequenceCoding.decode_zero, List.getElem?_nil, Option.getD_none, List.replicate_succ, List.replicate_zero] using zero_list_entry 2 i

theorem readout_gap (g s q l : ℕ)
    (hc : Valid g s (pack q 1 l (FiniteSequenceCoding.code [1, 0, 1]))) :
    readoutCode g s (pack q 1 l (FiniteSequenceCoding.code [1, 0, 1])) = 2 ∧
    readoutBound (pack q 1 l (FiniteSequenceCoding.code [1, 0, 1])) = 4 ∧
    (FiniteSequenceCoding.decode
      (FiniteSequenceCoding.cons 1 (FiniteSequenceCoding.code [1, 0, 1]))).count 1 = 3 := by
  have ht := (validTest_spec g s _).mpr hc
  have hfield := pack_fields q 1 l (FiniteSequenceCoding.code [1, 0, 1])
  have hb : readoutBound (pack q 1 l (FiniteSequenceCoding.code [1, 0, 1])) = 4 := by
    rw [readoutBound, hfield.2.1, hfield.2.2.2, ← FiniteSequenceCoding.code_cons]
    simp only [FiniteSequenceCoding.length, FiniteSequenceCoding.decode_code]
    rfl
  have hr : rawReadout (pack q 1 l (FiniteSequenceCoding.code [1, 0, 1])) = 2 := by
    rw [rawReadout, hb, hfield.2.1, hfield.2.2.2, ← FiniteSequenceCoding.code_cons]
    apply (PrimitiveRecursion.boundedSearch_eq_iff _ _ 4 2 (by decide)).mpr
    constructor
    · rw [FiniteSequenceCoding.entry_code]
      decide
    · intro j hj
      interval_cases j <;> (rw [FiniteSequenceCoding.entry_code]; decide)
  refine ⟨?_, hb, ?_⟩
  · unfold readoutCode
    rw [ht]
    exact hr
  · rw [← FiniteSequenceCoding.code_cons, FiniteSequenceCoding.decode_code]
    rfl

theorem zero_tuple_values :
    pack 0 0 0 0 = 0 ∧
    pack 1 0 0 (FiniteSequenceCoding.cons 1 0) = 6562 ∧
    pack 2 1 (FiniteSequenceCoding.cons 0 0) 0 = 27 := by
  norm_num [pack, FiniteSequenceCoding.cons, Nat.pair]

private theorem successor_lookup_scan :
    lookup successorLabels 0 0 = 1 + Nat.pair 1 (Nat.pair 1 (moveCode .left)) := by
  exact lookup_actual successorLabels SuccessorState.scan false

private theorem successor_lookup_back :
    lookup successorLabels 1 0 = 1 + Nat.pair 2 (Nat.pair 0 (moveCode .right)) := by
  exact lookup_actual successorLabels SuccessorState.back false

private theorem successor_lookup_halt : lookup successorLabels 2 1 = 0 := by
  exact lookup_actual successorLabels SuccessorState.halt true

private theorem successor_transitions :
    transition successorLabels 0 = 6562 ∧ transition successorLabels 6562 = 27 := by
  have v0 : Valid (Fintype.card Bool) (Fintype.card SuccessorState) 0 :=
    valid_zero _ _ (by decide) (by decide)
  have h0 := transition_rows successorLabels 0 1 1 .left v0 (by
    convert successor_lookup_scan using 1
    norm_num [stateCode, currentCode, Nat.unpair])
  norm_num [FiniteSequenceCoding.head, FiniteSequenceCoding.tail,
    FiniteSequenceCoding.cons, leftCode, rightCode, pack, Nat.pair, Nat.unpair] at h0
  have v1 := transition_valid successorLabels 0 v0
  rw [h0] at v1
  have h1 := transition_rows successorLabels 6562 2 0 .right v1 (by
    convert successor_lookup_back using 1
    norm_num [stateCode, currentCode, Nat.unpair])
  norm_num [FiniteSequenceCoding.head, FiniteSequenceCoding.tail,
    FiniteSequenceCoding.cons, leftCode, rightCode, pack, Nat.pair, Nat.unpair] at h1
  exact ⟨h0, h1⟩

theorem successor_zero_codes :
    numericalRun successorLabels 0 0 = 0 ∧
    numericalRun successorLabels 0 1 = 6562 ∧
    numericalRun successorLabels 0 2 = 27 ∧
    haltCode successorLabels 0 = 0 ∧ haltCode successorLabels 6562 = 0 ∧
    haltCode successorLabels 27 = 1 ∧ readoutCode 2 3 27 = 1 := by
  have h0 : numericalRun successorLabels 0 0 = 0 := rfl
  have h1 : numericalRun successorLabels 0 1 = 6562 := by
    exact successor_transitions.1
  have h2 : numericalRun successorLabels 0 2 = 27 := by
    change transition successorLabels (numericalRun successorLabels 0 1) = 27
    rw [h1]
    exact successor_transitions.2
  have v0 : Valid (Fintype.card Bool) (Fintype.card SuccessorState) 0 := by
    simpa only [numericalRun, initialCode, zero_tuple_values.1] using numericalRun_valid successorLabels 0 0
  have v1 := numericalRun_valid successorLabels 0 1
  have v2 := numericalRun_valid successorLabels 0 2
  rw [h1] at v1
  rw [h2] at v2
  have halt0 : haltCode successorLabels 0 = 0 := by
    apply (haltCode_spec _ _).2.mpr
    simp only [haltTest, (validTest_spec _ _ _).mpr v0, Bool.not_true, Bool.false_or]
    norm_num [stateCode, currentCode, Nat.unpair]
    rw [successor_lookup_scan]
    decide
  have halt1 : haltCode successorLabels 6562 = 0 := by
    apply (haltCode_spec _ _).2.mpr
    simp only [haltTest, (validTest_spec _ _ _).mpr v1, Bool.not_true, Bool.false_or]
    norm_num [stateCode, currentCode, Nat.unpair]

    rw [successor_lookup_back]
    decide
  have halt2 : haltCode successorLabels 27 = 1 := by
    apply (haltCode_spec _ _).1.mpr
    simp only [haltTest, (validTest_spec _ _ _).mpr v2, Bool.not_true, Bool.false_or]
    norm_num [stateCode, currentCode, Nat.unpair]

    rw [successor_lookup_halt]

  have read2 : readoutCode 2 3 27 = 1 := by
    have ht : validTest 2 3 27 = true := by
      apply (validTest_spec _ _ _).mpr
      exact v2
    have hcur : currentCode 27 = 1 := by norm_num [currentCode, Nat.unpair]
    have hright : rightCode 27 = 0 := by norm_num [rightCode, Nat.unpair]
    have hcons : FiniteSequenceCoding.cons 1 0 = FiniteSequenceCoding.code [1] :=
      (FiniteSequenceCoding.code_cons 1 []).symm
    have hb : readoutBound 27 = 1 := by
      rw [readoutBound, hcur, hright, hcons]
      simp only [FiniteSequenceCoding.length, FiniteSequenceCoding.decode_code]
      rfl
    have hr : rawReadout 27 = 1 := by
      rw [rawReadout, hb, hcur, hright, hcons]
      apply (PrimitiveRecursion.boundedSearch_spec _ (FiniteSequenceCoding.code [1]) 1).2.2.mpr
      intro i hi
      have he : i = 0 := by omega
      subst i
      rw [FiniteSequenceCoding.entry_code]
      decide
    unfold readoutCode
    rw [ht]
    exact hr
  exact ⟨h0, h1, h2, halt0, halt1, halt2, read2⟩

theorem successor_zero_history :
    History successorLabels 0 (FiniteSequenceCoding.code [0, 6562, 27]) ∧
    Certificate successorLabels 0 (Nat.pair 1 (FiniteSequenceCoding.code [0, 6562, 27])) ∧
    ¬ History successorLabels 0 0 := by
  have hh := first_halt_history successorLabels 0 2
    (by simpa using Lemmatheca.Entry.TuringMachines.successor_first_halt 0)
  have hp : prefixCode successorLabels 0 2 = FiniteSequenceCoding.code [0, 6562, 27] := by
    rw [(prefixCode_correct successorLabels 0 2).1]
    norm_num [List.range_succ, successor_zero_codes.1, successor_zero_codes.2.1,
      successor_zero_codes.2.2.1]
  rw [hp] at hh
  refine ⟨hh, ⟨?_, ?_⟩, history_empty _ _⟩
  · simpa using hh
  · simp only [Nat.unpair_pair, FiniteSequenceCoding.length, FiniteSequenceCoding.decode_code,
      List.length_cons, List.length_nil, FiniteSequenceCoding.entry_code]
    have hQ : Fintype.card SuccessorState = 3 := by decide
    simpa [hQ] using successor_zero_codes.2.2.2.2.2.2.symm

theorem successor_final_padding :
    Represents successorLabels
      (TuringMachines.run successor (TuringMachines.input binary successor 0) 2) 27 ∧
    Represents successorLabels
      (TuringMachines.run successor (TuringMachines.input binary successor 0) 2) 8 ∧
    leftCode 27 = FiniteSequenceCoding.code [0] ∧ leftCode 8 = FiniteSequenceCoding.code [] ∧
    (8 : ℕ) < 27 := by
  have h27 := run_simulation successorLabels 0 2
  rw [successor_zero_codes.2.2.1] at h27
  refine ⟨h27, represents_same_observations successorLabels _ 27 8 h27 (by norm_num [stateCode, Nat.unpair]) (by norm_num [currentCode, Nat.unpair]) ?_ ?_,
    by norm_num [leftCode, Nat.unpair, FiniteSequenceCoding.code, Encodable.encode_list_cons, Nat.pair], by norm_num [leftCode, Nat.unpair], by decide⟩
  · intro i
    have hl : leftCode 27 = FiniteSequenceCoding.code [0] := by norm_num [leftCode, Nat.unpair, FiniteSequenceCoding.code, Encodable.encode_list_cons, Nat.pair]
    rw [hl]
    have hz : leftCode 8 = 0 := by norm_num [leftCode, Nat.unpair]
    rw [hz]
    simpa only [FiniteSequenceCoding.entry, FiniteSequenceCoding.decode_zero, List.getElem?_nil, Option.getD_none, List.replicate_succ, List.replicate_zero] using (zero_list_entry 1 i).symm
  · intro i
    norm_num [rightCode, Nat.unpair]

end Lemmatheca.Entry.CodingTuringComputations
