import Lemmatheca.BoundedChangesAndStrongReductions.Tables
import Lemmatheca.LimitComputability.BoundedGuesses

/-! A fixed use window and a growing allowance in the existing finite evaluator. -/
namespace Lemmatheca.ComputabilityTheory.BoundedChangesStrongReductions

open UniversalComputation LimitComputability DifferenceEnumerable ComputablyBoundedChanges
open StrongReductions PostsTheorem

noncomputable section

set_option backward.isDefEq.respectTransparency false

def snapshotOracle (u : ℕ → ℕ) (s x : ℕ) : Set ℕ := haltingStage s ∩ Set.Iio (u x)

def snapshotWord (u : ℕ → ℕ) (s x : ℕ) : ℕ :=
  FiniteSequenceCoding.code ((List.range (u x)).map (haltingTest s))

def snapshotGuess (e : ℕ) (u : ℕ → ℕ) (s x : ℕ) : ℕ :=
  if finiteValue (snapshotWord u s x) s e x = 2 then 1 else 0

def discoveryCount (u : ℕ → ℕ) (s x : ℕ) : ℕ :=
  (Finset.range (u x)).sum (haltingTest s)

def revisionBudget (u : ℕ → ℕ) (x : ℕ) : ℕ := 2 * u x + 1

private theorem halting_test_zero (q : ℕ) : haltingTest 0 q = 0 := by
  rcases halting_stage_data.2.1 0 q with h | h
  · exact h
  · have hq := (EffectiveEnumerations.canonical_test_data haltingIndex).2.2.1 0 q h
    omega

private theorem halting_test_mono (r s q : ℕ) (hrs : r ≤ s) :
    haltingTest r q ≤ haltingTest s q := by
  rcases halting_stage_data.2.1 r q with hz | ho
  · rw [hz]
    exact Nat.zero_le _
  · have hmem := halting_stage_data.2.2.2.1 hrs
      ((halting_stage_data.2.2.1 r q).mp ho)
    rw [ho, (halting_stage_data.2.2.1 s q).mpr hmem]

private theorem discovery_zero (u : ℕ → ℕ) (x : ℕ) : discoveryCount u 0 x = 0 := by
  simp [discoveryCount, halting_test_zero]

private theorem discovery_mono (u : ℕ → ℕ) (x : ℕ) :
    Monotone (fun s => discoveryCount u s x) := by
  intro r s hrs
  exact Finset.sum_le_sum (fun q _ => halting_test_mono r s q hrs)

private theorem discovery_bound (u : ℕ → ℕ) (s x : ℕ) :
    discoveryCount u s x ≤ u x := by
  calc
    _ ≤ (Finset.range (u x)).sum (fun _ => 1) := by
      apply Finset.sum_le_sum
      intro q _
      rcases halting_stage_data.2.1 s q with h | h <;> simp [h]
    _ = u x := by simp

private theorem snapshot_binary (e : ℕ) (u : ℕ → ℕ) : Binary (snapshotGuess e u) := by
  intro s x
  unfold snapshotGuess
  split <;> simp

theorem snapshot_word_data (u : ℕ → ℕ) (s x : ℕ) :
    snapshotWord u s x = prefixCode (haltingStage s) (u x) ∧
      FiniteSequenceCoding.length (snapshotWord u s x) = u x ∧
      finiteOracle (snapshotWord u s x) = snapshotOracle u s x := by
  have hw : snapshotWord u s x = prefixCode (haltingStage s) (u x) := rfl
  refine ⟨hw, ?_, ?_⟩
  · rw [hw]
    exact (prefixCode_spec _ _).1
  · ext q
    change beta (snapshotWord u s x) q = 1 ↔ q ∈ haltingStage s ∧ q < u x
    by_cases hq : q < u x
    · rw [hw, (prefixCode_spec _ _).2 q hq]
      simp [indicator, hq]
    · have hlen : FiniteSequenceCoding.length (snapshotWord u s x) ≤ q := by
        rw [hw, (prefixCode_spec _ _).1]
        omega
      have hz := FiniteSequenceCoding.entry_out_of_range (snapshotWord u s x) q hlen
      simp [beta, hz, hq]

theorem snapshot_guess_data (e : ℕ) (u : ℕ → ℕ) (hu : Computable u) :
    Computable₂ (snapshotGuess e u) ∧ Binary (snapshotGuess e u) ∧
      StartsZero (snapshotGuess e u) := by
  have hterm : Computable₂ (fun p : ℕ × ℕ => fun q => haltingTest p.1 q) :=
    (halting_stage_data.1.to_comp.comp (Computable.fst.comp Computable.fst)
      Computable.snd).to₂
  have hlist : Computable (fun p : ℕ × ℕ =>
      (List.range (u p.2)).map (haltingTest p.1)) :=
    computable_list_map (Primrec.list_range.to_comp.comp (hu.comp Computable.snd)) hterm
  have hw : Computable (fun p : ℕ × ℕ => snapshotWord u p.1 p.2) :=
    Primrec.encode.to_comp.comp hlist
  have hp : Computable (fun p : ℕ × ℕ => pack4 (snapshotWord u p.1 p.2) p.1 e p.2) :=
    Primrec₂.natPair.to_comp.comp hw
      (Primrec₂.natPair.to_comp.comp Computable.fst
        (Primrec₂.natPair.to_comp.comp (Computable.const e) Computable.snd))
  have hv : Computable (fun p : ℕ × ℕ =>
      finiteValue (snapshotWord u p.1 p.2) p.1 e p.2) :=
    (finiteValue_primitive.to_comp.comp hp).of_eq
      (fun p => by simp only [finiteValueInput, pack4, Nat.unpair_pair])
  have hd : Computable₂ (snapshotGuess e u) :=
    (Computable.cond (Primrec.eq.decide.to_comp.comp hv (Computable.const 2))
      (Computable.const 1) (Computable.const 0)).of_eq
        (fun p => by simp only [Bool.cond_decide]; rfl)
  refine ⟨hd, snapshot_binary e u, ?_⟩
  intro x
  unfold snapshotGuess
  rw [finiteValue_outside _ 0 e x (Nat.zero_le x)]
  decide

theorem discovery_count_data (u : ℕ → ℕ) (hu : Computable u) :
    Computable₂ (discoveryCount u) ∧ (∀ x, discoveryCount u 0 x = 0) ∧
      (∀ x, Monotone (fun s => discoveryCount u s x)) ∧
      ∀ s x, discoveryCount u s x ≤ u x := by
  have hterm : Computable₂ (fun p : ℕ × ℕ => fun q => haltingTest p.1 q) :=
    (halting_stage_data.1.to_comp.comp (Computable.fst.comp Computable.fst)
      Computable.snd).to₂
  exact ⟨range_sum_computable (fun p : ℕ × ℕ => u p.2)
    (hu.comp Computable.snd) _ hterm, discovery_zero u, discovery_mono u,
    discovery_bound u⟩

theorem equal_discoveries (u : ℕ → ℕ) (s x : ℕ)
    (h : discoveryCount u (s + 1) x = discoveryCount u s x) :
    snapshotWord u (s + 1) x = snapshotWord u s x ∧
      snapshotOracle u (s + 1) x = snapshotOracle u s x := by
  have hbits : ∀ q < u x, haltingTest (s + 1) q = haltingTest s q := by
    have hall := (Finset.sum_eq_sum_iff_of_le (s := Finset.range (u x))
      (fun q _ => halting_test_mono s (s + 1) q (Nat.le_succ s))).mp h.symm
    intro q hq
    exact (hall q (Finset.mem_range.mpr hq)).symm
  have hw : snapshotWord u (s + 1) x = snapshotWord u s x := by
    apply congrArg FiniteSequenceCoding.code
    apply List.map_congr_left
    intro q hq
    exact hbits q (List.mem_range.mp hq)
  refine ⟨hw, ?_⟩
  exact (snapshot_word_data u (s + 1) x).2.2.symm.trans
    ((congrArg finiteOracle hw).trans (snapshot_word_data u s x).2.2)

theorem snapshot_persistence (e : ℕ) (u : ℕ → ℕ) (s x : ℕ)
    (h : discoveryCount u (s + 1) x = discoveryCount u s x) :
    snapshotGuess e u s x ≤ snapshotGuess e u (s + 1) x := by
  by_cases hs : finiteValue (snapshotWord u s x) s e x = 2
  · have hm : OracleProgramNumberings.bounded (finiteOracle (snapshotWord u s x))
        s (OracleProgramNumberings.decodeCode e) x = some 1 :=
      (OracleProgramNumberings.boundedValue_output _ s e x 1).mp
        ((finiteValue_identity _ s e x).symm.trans hs)
    have hn := OracleProgramNumberings.bounded_monotone
      (indicator (finiteOracle (snapshotWord u s x))) s 1
      (OracleProgramNumberings.decodeCode e) x 1 hm
    have hv : finiteValue (snapshotWord u (s + 1) x) (s + 1) e x = 2 := by
      rw [(equal_discoveries u s x h).1, finiteValue_identity]
      exact (OracleProgramNumberings.boundedValue_output _ (s + 1) e x 1).mpr hn
    simp [snapshotGuess, hs, hv]
  · simp [snapshotGuess, hs]

theorem revision_ledger (e : ℕ) (u : ℕ → ℕ) (s x : ℕ) :
    changeCount (snapshotGuess e u) s x ≤
      2 * discoveryCount u s x + snapshotGuess e u s x := by
  induction s with
  | zero => simp [changeCount, discovery_zero]
  | succ s ih =>
    have he : discoveryCount u s x ≤ discoveryCount u (s + 1) x :=
      discovery_mono u x (Nat.le_succ s)
    have hds : snapshotGuess e u s x ≤ 1 := by
      rcases snapshot_binary e u s x with h | h <;> omega
    have hdn : snapshotGuess e u (s + 1) x ≤ 1 := by
      rcases snapshot_binary e u (s + 1) x with h | h <;> omega
    by_cases heq : discoveryCount u (s + 1) x = discoveryCount u s x
    · have hd := snapshot_persistence e u s x heq
      rw [changeCount]
      split_ifs <;> omega
    · rw [changeCount]
      split_ifs <;> omega

theorem snapshot_revision_budget (e : ℕ) (u : ℕ → ℕ) (hu : Computable u) :
    ComputableBound (snapshotGuess e u) (revisionBudget u) := by
  have hc : Computable (revisionBudget u) :=
    Primrec.nat_add.to_comp.comp
      (Primrec.nat_mul.to_comp.comp (Computable.const 2) hu) (Computable.const 1)
  refine ⟨hc, fun s x => ?_⟩
  have hl := revision_ledger e u s x
  have he := discovery_bound u s x
  have hd : snapshotGuess e u s x ≤ 1 := by
    rcases snapshot_binary e u s x with h | h <;> omega
  change changeCount (snapshotGuess e u) s x ≤ 2 * u x + 1
  omega

theorem snapshot_converges (c : OracleComputation.Code) (u : ℕ → ℕ) (A : Set ℕ)
    (h : BoundedReduction c u A haltingDiagonal) :
    Converges (snapshotGuess (OracleProgramNumberings.encodeCode c) u) A := by
  classical
  intro x
  let C : Set ℕ := haltingDiagonal ∩ Set.Iio (u x)
  have hr : OracleComputation.eval C c x = Part.some (indicator A x) :=
    bounded_replay h x (fun q hq => by
      have hh : q ∈ C ↔ q ∈ haltingDiagonal := by
        simp only [C, Set.mem_inter_iff, Set.mem_Iio, hq, and_true]
      simp only [indicator, hh])
  obtain ⟨k, hk⟩ := (OracleProgramNumberings.bounded_complete C c x (indicator A x)).mp
    (Part.eq_some_iff.mp hr)
  obtain ⟨N, hN⟩ := halting_prefix_agreement (u x)
  have heq (s : ℕ) (hs : N ≤ s) : snapshotOracle u s x = C := by
    ext q
    change (haltingStage s q ∧ q < u x) ↔ (haltingDiagonal q ∧ q < u x)
    by_cases hq : q < u x
    · simp only [hq, and_true]
      have hh := hN s hs q hq
      change (if haltingStage s q then 1 else 0) =
        (if haltingDiagonal q then 1 else 0) at hh
      by_cases hqS : haltingStage s q <;> by_cases hqK : haltingDiagonal q <;> simp_all
    · simp only [hq, and_false]
  refine ⟨max N k, fun s hs => ?_⟩
  have hks : k ≤ s := by omega
  have hm : OracleProgramNumberings.bounded C s c x = some (indicator A x) := by
    have hv := OracleProgramNumberings.bounded_monotone
      (indicator (fun n => n ∈ C)) k (s - k) c x (indicator A x) hk
    simpa only [OracleProgramNumberings.bounded, Nat.add_sub_of_le hks] using hv
  have hv : finiteValue (snapshotWord u s x) s
      (OracleProgramNumberings.encodeCode c) x = indicator A x + 1 := by
    rw [finiteValue_identity, (snapshot_word_data u s x).2.2, heq s (by omega)]
    apply (OracleProgramNumberings.boundedValue_output C s
      (OracleProgramNumberings.encodeCode c) x (indicator A x)).mpr
    simpa only [OracleProgramNumberings.decode_encode] using hm
  change snapshotGuess (OracleProgramNumberings.encodeCode c) u s x = indicator A x
  rcases (show indicator A x = 0 ∨ indicator A x = 1 from indicator_bits A x) with hz | ho
  · simp [snapshotGuess, hv, hz]
  · simp [snapshotGuess, hv, ho]

theorem bounded_reduction_presentation (c : OracleComputation.Code) (u : ℕ → ℕ) (A : Set ℕ)
    (h : BoundedReduction c u A haltingDiagonal) :
    Computable₂ (snapshotGuess (OracleProgramNumberings.encodeCode c) u) ∧
      Binary (snapshotGuess (OracleProgramNumberings.encodeCode c) u) ∧
      StartsZero (snapshotGuess (OracleProgramNumberings.encodeCode c) u) ∧
      Converges (snapshotGuess (OracleProgramNumberings.encodeCode c) u) A ∧
      ComputableBound (snapshotGuess (OracleProgramNumberings.encodeCode c) u) (revisionBudget u) := by
  obtain ⟨hc, hb, hz⟩ := snapshot_guess_data (OracleProgramNumberings.encodeCode c) u h.1
  exact ⟨hc, hb, hz, snapshot_converges c u A h,
    snapshot_revision_budget (OracleProgramNumberings.encodeCode c) u h.1⟩

end
end Lemmatheca.ComputabilityTheory.BoundedChangesStrongReductions
