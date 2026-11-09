import Lemmatheca.LimitComputability.LimitLemma

/-! Delayed answers, drifting cutoffs, and a decidable limit without a computable modulus. -/
namespace Lemmatheca.Entry.LimitComputability

open Lemmatheca.ComputabilityTheory
open ComputabilityTheory.LimitComputability UniversalComputation

noncomputable section

private theorem indicator_univ_value (x : ℕ) : indicator (Set.univ : Set ℕ) x = 1 := by
  classical
  simp only [indicator, Set.univ, Set.ofPred]
  simp

private theorem indicator_empty_value (x : ℕ) : indicator (∅ : Set ℕ) x = 0 := by
  classical
  simp only [indicator, EmptyCollection.emptyCollection]
  simp

def delayedApproximation (N s _x : ℕ) : ℕ := if s ≤ N then 0 else 1

theorem delayed_approximation_spec (N : ℕ) :
    Computable₂ (delayedApproximation N) ∧ Binary (delayedApproximation N) ∧
      Converges (delayedApproximation N) Set.univ ∧
      (∀ s ≤ N, ∀ x, delayedApproximation N s x = 0) ∧
      (∀ x, delayedApproximation N (N + 1) x = 1) := by
  classical
  have hp : Primrec₂ (delayedApproximation N) :=
    Primrec.ite (Primrec.nat_le.comp Primrec.fst (Primrec.const N))
      (Primrec.const 0) (Primrec.const 1)
  refine ⟨hp.to_comp, ?_, ?_, ?_, ?_⟩
  · intro s x
    unfold delayedApproximation
    split <;> simp
  · intro x
    refine ⟨N + 1, fun s hs => ?_⟩
    have hn : ¬s ≤ N := by omega
    simp [delayedApproximation, hn, indicator_univ_value]
  · intro s hs x
    simp [delayedApproximation, hs]
  · intro x
    simp [delayedApproximation]

def driftingCutoff (s x : ℕ) : ℕ := if x < s then 1 else 0

theorem drifting_cutoff_spec :
    Computable₂ driftingCutoff ∧ Binary driftingCutoff ∧ Converges driftingCutoff Set.univ ∧
      (∀ s, driftingCutoff s s = 0 ∧ indicator Set.univ s = 1) ∧
    ∀ s, ∃ x, driftingCutoff s x ≠ indicator Set.univ x := by
  classical
  have hp : Primrec₂ driftingCutoff :=
    Primrec.ite (Primrec.nat_lt.comp Primrec.snd Primrec.fst)
      (Primrec.const 1) (Primrec.const 0)
  refine ⟨hp.to_comp, ?_, ?_, ?_, ?_⟩
  · intro s x
    unfold driftingCutoff
    split <;> simp
  · intro x
    refine ⟨x + 1, fun s hs => ?_⟩
    have hxs : x < s := by omega
    simp [driftingCutoff, hxs, indicator_univ_value]
  · intro s
    simp [driftingCutoff, indicator_univ_value]
  · intro s
    exact ⟨s, by simp [driftingCutoff, indicator_univ_value]⟩

theorem halting_examples :
    LimitComputable haltingDiagonal ∧ LimitComputable haltingDiagonalᶜ ∧
      ¬ ComputablePred haltingDiagonal ∧ ¬ ComputablePred haltingDiagonalᶜ ∧
      ¬ REPred haltingDiagonalᶜ := by
  refine ⟨enumerable_limit haltingDiagonal haltingDiagonal_enumerable,
    coenumerable_limit haltingDiagonalᶜ (by
      simpa only [Compl.compl, Set.ofPred, Membership.mem, Set.Mem, not_not] using haltingDiagonal_enumerable),
    haltingDiagonal_undecidable, ?_, haltingDiagonal_complement_not_enumerable⟩
  intro hc
  apply haltingDiagonal_undecidable
  simpa only [Compl.compl, Set.ofPred, Membership.mem, Set.Mem, not_not] using hc.not

theorem halting_no_computable_modulus (a : Approximation) (ha : Computable₂ a) :
    ¬ ∃ m, Computable m ∧ ConvergenceModulus a haltingDiagonal m := by
  rintro ⟨m, hm, hs⟩
  exact haltingDiagonal_undecidable (computable_modulus_decides a haltingDiagonal m ha hm hs)

def haltingPulse (s x : ℕ) : ℕ :=
  if haltingTest (s + 1) x = 1 ∧ haltingTest s x = 0 then 1 else 0

theorem halting_pulse_primitive : Primrec₂ haltingPulse := by
  have hn : Primrec (fun p : ℕ × ℕ => haltingTest (p.1 + 1) p.2) :=
    halting_stage_data.1.comp (Primrec.succ.comp Primrec.fst) Primrec.snd
  exact Primrec.ite ((Primrec.eq.comp hn (Primrec.const 1)).and
    (Primrec.eq.comp halting_stage_data.1 (Primrec.const 0)))
      (Primrec.const 1) (Primrec.const 0)

theorem halting_pulse_at_most_once (x s t : ℕ)
    (hs : haltingPulse s x = 1) (ht : haltingPulse t x = 1) : s = t := by
  have hs' : haltingTest (s + 1) x = 1 ∧ haltingTest s x = 0 := by
    unfold haltingPulse at hs
    split at hs
    · assumption
    · contradiction
  have ht' : haltingTest (t + 1) x = 1 ∧ haltingTest t x = 0 := by
    unfold haltingPulse at ht
    split at ht
    · assumption
    · contradiction
  obtain ⟨_, _, hmem, hmono, _, _, _⟩ := halting_stage_data
  have hst : ¬s < t := by
    intro hlt
    have hi := hmono (show s + 1 ≤ t by omega) ((hmem (s + 1) x).mp hs'.1)
    have hv := (hmem t x).mpr hi
    omega
  have hts : ¬t < s := by
    intro hlt
    have hi := hmono (show t + 1 ≤ s by omega) ((hmem (t + 1) x).mp ht'.1)
    have hv := (hmem s x).mpr hi
    omega
  omega

theorem halting_pulse_converges : Binary haltingPulse ∧ Converges haltingPulse ∅ := by
  classical
  refine ⟨?_, ?_⟩
  · intro s x
    unfold haltingPulse
    split <;> simp
  · intro x
    obtain ⟨t, ht⟩ := halting_stage_converges x
    refine ⟨t, fun s hs => ?_⟩
    have hnext := ht (s + 1) (by omega)
    have hnow := ht s hs
    have hz : haltingPulse s x = 0 := by
      unfold haltingPulse
      rw [hnext, hnow]
      by_cases hx : haltingDiagonal x <;> simp [indicator, hx]
    exact hz.trans (indicator_empty_value x).symm

theorem pulse_modulus_membership (m : ℕ → ℕ)
    (hm : ConvergenceModulus haltingPulse ∅ m) (x : ℕ) :
    x ∈ haltingDiagonal ↔ haltingTest (m x) x = 1 := by
  classical
  obtain ⟨_, hb, hmem, hmono, hcover, _, _⟩ := halting_stage_data
  constructor
  · intro hK
    by_contra hn
    have hbase := (hb (m x) x).resolve_right hn
    have hzero : ∀ s, m x ≤ s → haltingTest s x = 0 := by
      intro s hs
      induction s, hs using Nat.le_induction with
      | base => exact hbase
      | succ s hs ih =>
          rcases hb (s + 1) x with hz | hp
          · exact hz
          · have hpulse : haltingPulse s x = 1 := by simp [haltingPulse, hp, ih]
            have hmzero : haltingPulse s x = 0 := (hm x s hs).trans (indicator_empty_value x)
            omega
    obtain ⟨t, ht⟩ := (hcover x).mp hK
    have hi := hmono (Nat.le_max_left t (m x)) ht
    have hv := (hmem (max t (m x)) x).mpr hi
    have hz := hzero (max t (m x)) (Nat.le_max_right _ _)
    omega
  · intro hp
    exact (hcover x).mpr ⟨m x, (hmem (m x) x).mp hp⟩

theorem pulse_no_computable_modulus :
    ¬ ∃ m, Computable m ∧ ConvergenceModulus haltingPulse ∅ m := by
  classical
  rintro ⟨m, hc, hm⟩
  have htest : Computable (fun x => haltingTest (m x) x) :=
    halting_stage_data.1.to_comp.comp hc Computable.id
  have he (x : ℕ) : haltingTest (m x) x = indicator haltingDiagonal x := by
    have hiff := pulse_modulus_membership m hm x
    by_cases hx : x ∈ haltingDiagonal
    · have hv := hiff.mp hx
      change _ = if x ∈ haltingDiagonal then 1 else 0
      simpa only [ite_eq_left hx] using hv
    · have hn : haltingTest (m x) x ≠ 1 := fun h => hx (hiff.mpr h)
      have hz := (halting_stage_data.2.1 (m x) x).resolve_right hn
      change _ = if x ∈ haltingDiagonal then 1 else 0
      simpa only [ite_eq_right hx] using hz
  exact haltingDiagonal_undecidable
    ((decidable_iff_characteristic haltingDiagonal).mpr ⟨_, htest, he⟩)

end
end Lemmatheca.Entry.LimitComputability
