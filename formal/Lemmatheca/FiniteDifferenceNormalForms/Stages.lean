import Lemmatheca.FiniteDifferenceNormalForms.Thresholds

/-! The supplied finite list of increasing stage bits gives a bounded rank. -/
namespace Lemmatheca.ComputabilityTheory.FiniteDifferenceNormalForms

open UniversalComputation LimitComputability DifferenceEnumerable FiniteMindChanges

set_option backward.isDefEq.respectTransparency false

noncomputable def stageRank (e : ℕ → ℕ) : ℕ → Approximation
  | 0 => fun _ _ => 0
  | n + 1 => fun s x => stageRank e n s x + EffectiveEnumerations.stageTest (e n) s x

def parityGuess (R : Approximation) (s x : ℕ) : ℕ := R s x % 2

noncomputable def chainGuess (n : ℕ) (e : ℕ → ℕ) : Approximation :=
  parityGuess (stageRank e n)

theorem stage_rank_data (n : ℕ) (e : ℕ → ℕ) :
    Computable₂ (stageRank e n) ∧ StartsZero (stageRank e n) ∧
      (∀ s x, stageRank e n s x ≤ n) ∧
      ∀ s x, stageRank e n s x ≤ stageRank e n (s + 1) x := by
  induction n with
  | zero =>
      exact ⟨Computable.const 0, fun _ => rfl, fun _ _ => le_rfl, fun _ _ => le_rfl⟩
  | succ n ih =>
      obtain ⟨htc, htb, hbound, hinc, _⟩ := EffectiveEnumerations.canonical_test_data (e n)
      refine ⟨Primrec.nat_add.to_comp.comp ih.1 htc, ?_, ?_, ?_⟩
      · intro x
        have hz : EffectiveEnumerations.stageTest (e n) 0 x = 0 := by
          rcases htb 0 x with h | h
          · exact h
          · have := hbound 0 x h
            omega
        simp only [stageRank, ih.2.1 x, hz, Nat.zero_add]
      · intro s x
        have hb := ih.2.2.1 s x
        rcases htb s x with h | h <;> simp only [stageRank, h] <;> omega
      · intro s x
        have hm := ih.2.2.2 s x
        have hb : EffectiveEnumerations.stageTest (e n) s x ≤
            EffectiveEnumerations.stageTest (e n) (s + 1) x := by
          rcases htb s x with h | h
          · omega
          · rw [h, hinc s x h]
        simp only [stageRank]
        omega

theorem parity_rank_data (R : Approximation) (n : ℕ) (hc : Computable₂ R)
    (hz : StartsZero R) (hm : ∀ s x, R s x ≤ R (s + 1) x)
    (hn : ∀ s x, R s x ≤ n) :
    Computable₂ (parityGuess R) ∧ Binary (parityGuess R) ∧ StartsZero (parityGuess R) ∧
      (∀ s x, changeCount (parityGuess R) s x ≤ R s x) ∧ AtMostChanges (parityGuess R) n := by
  have hcomp : Computable₂ (parityGuess R) :=
    Primrec.nat_mod.to_comp.comp hc (Computable.const 2)
  have hbinary : Binary (parityGuess R) := by
    intro s x
    have h := Nat.mod_lt (R s x) (by omega : 0 < 2)
    change R s x % 2 = 0 ∨ R s x % 2 = 1
    omega
  have hzero : StartsZero (parityGuess R) := by
    intro x
    simp only [parityGuess, hz x, Nat.zero_mod]
  have hcount : ∀ s x, changeCount (parityGuess R) s x ≤ R s x := by
    intro s x
    induction s with
    | zero => simp only [changeCount]; omega
    | succ s ih =>
        have hm' := hm s x
        rw [changeCount]
        by_cases he : parityGuess R (s + 1) x = parityGuess R s x
        · rw [ite_eq_left he]
          omega
        · rw [ite_eq_right he]
          have hne : R (s + 1) x ≠ R s x := by
            intro h
            exact he (congrArg (fun k => k % 2) h)
          omega
  exact ⟨hcomp, hbinary, hzero, hcount, fun s x => (hcount s x).trans (hn s x)⟩

theorem stage_rank_convergence (n : ℕ) (e : ℕ → ℕ) (U : ℕ → Set ℕ)
    (hU : ∀ i, i < n → U i = EffectiveEnumerations.indexSet (e i)) (x : ℕ) :
    ∃ t, ∀ s, t ≤ s → stageRank e n s x = membershipRank n U x := by
  induction n with
  | zero => exact ⟨0, fun _ _ => rfl⟩
  | succ n ih =>
      obtain ⟨t, ht⟩ := ih (fun i hi => hU i (by omega))
      obtain ⟨u, hu⟩ := canonical_stage_converges (e n) x
      refine ⟨max t u, fun s hs => ?_⟩
      simp only [stageRank, membershipRank, ht s (by omega), hu s (by omega),
        hU n (by omega)]

theorem chain_approximation_data (n : ℕ) (e : ℕ → ℕ) (U : ℕ → Set ℕ)
    (he : ∀ i, i < n → U i = EffectiveEnumerations.indexSet (e i)) (hU : Nested n U) :
    Computable₂ (chainGuess n e) ∧ Binary (chainGuess n e) ∧
      StartsZero (chainGuess n e) ∧ AtMostChanges (chainGuess n e) n ∧
      Converges (chainGuess n e) (alternatingDifference n U) := by
  classical
  obtain ⟨hc, hz, hn, hm⟩ := stage_rank_data n e
  obtain ⟨hpc, hpb, hpz, _, hpn⟩ := parity_rank_data (stageRank e n) n hc hz hm hn
  refine ⟨hpc, hpb, hpz, hpn, fun x => ?_⟩
  obtain ⟨t, ht⟩ := stage_rank_convergence n e U he x
  refine ⟨t, fun s hs => ?_⟩
  change stageRank e n s x % 2 = indicator (alternatingDifference n U) x
  rw [ht s hs]
  have hpar := alternating_iff_odd_rank n U hU x
  have hb := Nat.mod_lt (membershipRank n U x) (by omega : 0 < 2)
  by_cases hx : x ∈ alternatingDifference n U
  · have ho := hpar.mp hx
    simp [indicator, show alternatingDifference n U x from hx, ho]
  · have hz : membershipRank n U x % 2 = 0 := by
      have hne : membershipRank n U x % 2 ≠ 1 := fun h => hx (hpar.mpr h)
      omega
    simp [indicator, show ¬alternatingDifference n U x from hx, hz]

theorem finite_difference_characterization (n : ℕ) (A : Set ℕ) :
    NCE n A ↔ ∃ U : ℕ → Set ℕ, EnumerableChain n U ∧ A = alternatingDifference n U := by
  classical
  constructor
  · rintro ⟨a, ha, hb, hc, hz, hn⟩
    exact ⟨thresholdSet a, threshold_reconstruction a A n ha hb hc hz hn⟩
  · rintro ⟨U, hU, rfl⟩
    have hex : ∀ i, ∃ e, i < n → U i = EffectiveEnumerations.indexSet e := by
      intro i
      by_cases hi : i < n
      · obtain ⟨e, he⟩ := (enumerable_iff_index (U i)).mp (hU.2 i hi)
        exact ⟨e, fun _ => Set.ext he⟩
      · exact ⟨0, fun h => (hi h).elim⟩
    choose e he using hex
    obtain ⟨hc, hb, hz, hn, hlim⟩ := chain_approximation_data n e U he hU.1
    exact ⟨chainGuess n e, hc, hb, hlim, hz, hn⟩

end Lemmatheca.ComputabilityTheory.FiniteDifferenceNormalForms
