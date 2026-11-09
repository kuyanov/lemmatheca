import Lemmatheca.FiniteDifferenceNormalForms.Basic

/-! One uniform positive search records all finite revision thresholds. -/
namespace Lemmatheca.ComputabilityTheory.FiniteDifferenceNormalForms

open UniversalComputation LimitComputability DifferenceEnumerable FiniteMindChanges

set_option backward.isDefEq.respectTransparency false

def thresholdSet (a : Approximation) (i : ℕ) : Set ℕ :=
  {x | ∃ s, i + 1 ≤ changeCount a s x}

def thresholdFamily (a : Approximation) : Set ℕ :=
  {z | z.unpair.2 ∈ thresholdSet a z.unpair.1}

theorem threshold_family_enumerable (a : Approximation) (ha : Computable₂ a) :
    REPred (thresholdFamily a) := by
  have hleft : Computable (fun p : ℕ × ℕ => p.1.unpair.1 + 1) :=
    Computable.succ.comp (Computable.fst.comp (Computable.unpair.comp Computable.fst))
  have hright : Computable (fun p : ℕ × ℕ => changeCount a p.2 p.1.unpair.2) :=
    (changeCount_computable a ha).comp Computable.snd
      (Computable.snd.comp (Computable.unpair.comp Computable.fst))
  have hp : ComputablePred (fun p : ℕ × ℕ =>
      p.1.unpair.1 + 1 ≤ changeCount a p.2 p.1.unpair.2) :=
    (Primrec.nat_le.decide.to_comp.comp hleft hright).computablePred
  exact (enumerable_iff_decidable_certificate _).mpr
    ⟨fun z s => z.unpair.1 + 1 ≤ changeCount a s z.unpair.2, hp, fun _ => Iff.rfl⟩

theorem threshold_enumerable (a : Approximation) (ha : Computable₂ a) (i : ℕ) :
    REPred (thresholdSet a i) := by
  have hp : ComputablePred (fun p : ℕ × ℕ => i + 1 ≤ changeCount a p.2 p.1) :=
    (Primrec.nat_le.decide.to_comp.comp (Computable.const (i + 1))
      ((changeCount_computable a ha).comp Computable.snd Computable.fst)).computablePred
  exact (enumerable_iff_decidable_certificate _).mpr
    ⟨fun x s => i + 1 ≤ changeCount a s x, hp, fun _ => Iff.rfl⟩

theorem threshold_nested (a : Approximation) (n : ℕ) :
    Nested n (thresholdSet a) := by
  intro i j hij _ x hx
  obtain ⟨s, hs⟩ := hx
  exact ⟨s, by omega⟩

theorem threshold_empty (a : Approximation) (n i : ℕ) (hn : AtMostChanges a n)
    (hi : n ≤ i) : thresholdSet a i = ∅ := by
  ext x
  constructor
  · rintro ⟨s, hs⟩
    have hb := hn s x
    omega
  · exact False.elim

theorem bounded_counter_max (a : Approximation) (n : ℕ) (hn : AtMostChanges a n) (x : ℕ) :
    ∃ r, r ≤ n ∧ ∃ t, changeCount a t x = r ∧
      (∀ s, changeCount a s x ≤ r) ∧ ∀ s, t ≤ s → changeCount a s x = r := by
  classical
  let P : ℕ → Prop := fun k => ∃ s, changeCount a s x = k
  have hp : P 0 := ⟨0, rfl⟩
  let r := Nat.findGreatest P n
  obtain ⟨t, ht⟩ := Nat.findGreatest_spec (P := P) (Nat.zero_le n) hp
  change changeCount a t x = r at ht
  have hr : ∀ s, changeCount a s x ≤ r := fun s =>
    Nat.le_findGreatest (P := P) (hn s x) ⟨s, rfl⟩
  refine ⟨r, Nat.findGreatest_le n, t, ht, hr, fun s hs => ?_⟩
  apply Nat.le_antisymm (hr s)
  rw [← ht]
  exact changeCount_monotone a x hs

theorem threshold_membership (a : Approximation) (x r : ℕ)
    (ht : ∃ t, changeCount a t x = r) (hr : ∀ s, changeCount a s x ≤ r) (i : ℕ) :
    x ∈ thresholdSet a i ↔ i < r := by
  constructor
  · rintro ⟨s, hs⟩
    have hb := hr s
    omega
  · intro hi
    obtain ⟨t, ht⟩ := ht
    exact ⟨t, by omega⟩

theorem threshold_reconstruction (a : Approximation) (A : Set ℕ) (n : ℕ)
    (ha : Computable₂ a) (hb : Binary a) (hc : Converges a A)
    (hz : StartsZero a) (hn : AtMostChanges a n) :
    EnumerableChain n (thresholdSet a) ∧ A = alternatingDifference n (thresholdSet a) := by
  classical
  have hchain : EnumerableChain n (thresholdSet a) :=
    ⟨threshold_nested a n, fun i _ => threshold_enumerable a ha i⟩
  refine ⟨hchain, ?_⟩
  ext x
  obtain ⟨r, hrn, t, ht, hr, hst⟩ := bounded_counter_max a n hn x
  have hrank : membershipRank n (thresholdSet a) x = r := by
    have hbound := membership_rank_bound n (thresholdSet a) x
    by_contra hne
    by_cases hlt : membershipRank n (thresholdSet a) x < r
    · have hmem := (threshold_membership a x r ⟨t, ht⟩ hr _).mpr hlt
      have hbad := (nested_membership_initial n (thresholdSet a) hchain.1 x _
        (by omega)).mp hmem
      omega
    · have hmem := (nested_membership_initial n (thresholdSet a) hchain.1 x r
        (by omega)).mpr (by omega)
      have hbad := (threshold_membership a x r ⟨t, ht⟩ hr r).mp hmem
      omega
  obtain ⟨u, hu⟩ := hc x
  have hbit : indicator A x = r % 2 := by
    rw [← hu (max t u) (le_max_right _ _), count_parity a hb hz,
      hst (max t u) (le_max_left _ _)]
  rw [alternating_iff_odd_rank n (thresholdSet a) hchain.1 x, hrank, ← hbit]
  simp only [indicator, ite_eq_left_iff, Nat.zero_ne_one, imp_false, not_not]
  change A x ↔ A x
  rfl

end Lemmatheca.ComputabilityTheory.FiniteDifferenceNormalForms
