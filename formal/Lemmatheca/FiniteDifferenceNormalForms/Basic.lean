import Lemmatheca.FiniteMindChanges.Operations

/-! Nested enumerable chains and their exact finite alternating differences. -/
namespace Lemmatheca.ComputabilityTheory.FiniteDifferenceNormalForms

open UniversalComputation LimitComputability DifferenceEnumerable FiniteMindChanges

set_option backward.isDefEq.respectTransparency false

def Nested (n : ℕ) (U : ℕ → Set ℕ) : Prop :=
  ∀ i j, i ≤ j → j < n → U j ⊆ U i

def EnumerableChain (n : ℕ) (U : ℕ → Set ℕ) : Prop :=
  Nested n U ∧ ∀ i, i < n → REPred (U i)

noncomputable def membershipRank : ℕ → (ℕ → Set ℕ) → ℕ → ℕ
  | 0, _, _ => 0
  | n + 1, U, x => membershipRank n U x + indicator (U n) x

def alternatingDifference (n : ℕ) (U : ℕ → Set ℕ) : Set ℕ :=
  {x | ∃ i, i < n ∧ i % 2 = 0 ∧ x ∈ U i ∧ (i + 1 = n ∨ x ∉ U (i + 1))}

theorem alternating_zero (U : ℕ → Set ℕ) : alternatingDifference 0 U = ∅ := by
  ext x
  simp [alternatingDifference]

theorem membership_rank_bound (n : ℕ) (U : ℕ → Set ℕ) (x : ℕ) :
    membershipRank n U x ≤ n := by
  classical
  induction n with
  | zero => simp [membershipRank]
  | succ n ih =>
      simp only [membershipRank, indicator]
      split_ifs <;> omega

theorem nested_membership_initial (n : ℕ) (U : ℕ → Set ℕ) (hU : Nested n U)
    (x i : ℕ) (hi : i < n) : x ∈ U i ↔ i < membershipRank n U x := by
  classical
  induction n with
  | zero => omega
  | succ n ih =>
      have hUn : Nested n U := fun j k hjk hk => hU j k hjk (by omega)
      by_cases hx : x ∈ U n
      · have hall : membershipRank (n + 1) U x = n + 1 := by
          have aux : ∀ k, k ≤ n + 1 → membershipRank k U x = k := by
            intro k
            induction k with
            | zero => intro _; rfl
            | succ k hk =>
                intro hkn
                have hm : x ∈ U k := hU k n (by omega) (by omega) hx
                simp [membershipRank, hk (by omega), indicator, show U k x from hm]
          exact aux (n + 1) le_rfl
        have hm : x ∈ U i := hU i n (by omega) (by omega) hx
        rw [hall]
        exact ⟨fun _ => hi, fun _ => hm⟩
      · have hz : indicator (U n) x = 0 := by simp [indicator, show ¬U n x from hx]
        simp only [membershipRank, hz, Nat.add_zero]
        by_cases hin : i < n
        · exact ih hUn hin
        · have hie : i = n := by omega
          subst i
          have hb := membership_rank_bound n U x
          exact ⟨fun h => (hx h).elim, fun h => by omega⟩

theorem alternating_iff_odd_rank (n : ℕ) (U : ℕ → Set ℕ) (hU : Nested n U) (x : ℕ) :
    x ∈ alternatingDifference n U ↔ membershipRank n U x % 2 = 1 := by
  have hb := membership_rank_bound n U x
  constructor
  · rintro ⟨i, hi, he, hm, hn⟩
    have hir := (nested_membership_initial n U hU x i hi).mp hm
    have hri : membershipRank n U x ≤ i + 1 := by
      rcases hn with hn | hn
      · omega
      · by_contra h
        have hip : i + 1 < n := by omega
        exact hn ((nested_membership_initial n U hU x (i + 1) hip).mpr (by omega))
    omega
  · intro hr
    have hpos : 0 < membershipRank n U x := by omega
    refine ⟨membershipRank n U x - 1, by omega, by omega, ?_, ?_⟩
    · exact (nested_membership_initial n U hU x _ (by omega)).mpr (by omega)
    · by_cases he : membershipRank n U x = n
      · exact Or.inl (by omega)
      · right
        intro hm
        have hp := (nested_membership_initial n U hU x
          (membershipRank n U x - 1 + 1) (by omega)).mp hm
        omega

theorem count_parity (a : Approximation) (hb : Binary a) (hz : StartsZero a) :
    ∀ s x, a s x = changeCount a s x % 2 := by
  intro s x
  induction s with
  | zero => simpa only [changeCount, Nat.zero_mod] using hz x
  | succ s ih =>
      classical
      rw [changeCount]
      by_cases h : a (s + 1) x = a s x
      · rw [ite_eq_left h, Nat.add_zero, h]
        exact ih
      · rw [ite_eq_right h]
        rcases hb s x with hs | hs <;>
          rcases hb (s + 1) x with ht | ht <;> omega

end Lemmatheca.ComputabilityTheory.FiniteDifferenceNormalForms
