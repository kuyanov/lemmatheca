import Lemmatheca.OneGenericSets.Construction

/-! The specified bit-coding history reuses the deterministic generic selector. -/
namespace Lemmatheca.ComputabilityTheory.FriedbergJumpInversion

open OracleComputation OracleProgramNumberings IncomparableTuringDegrees
  ComputableTreesAndPaths PostsTheorem UniversalComputation OneGenericSets TuringDegrees

noncomputable section
set_option autoImplicit false

def codingState (B : Set ℕ) (rho : ℕ) : ℕ → ℕ
  | 0 => Nat.pair 0 (OneGenericSets.normalize rho)
  | n + 1 => Nat.pair (n + 1)
      (appendBit (H n (codingState B rho n).unpair.2) (indicator (fun q => q ∈ B) n))

def codingWord (B : Set ℕ) (rho n : ℕ) : ℕ := (codingState B rho n).unpair.2

def codingExtension (B : Set ℕ) (rho n : ℕ) : ℕ := H n (codingWord B rho n)

def codedSet (B : Set ℕ) (rho : ℕ) : Set ℕ := unionSet (codingWord B rho)

theorem coding_recurrence (B : Set ℕ) (rho n : ℕ) :
    codingWord B rho 0 = OneGenericSets.normalize rho ∧
      codingWord B rho (n + 1) = appendBit (codingExtension B rho n)
        (indicator (fun q => q ∈ B) n) := by
  constructor <;> simp only [codingWord, codingState, codingExtension, Nat.unpair_pair]

theorem coding_invariant (B : Set ℕ) (rho n : ℕ) :
    (codingState B rho n).unpair.1 = n ∧ ValidCode (codingWord B rho n) ∧
      ValidCode (codingExtension B rho n) ∧
      Prefix (codingWord B rho n) (codingExtension B rho n) ∧
      Prefix (codingExtension B rho n) (codingWord B rho (n + 1)) ∧
      wordLength (codingWord B rho (n + 1)) = wordLength (codingExtension B rho n) + 1 ∧
      wordLength rho + n ≤ wordLength (codingWord B rho n) := by
  have hv : ∀ j, ValidCode (codingWord B rho j) := by
    intro j
    cases j with
    | zero => rw [(coding_recurrence B rho 0).1]; exact (normalize_spec rho).1
    | succ j =>
      rw [(coding_recurrence B rho j).2]
      exact append_valid _ _ (H_spec j (codingWord B rho j)).1
  have hh (j : ℕ) : Prefix (codingWord B rho j) (codingExtension B rho j) := by
    have h := (H_spec j (codingWord B rho j)).2.1
    rw [normalize_valid _ (hv j)] at h
    exact h
  have hl (j : ℕ) : wordLength rho + j ≤ wordLength (codingWord B rho j) := by
    induction j with
    | zero => rw [(coding_recurrence B rho 0).1, (normalize_spec rho).2.2]; omega
    | succ j ih =>
      have hb := (hh j).1
      rw [(coding_recurrence B rho j).2, (appendBit_spec _ _).1]
      omega
  refine ⟨?_, hv n, (H_spec n (codingWord B rho n)).1, hh n, ?_, ?_, hl n⟩
  · cases n <;> simp [codingState]
  · rw [(coding_recurrence B rho n).2]
    exact (appendBit_spec _ _).2.1
  · rw [(coding_recurrence B rho n).2, (appendBit_spec _ _).1]

theorem coded_prefixes (B : Set ℕ) (rho : ℕ) :
    (∀ n, Realizes (codingWord B rho n) (codedSet B rho)) ∧
      ∀ X : Set ℕ, (∀ n, Realizes (codingWord B rho n) X) → X = codedSet B rho := by
  apply coherent_union (codingWord B rho)
  · intro n
    have h := coding_invariant B rho n
    exact prefix_trans h.2.2.2.1 h.2.2.2.2.1
  · intro n
    have h := (coding_invariant B rho n).2.2.2.2.2.2
    omega

theorem coded_characteristic (B : Set ℕ) (rho x : ℕ) :
    indicator (fun q => q ∈ codedSet B rho) x = wordBit (codingWord B rho (x + 1)) x := by
  exact union_bit (codingWord B rho) x

theorem coding_bit (B : Set ℕ) (rho n : ℕ) :
    indicator (fun q => q ∈ codedSet B rho) (wordLength (codingExtension B rho n)) =
      indicator (fun q => q ∈ B) n := by
  have hr := (coded_prefixes B rho).1 (n + 1)
  have hlen := (coding_invariant B rho n).2.2.2.2.2.1
  have hb := hr (wordLength (codingExtension B rho n)) (by omega)
  rw [(coding_recurrence B rho n).2, (appendBit_spec _ _).2.2] at hb
  have hi : indicator (fun q => q ∈ B) n < 2 := by
    unfold indicator
    split_ifs <;> omega
  rw [Nat.mod_eq_of_lt hi] at hb
  exact hb.symm

theorem coded_extends (B : Set ℕ) (rho : ℕ) (hrho : ValidCode rho) :
    Realizes rho (codedSet B rho) := by
  have h := (coded_prefixes B rho).1 0
  rw [(coding_recurrence B rho 0).1, normalize_valid rho hrho] at h
  exact h

theorem coded_generic (B : Set ℕ) (rho : ℕ) : IsOneGeneric (codedSet B rho) := by
  apply generic_of_H_history _ (codingWord B rho) (coded_prefixes B rho).1
  intro n
  exact (coding_invariant B rho n).2.2.2.2.1

end
end Lemmatheca.ComputabilityTheory.FriedbergJumpInversion
