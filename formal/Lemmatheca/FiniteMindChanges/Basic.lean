import Lemmatheca.DifferencesOfEnumerableSets.Basic

/-! Fixed finite revision allowances, with the prescribed initial bit zero. -/
namespace Lemmatheca.ComputabilityTheory.FiniteMindChanges

open UniversalComputation LimitComputability DifferenceEnumerable

set_option backward.isDefEq.respectTransparency false

noncomputable def NCE (n : ℕ) (A : Set ℕ) : Prop :=
  ∃ a : Approximation, Computable₂ a ∧ Binary a ∧ Converges a A ∧
    StartsZero a ∧ AtMostChanges a n

noncomputable def CoNCE (n : ℕ) (A : Set ℕ) : Prop := NCE n Aᶜ

private theorem zero_count_constant (a : Approximation) (hn : AtMostChanges a 0)
    (s x : ℕ) : a s x = a 0 x := by
  by_contra hne
  have hlt := changeCount_strict_of_ne a x (Nat.zero_le s) (Ne.symm hne)
  have hle := hn s x
  simp only [changeCount] at hlt
  omega

theorem bounded_counts_converge (a : Approximation) (n : ℕ)
    (hb : Binary a) (hn : AtMostChanges a n) : ∃ A : Set ℕ, Converges a A := by
  classical
  have hstable : ∀ x, ∃ t, ∀ s, t ≤ s → a s x = a t x := by
    intro x
    let P : ℕ → Prop := fun k => ∃ s, changeCount a s x = k
    have hp : P 0 := ⟨0, rfl⟩
    obtain ⟨t, ht⟩ := Nat.findGreatest_spec (P := P) (Nat.zero_le n) hp
    refine ⟨t, fun s hts => ?_⟩
    by_contra hne
    have hlt := changeCount_strict_of_ne a x hts (Ne.symm hne)
    have hle := Nat.le_findGreatest (P := P) (hn s x) ⟨s, rfl⟩
    omega
  let t : ℕ → ℕ := fun x => Classical.choose (hstable x)
  let A : Set ℕ := {x | a (t x) x = 1}
  refine ⟨A, fun x => ⟨t x, fun s hs => ?_⟩⟩
  have hst : a s x = a (t x) x := Classical.choose_spec (hstable x) s hs
  rw [hst]
  rcases hb (t x) x with hz | ho
  · simp [indicator, A, Set.ofPred, hz]
  · simp [indicator, A, Set.ofPred, ho]

theorem nce_zero_iff (A : Set ℕ) : NCE 0 A ↔ A = ∅ := by
  classical
  constructor
  · rintro ⟨a, _hc, _hb, ha, hz, hn⟩
    ext x
    constructor
    · intro hx
      exfalso
      obtain ⟨t, ht⟩ := ha x
      have hbit := ht t le_rfl
      have hzero := (zero_count_constant a hn t x).trans (hz x)
      have hAx : A x := hx
      simp [indicator, hAx, hzero] at hbit
    · exact False.elim
  · rintro rfl
    refine ⟨fun _ _ => 0, Computable.const 0, fun _ _ => Or.inl rfl, ?_,
      fun _ => rfl, ?_⟩
    · intro x
      exact ⟨0, fun _ _ => by simp [indicator, EmptyCollection.emptyCollection]⟩
    · intro s x
      induction s with
      | zero => rfl
      | succ s ih => simpa [changeCount] using ih

theorem unrestricted_zero_iff (A : Set ℕ) :
    (∃ a : Approximation, Computable₂ a ∧ Binary a ∧ Converges a A ∧
      AtMostChanges a 0) ↔ ComputablePred A := by
  classical
  constructor
  · rintro ⟨a, hc, _hb, ha, hn⟩
    apply (decidable_iff_characteristic A).mpr
    refine ⟨a 0, hc.comp (Computable.const 0) Computable.id, fun x => ?_⟩
    obtain ⟨t, ht⟩ := ha x
    exact (zero_count_constant a hn t x).symm.trans (ht t le_rfl)
  · intro hA
    obtain ⟨f, hf, he⟩ := (decidable_iff_characteristic A).mp hA
    refine ⟨fun _ x => f x, hf.comp Computable.snd, ?_, ?_, ?_⟩
    · intro s x
      change f x = 0 ∨ f x = 1
      rw [he x]
      simp only [indicator]
      split <;> simp
    · intro x
      exact ⟨0, fun _ _ => he x⟩
    · intro s x
      induction s with
      | zero => rfl
      | succ s ih => simpa [changeCount] using ih

theorem nce_mono {m n : ℕ} (hmn : m ≤ n) (A : Set ℕ) (ha : NCE m A) : NCE n A := by
  obtain ⟨a, hc, hb, he, hz, hn⟩ := ha
  exact ⟨a, hc, hb, he, hz, fun s x => (hn s x).trans hmn⟩

theorem nce_limit_computable (n : ℕ) (A : Set ℕ) (ha : NCE n A) : LimitComputable A := by
  obtain ⟨a, hc, hb, he, _hz, _hn⟩ := ha
  exact ⟨a, hc, hb, he⟩

end Lemmatheca.ComputabilityTheory.FiniteMindChanges
