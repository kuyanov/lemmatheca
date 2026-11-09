import Lemmatheca.UniversalFiniteChangeSets.Simulator

/-! Faithfulness of the supplied clipped simulator needs a bound only at its chosen input. -/
namespace Lemmatheca.ComputabilityTheory.BeyondComputableChangeBounds

open UniversalComputation LimitComputability DifferenceEnumerable FiniteMindChanges
open UniversalFiniteChangeSets

set_option backward.isDefEq.respectTransparency false

def PresentsAt (p : ℕ) (a : Approximation) (x : ℕ) : Prop :=
  ∀ k, phi p (Nat.pair k x) = Part.some (a k x)

private theorem supplied_value (e x : ℕ) (a : Approximation) (hp : PresentsAt e a x)
    (s k : ℕ) (h : boundedValue s e (Nat.pair k x) = 1 ∨
      boundedValue s e (Nat.pair k x) = 2) :
    boundedValue s e (Nat.pair k x) - 1 = a k x := by
  have hv : boundedValue s e (Nat.pair k x) =
      (boundedValue s e (Nat.pair k x) - 1) + 1 := by omega
  exact Part.mem_unique ((phi_output e (Nat.pair k x) _).mpr ⟨s, hv⟩)
    (Part.eq_some_iff.mp (hp k))

private theorem cursor_monotone (n e x : ℕ) :
    Monotone (fun s => (simulation n e x s).1) :=
  monotone_nat_of_le_succ fun s => (simulation_invariants n e x s).2.2.2

private theorem exhausted_constant (a : Approximation) (n r x : ℕ)
    (hn : ∀ s, changeCount a s x ≤ n) (h : changeCount a r x = n) :
    ∀ t, r ≤ t → a t x = a r x := by
  intro t ht
  by_contra he
  have hstrict := changeCount_strict_of_ne a x ht (Ne.symm he)
  have hbound := hn t
  omega

theorem pointwise_prefix (n p : ℕ) (a : Approximation) (x : ℕ)
    (hp : PresentsAt p a x) (hz : a 0 x = 0)
    (hn : ∀ s, changeCount a s x ≤ n) (s : ℕ) :
    (simulation n p x s).2.1 = a ((simulation n p x s).1 - 1) x ∧
      (simulation n p x s).2.2 = changeCount a ((simulation n p x s).1 - 1) x ∧
      ((simulation n p x s).2.2 = n →
        ∀ t, (simulation n p x s).1 - 1 ≤ t → a t x = (simulation n p x s).2.1) := by
  have hcore : ∀ s,
      (simulation n p x s).2.1 = a ((simulation n p x s).1 - 1) x ∧
      (simulation n p x s).2.2 = changeCount a ((simulation n p x s).1 - 1) x := by
    intro s
    induction s with
    | zero => simp [simulation, changeCount, hz]
    | succ s ih =>
        by_cases hc : (simulation n p x s).2.2 < n
        · by_cases hv : boundedValue s p (Nat.pair (simulation n p x s).1 x) = 1 ∨
              boundedValue s p (Nat.pair (simulation n p x s).1 x) = 2
          · have ha := supplied_value p x a hp s (simulation n p x s).1 hv
            simp only [simulation, step, ite_eq_left hc, ite_eq_left hv, Nat.add_sub_cancel]
            constructor
            · exact ha
            · rw [ha, ih.1, ih.2]
              by_cases hk : (simulation n p x s).1 = 0
              · simp [hk, hz, changeCount]
              · have hk' : (simulation n p x s).1 =
                    ((simulation n p x s).1 - 1) + 1 := by omega
                conv_rhs => rw [hk', changeCount]
                rw [← hk']
          · simpa only [simulation, step, ite_eq_left hc, ite_eq_right hv] using ih
        · simpa only [simulation, step, ite_eq_right hc] using ih
  refine ⟨(hcore s).1, (hcore s).2, ?_⟩
  intro he t ht
  have hh : changeCount a ((simulation n p x s).1 - 1) x = n := by
    rw [← (hcore s).2, he]
  exact (exhausted_constant a n _ x hn hh t ht).trans (hcore s).1.symm

theorem pointwise_progress (n p : ℕ) (a : Approximation) (x : ℕ)
    (hp : PresentsAt p a x) (hb : ∀ k, a k x = 0 ∨ a k x = 1) (m : ℕ) :
    ∃ s, m ≤ (simulation n p x s).1 ∨ (simulation n p x s).2.2 = n := by
  induction m with
  | zero => exact ⟨0, Or.inl (Nat.zero_le _)⟩
  | succ m ih =>
      obtain ⟨t, ht | ht⟩ := ih
      · by_cases hm : m + 1 ≤ (simulation n p x t).1
        · exact ⟨t, Or.inl hm⟩
        have hmt : (simulation n p x t).1 = m := by omega
        have hav : a m x ∈ phi p (Nat.pair m x) := Part.eq_some_iff.mp (hp m)
        obtain ⟨k, hk⟩ := (phi_output p (Nat.pair m x) _).mp hav
        let u := max t k
        have hcur : m ≤ (simulation n p x u).1 := by
          rw [← hmt]
          exact cursor_monotone n p x (le_max_left _ _)
        by_cases hm' : m + 1 ≤ (simulation n p x u).1
        · exact ⟨u, Or.inl hm'⟩
        have hmu : (simulation n p x u).1 = m := by omega
        by_cases hc : (simulation n p x u).2.2 = n
        · exact ⟨u, Or.inr hc⟩
        have hcn : (simulation n p x u).2.2 < n := by
          have hbound := (simulation_invariants n p x u).2.1
          omega
        have hval : boundedValue u p (Nat.pair m x) = a m x + 1 :=
          (boundedValue_output _ _ _ _).mpr
            (Nat.Partrec.Code.evaln_mono (le_max_right t k)
              ((boundedValue_output _ _ _ _).mp hk))
        have hv : boundedValue u p (Nat.pair m x) = 1 ∨
            boundedValue u p (Nat.pair m x) = 2 := by
          rcases hb m with h | h <;> simp [hval, h]
        refine ⟨u + 1, Or.inl ?_⟩
        simp [simulation, step, hcn, hmu, hv]
      · exact ⟨t, Or.inr ht⟩

theorem pointwise_faithfulness (n p : ℕ) (a : Approximation) (x ell : ℕ)
    (hp : PresentsAt p a x) (hb : ∀ k, a k x = 0 ∨ a k x = 1)
    (hz : a 0 x = 0) (hn : ∀ s, changeCount a s x ≤ n)
    (hl : ∃ t, ∀ k, t ≤ k → a k x = ell) :
    (∃ t, ∀ s, t ≤ s → universalGuess n p s x = ell) ∧
      (x ∈ rowSet n p ↔ ell = 1) := by
  have hlim : ∃ t, ∀ s, t ≤ s → universalGuess n p s x = ell := by
    obtain ⟨t, ht⟩ := hl
    obtain ⟨s, hcur | hfull⟩ := pointwise_progress n p a x hp hb (t + 1)
    · refine ⟨s, fun u hu => ?_⟩
      have hm : (simulation n p x s).1 ≤ (simulation n p x u).1 := cursor_monotone n p x hu
      have hind : t ≤ (simulation n p x u).1 - 1 := by omega
      exact (pointwise_prefix n p a x hp hz hn u).1.trans (ht _ hind)
    · have hprefix := pointwise_prefix n p a x hp hz hn s
      have hbval : (simulation n p x s).2.1 = ell := by
        have he := hprefix.2.2 hfull (max t ((simulation n p x s).1 - 1))
          (le_max_right _ _)
        exact he.symm.trans (ht _ (le_max_left _ _))
      refine ⟨s, fun u hu => ?_⟩
      have hm : (simulation n p x s).1 ≤ (simulation n p x u).1 := cursor_monotone n p x hu
      have he := hprefix.2.2 hfull ((simulation n p x u).1 - 1) (by omega)
      exact (pointwise_prefix n p a x hp hz hn u).1.trans (he.trans hbval)
  refine ⟨hlim, ?_⟩
  obtain ⟨t, ht⟩ := hlim
  constructor
  · rintro ⟨u, hu⟩
    exact (ht (max t u) (le_max_left _ _)).symm.trans (hu _ (le_max_right _ _))
  · intro he
    exact ⟨t, fun s hs => (ht s hs).trans he⟩

end Lemmatheca.ComputabilityTheory.BeyondComputableChangeBounds
