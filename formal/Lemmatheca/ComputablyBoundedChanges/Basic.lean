import Lemmatheca.FiniteMindChanges.Operations

/-! Input-dependent revision bounds and their natural-number countdown form. -/
namespace Lemmatheca.ComputabilityTheory.ComputablyBoundedChanges

open UniversalComputation LimitComputability DifferenceEnumerable FiniteMindChanges

set_option backward.isDefEq.respectTransparency false

def BoundedBy (a : Approximation) (b : ℕ → ℕ) : Prop :=
  ∀ s x, changeCount a s x ≤ b x

noncomputable def ComputableBound (a : Approximation) (b : ℕ → ℕ) : Prop :=
  Computable b ∧ BoundedBy a b

noncomputable def OmegaCE (A : Set ℕ) : Prop :=
  ∃ (a : Approximation) (b : ℕ → ℕ),
    Computable₂ a ∧ Binary a ∧ Converges a A ∧ StartsZero a ∧ ComputableBound a b

def Countdown (a r : Approximation) : Prop :=
  ∀ s x, r (s + 1) x ≤ r s x ∧
    (a (s + 1) x ≠ a s x → r (s + 1) x < r s x)

noncomputable def ComputableCountdown (a r : Approximation) : Prop :=
  Computable₂ r ∧ Countdown a r

def reserve (a : Approximation) (b : ℕ → ℕ) (s x : ℕ) : ℕ :=
  b x - changeCount a s x

theorem bounded_counts_converge (a : Approximation) (b : ℕ → ℕ)
    (hb : Binary a) (hn : BoundedBy a b) : ∃ A : Set ℕ, Converges a A := by
  classical
  have hstable : ∀ x, ∃ t, ∀ s, t ≤ s → a s x = a t x := by
    intro x
    let P : ℕ → Prop := fun k => ∃ s, changeCount a s x = k
    have hp : P 0 := ⟨0, rfl⟩
    obtain ⟨t, ht⟩ := Nat.findGreatest_spec (P := P) (Nat.zero_le (b x)) hp
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

theorem reserve_data (a : Approximation) (b : ℕ → ℕ)
    (hc : Computable₂ a) (hb : ComputableBound a b) :
    ComputableCountdown a (reserve a b) ∧ ∀ x, reserve a b 0 x = b x := by
  have hrc : Computable₂ (reserve a b) :=
    Primrec.nat_sub.to_comp.comp (hb.1.comp Computable.snd) (changeCount_computable a hc)
  refine ⟨⟨hrc, ?_⟩, fun _ => rfl⟩
  intro s x
  have hm := changeCount_monotone a x (Nat.le_succ s)
  change changeCount a s x ≤ changeCount a (s + 1) x at hm
  constructor
  · dsimp [reserve]
    omega
  · intro hne
    have hs := hb.2 (s + 1) x
    have hstep : changeCount a (s + 1) x = changeCount a s x + 1 := by
      simp [changeCount, hne]
    dsimp [reserve]
    omega

theorem countdown_pays (a r : Approximation) (hr : Countdown a r) :
    ∀ s x, changeCount a s x + r s x ≤ r 0 x := by
  intro s x
  induction s with
  | zero => simp [changeCount]
  | succ s ih =>
      obtain ⟨hm, hd⟩ := hr s x
      by_cases h : a (s + 1) x = a s x
      · simp only [changeCount, ite_eq_left h]
        omega
      · have hdrop := hd h
        simp only [changeCount, ite_eq_right h]
        omega

theorem countdown_initial_bound (a r : Approximation) (hr : ComputableCountdown a r) :
    ComputableBound a (fun x => r 0 x) := by
  refine ⟨hr.1.comp (Computable.const 0) Computable.id, fun s x => ?_⟩
  have hp := countdown_pays a r hr.2 s x
  change changeCount a s x ≤ r 0 x
  omega

theorem omega_iff_countdown (A : Set ℕ) :
    OmegaCE A ↔ ∃ a r : Approximation,
      Computable₂ a ∧ Binary a ∧ Converges a A ∧ StartsZero a ∧
        ComputableCountdown a r := by
  constructor
  · rintro ⟨a, b, hc, hb, hl, hz, hn⟩
    exact ⟨a, reserve a b, hc, hb, hl, hz, (reserve_data a b hc hn).1⟩
  · rintro ⟨a, r, hc, hb, hl, hz, hr⟩
    exact ⟨a, fun x => r 0 x, hc, hb, hl, hz, countdown_initial_bound a r hr⟩

theorem nce_is_omega (n : ℕ) (A : Set ℕ) (ha : NCE n A) : OmegaCE A := by
  obtain ⟨a, hc, hb, hl, hz, hn⟩ := ha
  exact ⟨a, fun _ => n, hc, hb, hl, hz, Computable.const n, hn⟩

theorem omega_limit_computable (A : Set ℕ) (ha : OmegaCE A) : LimitComputable A := by
  obtain ⟨a, _b, hc, hb, hl, _hz, _hn⟩ := ha
  exact ⟨a, hc, hb, hl⟩

end Lemmatheca.ComputabilityTheory.ComputablyBoundedChanges
