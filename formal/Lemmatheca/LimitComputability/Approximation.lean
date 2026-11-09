import Lemmatheca.EffectiveEnumerations.Stages
import Lemmatheca.TuringDegrees.Reductions

/-! Pointwise binary approximations and their finite-snapshot presentation. -/
namespace Lemmatheca.ComputabilityTheory.LimitComputability

open UniversalComputation

set_option backward.isDefEq.respectTransparency false

abbrev Approximation := ℕ → ℕ → ℕ

def Binary (a : Approximation) : Prop := ∀ s x, a s x = 0 ∨ a s x = 1

noncomputable def Converges (a : Approximation) (A : Set ℕ) : Prop :=
  ∀ x, ∃ t, ∀ s, t ≤ s → a s x = indicator A x

noncomputable def LimitComputable (A : Set ℕ) : Prop :=
  ∃ a : Approximation, Computable₂ a ∧ Binary a ∧ Converges a A

def truncate (a : Approximation) (s x : ℕ) : ℕ := if x < s then a s x else 0

theorem truncate_computable (a : Approximation) (ha : Computable₂ a) :
    Computable₂ (truncate a) := by
  exact (Computable.cond
    (Primrec.nat_lt.comp Primrec.snd Primrec.fst).decide.to_comp ha (Computable.const 0)).of_eq
      (fun p => by simp [truncate])

theorem truncate_binary (a : Approximation) (ha : Binary a) : Binary (truncate a) := by
  intro s x
  unfold truncate
  split
  · exact ha s x
  · exact Or.inl rfl

theorem truncate_finite (a : Approximation) (s : ℕ) :
    {x | truncate a s x = 1} ⊆ Set.Iio s ∧ {x | truncate a s x = 1}.Finite := by
  have hb : {x | truncate a s x = 1} ⊆ Set.Iio s := by
    intro x hx
    by_contra h
    have hn : ¬x < s := h
    simp [truncate, hn] at hx
  exact ⟨hb, (Set.finite_Iio s).subset hb⟩

theorem truncate_converges (a : Approximation) (A : Set ℕ) (ha : Converges a A) :
    Converges (truncate a) A := by
  intro x
  obtain ⟨t, ht⟩ := ha x
  refine ⟨max t (x + 1), fun s hs => ?_⟩
  have hxs : x < s := by omega
  rw [truncate, ite_eq_left hxs]
  exact ht s (by omega)

theorem finite_snapshot_characterization (A : Set ℕ) :
    LimitComputable A ↔ ∃ a : Approximation,
      Computable₂ a ∧ Binary a ∧ Converges a A ∧ ∀ s x, a s x = 1 → x < s := by
  constructor
  · rintro ⟨a, hc, hb, ha⟩
    exact ⟨truncate a, truncate_computable a hc, truncate_binary a hb,
      truncate_converges a A ha, fun s x hx => (truncate_finite a s).1 hx⟩
  · rintro ⟨a, hc, hb, ha, _⟩
    exact ⟨a, hc, hb, ha⟩

theorem finite_prefix_stabilization (a : Approximation) (A : Set ℕ)
    (ha : Converges a A) (n : ℕ) :
    ∃ t, ∀ s, t ≤ s → ∀ x < n, a s x = indicator A x := by
  induction n with
  | zero => exact ⟨0, fun _ _ _ hx => False.elim (Nat.not_lt_zero _ hx)⟩
  | succ n ih =>
      obtain ⟨t, ht⟩ := ih
      obtain ⟨u, hu⟩ := ha n
      refine ⟨max t u, ?_⟩
      intro s hs x hx
      by_cases hxn : x < n
      · exact ht s (by omega) x hxn
      · have he : x = n := by omega
        subst x
        exact hu s (by omega)

theorem finitely_many_changes (a : Approximation) (A : Set ℕ)
    (ha : Converges a A) (x : ℕ) : {s | a (s + 1) x ≠ a s x}.Finite := by
  obtain ⟨t, ht⟩ := ha x
  apply (Set.finite_Iio t).subset
  intro s hs
  by_contra h
  have hts : t ≤ s := Nat.le_of_not_gt h
  exact hs ((ht (s + 1) (by omega)).trans (ht s hts).symm)

def complementApproximation (a : Approximation) (s x : ℕ) : ℕ := 1 - a s x

theorem complement_approximation (a : Approximation) (A : Set ℕ)
    (hc : Computable₂ a) (hb : Binary a) (ha : Converges a A) :
    Computable₂ (complementApproximation a) ∧ Binary (complementApproximation a) ∧
      Converges (complementApproximation a) Aᶜ := by
  classical
  refine ⟨Primrec.nat_sub.to_comp.comp (Computable.const 1) hc, ?_, ?_⟩
  · intro s x
    rcases hb s x with h | h <;> simp [complementApproximation, h]
  · intro x
    obtain ⟨t, ht⟩ := ha x
    refine ⟨t, fun s hs => ?_⟩
    rw [complementApproximation, ht s hs]
    simp only [indicator, Compl.compl, Set.ofPred]
    by_cases hx : A x <;> simp [hx] <;> exact hx

theorem canonical_stage_converges (e : ℕ) :
    Converges (EffectiveEnumerations.stageTest e) (EffectiveEnumerations.indexSet e) := by
  classical
  intro x
  by_cases hx : x ∈ EffectiveEnumerations.indexSet e
  · obtain ⟨t, ht⟩ := (EffectiveEnumerations.stage_union e x).mp hx
    refine ⟨t, fun s hs => ?_⟩
    have hm := EffectiveEnumerations.stage_monotone e hs ht
    have hp := (EffectiveEnumerations.stage_test_spec e s x).2.mpr hm
    change EffectiveEnumerations.stageTest e s x = if x ∈ EffectiveEnumerations.indexSet e then 1 else 0
    simpa only [ite_eq_left hx] using hp
  · refine ⟨0, fun s _ => ?_⟩
    have hn : EffectiveEnumerations.stageTest e s x ≠ 1 := by
      intro hp
      exact hx ((EffectiveEnumerations.stage_union e x).mpr
        ⟨s, (EffectiveEnumerations.stage_test_spec e s x).2.mp hp⟩)
    have hz := ((EffectiveEnumerations.stage_test_spec e s x).1).resolve_right hn
    change EffectiveEnumerations.stageTest e s x = if x ∈ EffectiveEnumerations.indexSet e then 1 else 0
    simpa only [ite_eq_right hx] using hz

theorem enumerable_limit (A : Set ℕ) (hA : REPred A) : LimitComputable A := by
  obtain ⟨e, he⟩ := (enumerable_iff_index A).mp hA
  have hEq : A = EffectiveEnumerations.indexSet e := Set.ext he
  rw [hEq]
  exact ⟨EffectiveEnumerations.stageTest e,
    (EffectiveEnumerations.canonical_test_data e).1,
    (EffectiveEnumerations.canonical_test_data e).2.1, canonical_stage_converges e⟩

theorem coenumerable_limit (A : Set ℕ) (hA : REPred Aᶜ) : LimitComputable A := by
  obtain ⟨a, hc, hb, ha⟩ := enumerable_limit Aᶜ hA
  obtain ⟨hcc, hbc, hac⟩ := complement_approximation a Aᶜ hc hb ha
  exact ⟨complementApproximation a, hcc, hbc, by simpa using hac⟩

noncomputable def ConvergenceModulus (a : Approximation) (A : Set ℕ) (m : ℕ → ℕ) : Prop :=
  ∀ x s, m x ≤ s → a s x = indicator A x

theorem convergence_modulus_exists (a : Approximation) (A : Set ℕ) (ha : Converges a A) :
    ∃ m, ConvergenceModulus a A m := by
  classical
  exact ⟨fun x => Classical.choose (ha x), fun x => Classical.choose_spec (ha x)⟩

def modulusDecider (a : Approximation) (m : ℕ → ℕ) (x : ℕ) : ℕ := a (m x) x

theorem modulus_decider_correct (a : Approximation) (A : Set ℕ) (m : ℕ → ℕ)
    (ha : Computable₂ a) (hm : Computable m) (hs : ConvergenceModulus a A m) :
    Computable (modulusDecider a m) ∧ ∀ x, modulusDecider a m x = indicator A x := by
  exact ⟨ha.comp hm Computable.id, fun x => hs x (m x) le_rfl⟩

theorem computable_modulus_decides (a : Approximation) (A : Set ℕ) (m : ℕ → ℕ)
    (ha : Computable₂ a) (hm : Computable m) (hs : ConvergenceModulus a A m) :
    ComputablePred A := by
  exact (decidable_iff_characteristic A).mpr
    ⟨modulusDecider a m, modulus_decider_correct a A m ha hm hs⟩

end Lemmatheca.ComputabilityTheory.LimitComputability
