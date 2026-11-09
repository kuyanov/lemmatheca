import Lemmatheca.LimitComputability.Approximation

/-! Prefix revision counters and differences of computably enumerable sets. -/
namespace Lemmatheca.ComputabilityTheory.DifferenceEnumerable

open UniversalComputation LimitComputability

set_option backward.isDefEq.respectTransparency false

def changeCount (a : Approximation) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | s + 1, x => changeCount a s x + if a (s + 1) x = a s x then 0 else 1

def StartsZero (a : Approximation) : Prop := ∀ x, a 0 x = 0

def AtMostChanges (a : Approximation) (n : ℕ) : Prop :=
  ∀ s x, changeCount a s x ≤ n

def IsDifferenceEnumerable (A : Set ℕ) : Prop :=
  ∃ U V : Set ℕ, REPred U ∧ REPred V ∧ A = U \ V

noncomputable def TwoChangeApproximation (A : Set ℕ) : Prop :=
  ∃ a : Approximation, Computable₂ a ∧ Binary a ∧ Converges a A ∧
    StartsZero a ∧ AtMostChanges a 2

def differenceGuess (u v : Approximation) (s x : ℕ) : ℕ := u s x * (1 - v s x)

noncomputable def stageDifference (e f : ℕ) : Approximation :=
  differenceGuess (EffectiveEnumerations.stageTest e) (EffectiveEnumerations.stageTest f)

def positiveEvents (a : Approximation) : Set ℕ := {x | ∃ r, a r x = 1}

def cancellationEvents (a : Approximation) : Set ℕ :=
  {x | ∃ r t, r < t ∧ a r x = 1 ∧ a t x = 0}

theorem changeCount_computable (a : Approximation) (ha : Computable₂ a) :
    Computable₂ (changeCount a) := by
  have hnext : Computable (fun p : (ℕ × ℕ) × (ℕ × ℕ) => a (p.2.1 + 1) p.1.2) :=
    ha.comp (Computable.succ.comp (Computable.fst.comp Computable.snd))
      (Computable.snd.comp Computable.fst)
  have hcurrent : Computable (fun p : (ℕ × ℕ) × (ℕ × ℕ) => a p.2.1 p.1.2) :=
    ha.comp (Computable.fst.comp Computable.snd) (Computable.snd.comp Computable.fst)
  have heq := Primrec.eq.decide.to_comp.comp hnext hcurrent
  have hs : Computable₂ (fun p : ℕ × ℕ => fun q : ℕ × ℕ =>
      q.2 + if a (q.1 + 1) p.2 = a q.1 p.2 then 0 else 1) := by
    exact Primrec.nat_add.to_comp.comp (Computable.snd.comp Computable.snd)
      ((Computable.cond heq (Computable.const 0) (Computable.const 1)).of_eq (fun _ => by simp))
  apply (Computable.nat_rec Computable.fst (Computable.const 0) hs).of_eq
  intro p
  induction p.1 with
  | zero => rfl
  | succ n ih => simp only [changeCount, ih]

theorem changeCount_monotone (a : Approximation) (x : ℕ) :
    Monotone (fun s => changeCount a s x) := by
  apply monotone_nat_of_le_succ
  intro s
  simp only [changeCount]
  exact Nat.le_add_right _ _

theorem changeCount_strict_of_ne (a : Approximation) (x : ℕ) {r t : ℕ}
    (hrt : r ≤ t) (hne : a r x ≠ a t x) :
    changeCount a r x < changeCount a t x := by
  revert hne
  induction t, hrt using Nat.le_induction with
  | base => exact fun h => (h rfl).elim
  | succ t hrt ih =>
      intro hne
      by_cases h : a r x = a t x
      · have hstep : a (t + 1) x ≠ a t x := fun he => hne (h.trans he.symm)
        rw [changeCount, ite_eq_right hstep]
        have hm : changeCount a r x ≤ changeCount a t x := changeCount_monotone a x hrt
        omega
      · have hi := ih h
        exact hi.trans_le (changeCount_monotone a x (Nat.le_succ t))

theorem difference_count_bound (u v : Approximation) (hu : Binary u) (hv : Binary v)
    (hmu : ∀ s x, u s x ≤ u (s + 1) x) (hmv : ∀ s x, v s x ≤ v (s + 1) x) :
    ∀ s x, changeCount (differenceGuess u v) s x ≤ u s x + v s x := by
  intro s x
  induction s with
  | zero => simp [changeCount]
  | succ s ih =>
      have hmu' := hmu s x
      have hmv' := hmv s x
      rw [changeCount]
      by_cases hd : differenceGuess u v (s + 1) x = differenceGuess u v s x
      · rw [ite_eq_left hd]
        omega
      · rw [ite_eq_right hd]
        have hs : u s x + v s x < u (s + 1) x + v (s + 1) x := by
          rcases hu s x with hu0 | hu0 <;> rcases hu (s + 1) x with hu1 | hu1 <;>
            rcases hv s x with hv0 | hv0 <;> rcases hv (s + 1) x with hv1 | hv1 <;>
            simp [differenceGuess, hu0, hu1, hv0, hv1] at hd hmu' hmv' ⊢
        omega

private theorem stageTest_zero (e x : ℕ) : EffectiveEnumerations.stageTest e 0 x = 0 := by
  rcases (EffectiveEnumerations.stage_test_spec e 0 x).1 with h | h
  · exact h
  · have hx := (EffectiveEnumerations.canonical_test_data e).2.2.1 0 x h
    omega

private theorem stageTest_le_succ (e s x : ℕ) :
    EffectiveEnumerations.stageTest e s x ≤ EffectiveEnumerations.stageTest e (s + 1) x := by
  rcases (EffectiveEnumerations.stage_test_spec e s x).1 with h | h
  · rw [h]
    exact Nat.zero_le _
  · have hx := (EffectiveEnumerations.stage_test_spec e s x).2.mp h
    have hy := EffectiveEnumerations.stage_monotone e (Nat.le_succ s) hx
    have ht := (EffectiveEnumerations.stage_test_spec e (s + 1) x).2.mpr hy
    rw [h, ht]

theorem stage_difference_data (e f : ℕ) :
    Computable₂ (stageDifference e f) ∧ Binary (stageDifference e f) ∧
      Converges (stageDifference e f)
        (EffectiveEnumerations.indexSet e \ EffectiveEnumerations.indexSet f) ∧
      StartsZero (stageDifference e f) ∧ AtMostChanges (stageDifference e f) 2 := by
  classical
  have hbe := (EffectiveEnumerations.canonical_test_data e).2.1
  have hbf := (EffectiveEnumerations.canonical_test_data f).2.1
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact Primrec.nat_mul.to_comp.comp (EffectiveEnumerations.canonical_test_data e).1
      (Primrec.nat_sub.to_comp.comp (Computable.const 1)
        (EffectiveEnumerations.canonical_test_data f).1)
  · intro s x
    rcases hbe s x with he | he <;> rcases hbf s x with hf | hf <;>
      simp [stageDifference, differenceGuess, he, hf]
  · intro x
    obtain ⟨t, ht⟩ := canonical_stage_converges e x
    obtain ⟨u, hu⟩ := canonical_stage_converges f x
    refine ⟨max t u, fun s hs => ?_⟩
    rw [stageDifference, differenceGuess, ht s (by omega), hu s (by omega)]
    simp only [indicator, SDiff.sdiff, Set.diff, Set.ofPred, Membership.mem, Set.Mem]
    by_cases he : EffectiveEnumerations.indexSet e x <;>
      by_cases hf : EffectiveEnumerations.indexSet f x <;> simp [he, hf]
  · intro x
    simp [stageDifference, differenceGuess, stageTest_zero]
  · intro s x
    have hc := difference_count_bound _ _ hbe hbf (stageTest_le_succ e) (stageTest_le_succ f) s x
    change changeCount (differenceGuess (EffectiveEnumerations.stageTest e)
      (EffectiveEnumerations.stageTest f)) s x ≤ 2
    rcases hbe s x with he | he <;> rcases hbf s x with hf | hf <;>
      rw [he, hf] at hc <;> omega

theorem event_sets_enumerable (a : Approximation) (ha : Computable₂ a) :
    REPred (positiveEvents a) ∧ REPred (cancellationEvents a) ∧
      cancellationEvents a ⊆ positiveEvents a := by
  classical
  have hpos : ComputablePred (fun p : ℕ × ℕ => a p.2 p.1 = 1) :=
    (Primrec.eq.decide.to_comp.comp (ha.comp Computable.snd Computable.fst)
      (Computable.const 1)).computablePred
  have hp : REPred (positiveEvents a) :=
    (enumerable_iff_decidable_certificate _).mpr ⟨fun x r => a r x = 1, hpos, fun _ => Iff.rfl⟩
  have hr := (Computable.fst.comp Computable.unpair).comp (Computable.snd : Computable (@Prod.snd ℕ ℕ))
  have ht := (Computable.snd.comp Computable.unpair).comp (Computable.snd : Computable (@Prod.snd ℕ ℕ))
  have hlt : ComputablePred (fun p : ℕ × ℕ => p.2.unpair.1 < p.2.unpair.2) :=
    (Primrec.nat_lt.decide.to_comp.comp hr ht).computablePred
  have hone : ComputablePred (fun p : ℕ × ℕ => a p.2.unpair.1 p.1 = 1) :=
    (Primrec.eq.decide.to_comp.comp (ha.comp hr Computable.fst) (Computable.const 1)).computablePred
  have hzero : ComputablePred (fun p : ℕ × ℕ => a p.2.unpair.2 p.1 = 0) :=
    (Primrec.eq.decide.to_comp.comp (ha.comp ht Computable.fst) (Computable.const 0)).computablePred
  have htest : ComputablePred (fun p : ℕ × ℕ =>
      p.2.unpair.1 < p.2.unpair.2 ∧ a p.2.unpair.1 p.1 = 1 ∧ a p.2.unpair.2 p.1 = 0) := by
    apply Computable.computablePred
    exact (Primrec.and.to_comp.comp hlt.decide
      (Primrec.and.to_comp.comp hone.decide hzero.decide)).of_eq
      (fun _ => by simp only [Bool.decide_and])
  have hn : REPred (cancellationEvents a) := by
    apply (enumerable_iff_decidable_certificate _).mpr
    refine ⟨fun x w => w.unpair.1 < w.unpair.2 ∧
      a w.unpair.1 x = 1 ∧ a w.unpair.2 x = 0, htest, ?_⟩
    intro x
    constructor
    · rintro ⟨r, t, hrt, hr, ht⟩
      exact ⟨Nat.pair r t, by simpa using And.intro hrt (And.intro hr ht)⟩
    · rintro ⟨w, hw⟩
      exact ⟨w.unpair.1, w.unpair.2, hw⟩
  exact ⟨hp, hn, fun _ ⟨r, _, _, hr, _⟩ => ⟨r, hr⟩⟩

theorem two_change_reconstruction (a : Approximation) (A : Set ℕ)
    (hb : Binary a) (hc : Converges a A) (hz : StartsZero a) (hn : AtMostChanges a 2) :
    A = positiveEvents a \ cancellationEvents a := by
  classical
  ext x
  constructor
  · intro hx
    change A x at hx
    obtain ⟨u, hu⟩ := hc x
    have hfinal (q : ℕ) (hq : u ≤ q) : a q x = 1 := by
      simpa [indicator, hx] using hu q hq
    refine ⟨⟨u, hfinal u le_rfl⟩, ?_⟩
    rintro ⟨r, t, hrt, hr, ht⟩
    let q := max t u
    have hq := hfinal q (le_max_right _ _)
    have h0r := changeCount_strict_of_ne a x (Nat.zero_le r)
      (show a 0 x ≠ a r x by rw [hz x, hr]; decide)
    have hrt' := changeCount_strict_of_ne a x hrt.le
      (show a r x ≠ a t x by rw [hr, ht]; decide)
    have htq := changeCount_strict_of_ne a x (le_max_left t u)
      (show a t x ≠ a q x by rw [ht, hq]; decide)
    have hbound := hn q x
    dsimp [q] at hbound
    simp only [changeCount] at h0r
    omega
  · rintro ⟨⟨r, hr⟩, hn⟩
    obtain ⟨t, ht⟩ := hc x
    let q := max (r + 1) t
    have hrq : r < q := by dsimp [q]; omega
    have hqone : a q x = 1 := (hb q x).resolve_left (fun hq => hn ⟨r, q, hrq, hr, hq⟩)
    have hq := ht q (le_max_right _ _)
    by_contra hx
    change ¬ A x at hx
    rw [indicator, ite_eq_right hx, hqone] at hq
    omega

theorem difference_iff_two_change (A : Set ℕ) :
    IsDifferenceEnumerable A ↔ TwoChangeApproximation A := by
  constructor
  · rintro ⟨U, V, hU, hV, rfl⟩
    obtain ⟨e, he⟩ := (enumerable_iff_index U).mp hU
    obtain ⟨f, hf⟩ := (enumerable_iff_index V).mp hV
    have hU' : U = EffectiveEnumerations.indexSet e := Set.ext he
    have hV' : V = EffectiveEnumerations.indexSet f := Set.ext hf
    rw [hU', hV']
    exact ⟨stageDifference e f, stage_difference_data e f⟩
  · rintro ⟨a, ha, hb, hc, hz, hn⟩
    obtain ⟨hp, hn', _⟩ := event_sets_enumerable a ha
    exact ⟨positiveEvents a, cancellationEvents a, hp, hn', two_change_reconstruction a A hb hc hz hn⟩

theorem difference_limit_computable (A : Set ℕ) (hA : IsDifferenceEnumerable A) :
    LimitComputable A := by
  obtain ⟨a, ha, hb, hc, _⟩ := (difference_iff_two_change A).mp hA
  exact ⟨a, ha, hb, hc⟩

theorem canonical_one_change (e : ℕ) :
    StartsZero (EffectiveEnumerations.stageTest e) ∧
      (∀ s x, changeCount (EffectiveEnumerations.stageTest e) s x =
        EffectiveEnumerations.stageTest e s x) ∧
      AtMostChanges (EffectiveEnumerations.stageTest e) 1 := by
  have heq : ∀ s x, changeCount (EffectiveEnumerations.stageTest e) s x =
      EffectiveEnumerations.stageTest e s x := by
    intro s x
    induction s with
    | zero => simp [changeCount, stageTest_zero]
    | succ s ih =>
        rw [changeCount, ih]
        have hm := stageTest_le_succ e s x
        rcases (EffectiveEnumerations.stage_test_spec e s x).1 with hs | hs <;>
          rcases (EffectiveEnumerations.stage_test_spec e (s + 1) x).1 with ht | ht <;>
          simp [hs, ht] at hm ⊢
  refine ⟨stageTest_zero e, heq, ?_⟩
  intro s x
  rw [heq]
  rcases (EffectiveEnumerations.stage_test_spec e s x).1 with h | h <;> simp [h]

theorem one_change_reconstruction (a : Approximation) (A : Set ℕ)
    (hc : Converges a A) (hz : StartsZero a) (hn : AtMostChanges a 1) :
    A = positiveEvents a := by
  classical
  ext x
  constructor
  · intro hx
    change A x at hx
    obtain ⟨t, ht⟩ := hc x
    exact ⟨t, by simpa [indicator, hx] using ht t le_rfl⟩
  · rintro ⟨r, hr⟩
    by_contra hx
    change ¬ A x at hx
    obtain ⟨t, ht⟩ := hc x
    let q := max r t
    have hq : a q x = 0 := by simpa [indicator, hx] using ht q (le_max_right _ _)
    have h0r := changeCount_strict_of_ne a x (Nat.zero_le r)
      (show a 0 x ≠ a r x by rw [hz x, hr]; decide)
    have hrq := changeCount_strict_of_ne a x (le_max_left r t)
      (show a r x ≠ a q x by rw [hr, hq]; decide)
    have hbound := hn q x
    dsimp [q] at hbound
    simp only [changeCount] at h0r
    omega

theorem enumerable_iff_one_change (A : Set ℕ) :
    REPred A ↔ ∃ a : Approximation, Computable₂ a ∧ Binary a ∧ Converges a A ∧
      StartsZero a ∧ AtMostChanges a 1 := by
  constructor
  · intro hA
    obtain ⟨e, he⟩ := (enumerable_iff_index A).mp hA
    have hA' : A = EffectiveEnumerations.indexSet e := Set.ext he
    rw [hA']
    exact ⟨EffectiveEnumerations.stageTest e, (EffectiveEnumerations.canonical_test_data e).1,
      (EffectiveEnumerations.canonical_test_data e).2.1, canonical_stage_converges e,
      (canonical_one_change e).1, (canonical_one_change e).2.2⟩
  · rintro ⟨a, ha, _, hc, hz, hn⟩
    rw [one_change_reconstruction a A hc hz hn]
    exact (event_sets_enumerable a ha).1

theorem enumerable_difference (A : Set ℕ) (hA : REPred A) : IsDifferenceEnumerable A := by
  have hempty : REPred (∅ : Set ℕ) := by
    change REPred (fun _ : ℕ => False)
    apply ComputablePred.to_re
    exact Computable.computablePred (Computable.const false)
  exact ⟨A, ∅, hA, hempty, by simp⟩

theorem coenumerable_difference (A : Set ℕ) (hA : REPred Aᶜ) : IsDifferenceEnumerable A := by
  have hfull : REPred (Set.univ : Set ℕ) := by
    change REPred (fun _ : ℕ => True)
    apply ComputablePred.to_re
    exact Computable.computablePred (Computable.const true)
  exact ⟨Set.univ, Aᶜ, hfull, hA, by simp⟩

theorem decidable_difference (A : Set ℕ) (hA : ComputablePred A) : IsDifferenceEnumerable A := by
  exact enumerable_difference A hA.to_re

theorem difference_inter (A B : Set ℕ)
    (hA : IsDifferenceEnumerable A) (hB : IsDifferenceEnumerable B) :
    IsDifferenceEnumerable (A ∩ B) := by
  obtain ⟨U, V, hU, hV, rfl⟩ := hA
  obtain ⟨R, S, hR, hS, rfl⟩ := hB
  refine ⟨U ∩ R, V ∪ S, enumerable_inter hU hR, enumerable_union hV hS, ?_⟩
  ext x
  simp only [Set.mem_inter_iff, Set.mem_sdiff, Set.mem_union]
  tauto

theorem difference_preimage (A : Set ℕ) (f : ℕ → ℕ)
    (hA : IsDifferenceEnumerable A) (hf : Computable f) :
    IsDifferenceEnumerable (f ⁻¹' A) := by
  obtain ⟨U, V, hU, hV, rfl⟩ := hA
  exact ⟨f ⁻¹' U, f ⁻¹' V, UniversalComputation.enumerable_preimage (A := U) (g := f) hU hf,
    UniversalComputation.enumerable_preimage (A := V) (g := f) hV hf, rfl⟩

end Lemmatheca.ComputabilityTheory.DifferenceEnumerable
