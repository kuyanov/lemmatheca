import Lemmatheca.ComputablyBoundedChanges.Basic
import Lemmatheca.FiniteDifferenceNormalForms.Thresholds
import Lemmatheca.TuringJump.Recoding

/-! One ordinary search and one freezing map for all revision thresholds. -/
namespace Lemmatheca.ComputabilityTheory.BoundedChangesStrongReductions

open UniversalComputation LimitComputability DifferenceEnumerable ComputablyBoundedChanges

noncomputable section

set_option backward.isDefEq.respectTransparency false

def changeThresholds (a : Approximation) : Set ℕ :=
  {w | ∃ s, w.unpair.2 < changeCount a s w.unpair.1}

def thresholdSearch (a : Approximation) (w : ℕ) : Part ℕ :=
  (Nat.rfind fun s => Part.some (decide (w.unpair.2 < changeCount a s w.unpair.1))).map
    (fun _ => 0)

theorem threshold_search_recursive (a : Approximation) (hc : Computable₂ a) :
    Nat.Partrec (thresholdSearch a) := by
  have hcount : Computable (fun p : ℕ × ℕ => changeCount a p.2 p.1.unpair.1) :=
    (changeCount_computable a hc).comp Computable.snd
      (Computable.fst.comp (Computable.unpair.comp Computable.fst))
  have hp : Computable₂ (fun w s : ℕ => decide (w.unpair.2 < changeCount a s w.unpair.1)) :=
    Primrec.nat_lt.decide.to_comp.comp
      (Computable.snd.comp (Computable.unpair.comp Computable.fst)) hcount
  exact Partrec.nat_iff.mp ((Partrec.rfind hp.partrec₂).map (Computable.const 0).to₂)

def thresholdCode (a : Approximation) (hc : Computable₂ a) : Nat.Partrec.Code :=
  Classical.choose (Nat.Partrec.Code.exists_code.mp (threshold_search_recursive a hc))

def thresholdIndex (a : Approximation) (hc : Computable₂ a) : ℕ :=
  Encodable.encode (thresholdCode a hc)

def thresholdQuery (a : Approximation) (hc : Computable₂ a) (x k : ℕ) : ℕ :=
  TuringJump.ordinaryFreeze (thresholdIndex a hc) (Nat.pair x k)

theorem threshold_search_domain (a : Approximation) (w : ℕ) :
    (thresholdSearch a w).Dom ↔ w ∈ changeThresholds a := by
  change (Nat.rfind fun s => Part.some
    (decide (w.unpair.2 < changeCount a s w.unpair.1))).Dom ↔
      ∃ s, w.unpair.2 < changeCount a s w.unpair.1
  rw [Nat.rfind_dom]
  simp

theorem threshold_code_eval (a : Approximation) (hc : Computable₂ a) (w : ℕ) :
    phi (thresholdIndex a hc) w = thresholdSearch a w := by
  unfold phi thresholdIndex
  rw [Denumerable.ofNat_encode]
  exact congrFun (Classical.choose_spec
    (Nat.Partrec.Code.exists_code.mp (threshold_search_recursive a hc))) w

theorem threshold_zero_output (a : Approximation) (hc : Computable₂ a) (x k : ℕ) :
    phi (thresholdIndex a hc) (Nat.pair x k) = Part.some 0 ↔
      Nat.pair x k ∈ changeThresholds a := by
  rw [threshold_code_eval, Part.eq_some_iff]
  constructor
  · intro hy
    exact (threshold_search_domain a _).mp hy.1
  · intro hx
    exact ⟨(threshold_search_domain a _).mpr hx, rfl⟩

theorem thresholds_enumerable (a : Approximation) (hc : Computable₂ a) :
    REPred (changeThresholds a) := by
  apply (enumerable_iff_index (changeThresholds a)).mpr
  refine ⟨thresholdIndex a hc, fun w => ?_⟩
  rw [threshold_code_eval]
  exact (threshold_search_domain a w).symm

theorem threshold_query_primitive (a : Approximation) (hc : Computable₂ a) :
    Primrec₂ (thresholdQuery a hc) := by
  exact (TuringJump.ordinary_freeze_primitive.comp
    (Primrec.const (thresholdIndex a hc)) Primrec₂.natPair).to₂

theorem threshold_query_eval (a : Approximation) (hc : Computable₂ a) (x k y : ℕ) :
    phi (thresholdQuery a hc x k) y = phi (thresholdIndex a hc) (Nat.pair x k) := by
  exact TuringJump.ordinary_freeze_eval (thresholdIndex a hc) (Nat.pair x k) y

theorem threshold_query_halting (a : Approximation) (hc : Computable₂ a) (x k : ℕ) :
    thresholdQuery a hc x k ∈ haltingDiagonal ↔ Nat.pair x k ∈ changeThresholds a := by
  change (phi (thresholdQuery a hc x k) (thresholdQuery a hc x k)).Dom ↔ _
  rw [threshold_query_eval, threshold_code_eval, threshold_search_domain]

theorem thresholds_above_bound (a : Approximation) (b : ℕ → ℕ)
    (hn : BoundedBy a b) (x k : ℕ) (hk : b x ≤ k) :
    Nat.pair x k ∉ changeThresholds a := by
  simp only [changeThresholds, Set.mem_ofPred_eq, Nat.unpair_pair]
  rintro ⟨s, hs⟩
  have hbound := hn s x
  omega

theorem counter_max_at (a : Approximation) (b : ℕ → ℕ) (hn : BoundedBy a b) (x : ℕ) :
    ∃ m, m ≤ b x ∧ ∃ t, changeCount a t x = m ∧
      (∀ s, changeCount a s x ≤ m) ∧ ∀ s, t ≤ s → changeCount a s x = m := by
  classical
  let P : ℕ → Prop := fun m => ∃ s, changeCount a s x = m
  have hp : P 0 := ⟨0, rfl⟩
  let m := Nat.findGreatest P (b x)
  obtain ⟨t, ht⟩ := Nat.findGreatest_spec (P := P) (Nat.zero_le (b x)) hp
  change changeCount a t x = m at ht
  have hmax : ∀ s, changeCount a s x ≤ m := fun s =>
    Nat.le_findGreatest (P := P) (hn s x) ⟨s, rfl⟩
  refine ⟨m, Nat.findGreatest_le _, t, ht, hmax, fun s hs => ?_⟩
  apply Nat.le_antisymm (hmax s)
  rw [← ht]
  exact changeCount_monotone a x hs

theorem threshold_sum (a : Approximation) (hc : Computable₂ a) (b : ℕ → ℕ)
    (x m : ℕ) (hm : ∃ t, changeCount a t x = m)
    (hmax : ∀ s, changeCount a s x ≤ m) (hb : m ≤ b x) :
    (Finset.range (b x)).sum
      (fun k => indicator haltingDiagonal (thresholdQuery a hc x k)) = m := by
  classical
  have hmem (k : ℕ) : thresholdQuery a hc x k ∈ haltingDiagonal ↔ k < m := by
    rw [threshold_query_halting]
    simp only [changeThresholds, Set.mem_ofPred_eq, Nat.unpair_pair]
    constructor
    · rintro ⟨s, hs⟩
      exact lt_of_lt_of_le hs (hmax s)
    · intro hk
      obtain ⟨t, ht⟩ := hm
      exact ⟨t, by simpa [ht] using hk⟩
  have hfilter : (Finset.range (b x)).filter (fun k => k < m) = Finset.range m := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  calc
    _ = (Finset.range (b x)).sum (fun k => if k < m then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro k _
      by_cases hk : k < m
      · have hh : haltingDiagonal (thresholdQuery a hc x k) := (hmem k).mpr hk
        simp [indicator, hh, hk]
      · have hh : ¬ haltingDiagonal (thresholdQuery a hc x k) :=
          fun h => hk ((hmem k).mp h)
        simp [indicator, hh, hk]
    _ = ((Finset.range (b x)).filter (fun k => k < m)).card := by simp
    _ = m := by rw [hfilter]; simp

theorem final_parity (a : Approximation) (hc : Computable₂ a) (A : Set ℕ) (b : ℕ → ℕ)
    (hb : Binary a) (hz : StartsZero a) (hl : Converges a A) (hn : BoundedBy a b) (x : ℕ) :
    indicator A x = ((Finset.range (b x)).sum
      (fun k => indicator haltingDiagonal (thresholdQuery a hc x k))) % 2 := by
  obtain ⟨m, hm, t, ht, hmax, hstable⟩ := counter_max_at a b hn x
  rw [threshold_sum a hc b x m ⟨t, ht⟩ hmax hm]
  obtain ⟨u, hu⟩ := hl x
  have hbit := FiniteDifferenceNormalForms.count_parity a hb hz (max t u) x
  rw [hstable _ (le_max_left _ _), hu _ (le_max_right _ _)] at hbit
  exact hbit

end
end Lemmatheca.ComputabilityTheory.BoundedChangesStrongReductions
