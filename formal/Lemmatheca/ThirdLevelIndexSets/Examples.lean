import Lemmatheca.ThirdLevelIndexSets.Classification
import Lemmatheca.IndexSetCompleteness.Examples

/-! Explicit answers for complement sizes, repeated updates and unbounded event labels. -/
namespace Lemmatheca.Entry.ThirdLevelIndexSets
open Lemmatheca.ComputabilityTheory
open ThirdLevelIndexSets EffectiveEnumerations UniversalComputation

/-- Actual ordinary empty/whole-domain indices exist; the middle example is the earlier parity index. -/
theorem domain_examples :
    ∃ eEmpty eWhole : ℕ,
      indexSet eEmpty = ∅ ∧ indexSet eWhole = Set.univ ∧
      eEmpty ∈ CoinfiniteIndices ∧ eEmpty ∉ CofiniteIndices ∧
      (indexSet eEmpty).Finite ∧
      Lemmatheca.Entry.IndexSetCompleteness.evenIndex ∈ CoinfiniteIndices ∧
      Lemmatheca.Entry.IndexSetCompleteness.evenIndex ∉ CofiniteIndices ∧
      (indexSet Lemmatheca.Entry.IndexSetCompleteness.evenIndex).Infinite ∧
      eWhole ∈ CofiniteIndices ∧ eWhole ∉ CoinfiniteIndices ∧
      (indexSet eWhole).Infinite := by
  classical
  obtain ⟨eEmpty,he⟩ := phi_complete Nat.Partrec.none
  let eWhole := Encodable.encode Nat.Partrec.Code.zero
  have hEmpty : indexSet eEmpty = ∅ := by
    ext z
    simp [indexSet,he]
  have hWhole : indexSet eWhole = Set.univ := by
    ext z
    simp [indexSet,eWhole,phi,Denumerable.ofNat_encode,Nat.Partrec.Code.eval]
    change (Part.some (0 : ℕ)).Dom
    trivial
  have hEven : ((indexSet Lemmatheca.Entry.IndexSetCompleteness.evenIndex)ᶜ).Infinite := by
    intro hf
    obtain ⟨a,ha⟩ := hf.bddAbove
    have hm : 2*(a+1)+1 ∉ indexSet Lemmatheca.Entry.IndexSetCompleteness.evenIndex := by
      rw [Lemmatheca.Entry.IndexSetCompleteness.evenIndex_domain]
      omega
    have := ha hm
    omega
  refine ⟨eEmpty,eWhole,hEmpty,hWhole,?_,?_,?_,hEven,hEven,
    Lemmatheca.Entry.IndexSetCompleteness.evenIndex_facts.1,?_,?_,?_⟩
  · change ((indexSet eEmpty)ᶜ).Infinite
    rw [hEmpty]
    simpa using (Set.infinite_univ : (Set.univ : Set ℕ).Infinite)
  · change ¬ ((indexSet eEmpty)ᶜ).Finite
    rw [hEmpty]
    simpa using (Set.infinite_univ : (Set.univ : Set ℕ).Infinite)
  · rw [hEmpty]
    exact Set.finite_empty
  · change ((indexSet eWhole)ᶜ).Finite
    rw [hWhole]
    simp
  · change ¬ ((indexSet eWhole)ᶜ).Infinite
    rw [hWhole]
    simp
  · rw [hWhole]
    exact Set.infinite_univ

theorem two_current_bumps :
    (bump (bump [1,4] 1) 1).toFinset = {1,2,3,4} ∧
      (marker [1,4] 1 :: marker [1,4] 1 :: [1,4]).toFinset = {1,2,4} := by
  decide

def onceEvent (_x s c : ℕ) : Bool := decide (c < s)
def onceLabel (c : ℕ) : ℕ := c

theorem onceEvent_primitive :
    Primrec (fun p : (ℕ × ℕ) × ℕ => onceEvent p.1.1 p.1.2 p.2) := by
  exact (Primrec.nat_lt.comp Primrec.snd (Primrec.snd.comp Primrec.fst)).decide

theorem onceEvent_bound (x s c : ℕ) (h : onceEvent x s c = true) : c < s := by
  simpa only [onceEvent,decide_eq_true_eq] using h

theorem onceEvent_increasing (x s c : ℕ) (h : onceEvent x s c = true) :
    onceEvent x (s+1) c = true := by
  have := onceEvent_bound x s c h
  simp only [onceEvent,decide_eq_true_eq]
  omega

def onceSchedule : Schedule where
  event := onceEvent
  label := onceLabel
  event_primitive := onceEvent_primitive
  label_primitive := Primrec.id
  bounded := onceEvent_bound
  increasing := onceEvent_increasing

theorem once_fresh (x s c : ℕ) : fresh onceSchedule x s c = true ↔ c = s := by
  simp only [fresh,onceSchedule,onceEvent,Bool.and_eq_true,decide_eq_true_eq,
    Bool.not_eq_true',decide_eq_false_iff_not]
  omega

private theorem count_odds_below_even (s : ℕ) :
    ((List.range (2*s)).filter (fun z => decide (z % 2 = 1))).length = s := by
  induction s with
  | zero => simp
  | succ s ih =>
    have he : 2*(s+1) = 2*s+1+1 := by omega
    rw [he, List.range_succ, List.range_succ]
    simp [List.filter_append, Nat.add_mod, ih]

private theorem even_prefix_missing (B : List ℕ) (s : ℕ)
    (hB : ∀ z, z ∈ B ↔ ∃ j < s, z = 2*j) :
    (missingBelow B (2*s)).length = s := by
  have he : missingBelow B (2*s) =
      (List.range (2*s)).filter (fun z => decide (z % 2 = 1)) := by
    apply List.filter_congr
    intro z hz
    have hz' : z < 2*s := List.mem_range.mp hz
    have hm : z ∈ B ↔ z % 2 = 0 := by
      rw [hB]
      constructor
      · rintro ⟨j,hj,rfl⟩
        omega
      · intro he
        exact ⟨z/2,by omega,by omega⟩
    by_cases hb : z ∈ B
    · have hmod := hm.mp hb
      simp [hb,hmod]
    · have hmod : z % 2 = 1 := by
        have hz0 : z % 2 ≠ 0 := fun h0 => hb (hm.mpr h0)
        have := Nat.mod_lt z (by decide : 0 < 2)
        omega
      simp [hb,hmod]
  rw [he]
  exact count_odds_below_even s

private theorem once_scan_prefix (x s : ℕ) (B : List ℕ) (c : ℕ) (hc : c ≤ s) :
    scan onceSchedule x s B c = B := by
  induction c with
  | zero => rfl
  | succ c ih =>
    have hn : fresh onceSchedule x s c = false := by
      apply Bool.eq_false_iff.mpr
      intro hf
      have := (once_fresh x s c).mp hf
      omega
    simpa only [scan,hn,Bool.false_eq_true,ite_false] using ih (by omega)

theorem once_stages (x s z : ℕ) :
    z ∈ stages onceSchedule x s ↔ ∃ j < s, z = 2*j := by
  induction s generalizing z with
  | zero => simp [stages]
  | succ s ih =>
    have hm : marker (stages onceSchedule x s) s = 2*s := by
      apply (marker_unique _ _ _).mpr
      refine ⟨?_,even_prefix_missing _ s ih⟩
      intro h
      obtain ⟨j,hj,he⟩ := (ih _).mp h
      omega
    have hf : fresh onceSchedule x s s = true := (once_fresh x s s).mpr rfl
    have he : stages onceSchedule x (s+1) = bump (stages onceSchedule x s) s := by
      change scan onceSchedule x s (stages onceSchedule x s) (s+1) = _
      rw [scan]
      simp only [hf,ite_true,once_scan_prefix x s _ s le_rfl]
      rfl
    rw [he,bump,hm,List.mem_cons,ih]
    constructor
    · rintro (hz | ⟨j,hj,hz⟩)
      · exact ⟨s,by omega,hz⟩
      · exact ⟨j,by omega,hz⟩
    · rintro ⟨j,hj,hz⟩
      by_cases hs : j < s
      · exact Or.inr ⟨j,hs,hz⟩
      · have : j = s := by omega
        exact Or.inl (this ▸ hz)

theorem once_output (x : ℕ) : output onceSchedule x = {z | z % 2 = 0} := by
  ext z
  change (∃ s,z ∈ stages onceSchedule x s) ↔ z % 2 = 0
  simp only [once_stages]
  constructor
  · rintro ⟨s,j,hj,rfl⟩
    omega
  · intro hz
    exact ⟨z/2+1,z/2,by omega,by omega⟩

theorem once_events (x : ℕ) : (events onceSchedule x).Infinite ∧
    (∀ n, (lowEvents onceSchedule x n).Finite) ∧
      ((output onceSchedule x)ᶜ).Infinite := by
  have he : events onceSchedule x = Set.univ := by
    ext c
    constructor
    · exact fun _ => Set.mem_univ _
    · intro _
      exact ⟨c+1,by simp [onceSchedule,onceEvent]⟩
  have hl (n : ℕ) : lowEvents onceSchedule x n = Set.Iic n := by
    ext c
    change (c ∈ events onceSchedule x ∧ c ≤ n) ↔ c ≤ n
    rw [he]
    simp
  have hf : ∀ n, (lowEvents onceSchedule x n).Finite := by
    intro n
    rw [hl n]
    exact Set.finite_Iic n
  refine ⟨?_,hf,output_coinfinite_of_finite_low onceSchedule x hf⟩
  rw [he]
  exact Set.infinite_univ

end Lemmatheca.Entry.ThirdLevelIndexSets
