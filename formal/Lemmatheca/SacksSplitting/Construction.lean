import Lemmatheca.FriedbergSplitting.Scheduler
import Lemmatheca.FiniteInjuryAndPostsProblem.Effectivity
import Lemmatheca.LowSimpleSets.Lowness

/-! The specified monotone-record Sacks splitting algorithm. -/
namespace Lemmatheca.ComputabilityTheory.SacksSplitting

open PostsTheorem PrimitiveRecursion UniversalComputation LimitComputability

noncomputable section
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

abbrev State := ℕ × ℕ × ℕ × ℕ

def sideCode (z : State) (i : ℕ) : ℕ := if i % 2 = 0 then z.1 else z.2.1

def lengthRecord (z : State) (q : ℕ) : ℕ := FiniteSequenceCoding.entry z.2.2.1 q

def restraintRecord (z : State) (q : ℕ) : ℕ := FiniteSequenceCoding.entry z.2.2.2 q

def leastObservation (s : ℕ) (z : State) (q : ℕ) : ℕ :=
  let k := boundedSearch (fun p : State × ℕ => fun k =>
    0 < finiteValue (sideCode p.1 (p.2 % 2)) k (p.2 / 2) (p.2 / 2)) (z, q) (s + 2)
  if k < s + 2 then k else 0

def Expands (h : Approximation) (s : ℕ) (z : State) (q : ℕ) : Prop :=
  ∀ x < lengthRecord z q + 1,
    finiteValue (sideCode z (q % 2)) (s + 1) (q / 2) x = h s x + 1

def nextLength (h : Approximation) (s : ℕ) (z : State) (q : ℕ) : ℕ :=
  if q ≤ s then lengthRecord z q + if Expands h s z q then 1 else 0 else 0

def nextRestraint (h : Approximation) (s : ℕ) (z : State) (q : ℕ) : ℕ :=
  if q ≤ s then max (restraintRecord z q)
    (max (leastObservation s z q) (if Expands h s z q then s + 1 else 0)) else 0

def priority (a : ℕ) (h : Approximation) (s : ℕ) (z : State) : ℕ :=
  boundedSearch (fun p : ℕ × (ℕ × State) => fun q =>
    FriedbergSplitting.arrival p.1 p.2.1 < nextRestraint h p.2.1 p.2.2 q)
    (a, s, z) (s + 1)

def chosenSide (a : ℕ) (h : Approximation) (s : ℕ) (z : State) : ℕ :=
  if priority a h s z < s + 1 then 1 - priority a h s z % 2 else 0

def nextSideCode (a : ℕ) (h : Approximation) (s : ℕ) (z : State) (i : ℕ) : ℕ :=
  FiniteInjury.tabulate (s + 1) (fun x =>
    if FriedbergSplitting.HasArrival a s ∧ chosenSide a h s z = i % 2 ∧
      x = FriedbergSplitting.arrival a s then 1 else beta (sideCode z i) x)

def next (a : ℕ) (h : Approximation) (s : ℕ) (z : State) : State :=
  (nextSideCode a h s z 0, nextSideCode a h s z 1,
    FiniteInjury.tabulate (s + 1) (nextLength h s z),
    FiniteInjury.tabulate (s + 1) (nextRestraint h s z))

def stage (a : ℕ) (h : Approximation) : ℕ → State
  | 0 => (0, 0, 0, 0)
  | s + 1 => next a h s (stage a h s)

def stageCode (a : ℕ) (h : Approximation) (s i : ℕ) : ℕ :=
  sideCode (stage a h s) i

def stageBit (a : ℕ) (h : Approximation) (s i x : ℕ) : ℕ :=
  beta (stageCode a h s i) x

def stageSet (a : ℕ) (h : Approximation) (s i : ℕ) : Set ℕ :=
  finiteOracle (stageCode a h s i)

def piece (a : ℕ) (h : Approximation) (i : ℕ) : Set ℕ :=
  {x | ∃ s, x ∈ stageSet a h s i}

def lengthAt (a : ℕ) (h : Approximation) (s q : ℕ) : ℕ :=
  lengthRecord (stage a h s) q

def restraintAt (a : ℕ) (h : Approximation) (s q : ℕ) : ℕ :=
  restraintRecord (stage a h s) q

def Expanded (a : ℕ) (h : Approximation) (q s : ℕ) : Prop :=
  q ≤ s ∧ Expands h s (stage a h s) q

def Computes (a : ℕ) (h : Approximation) (C : Set ℕ) (q : ℕ) : Prop :=
  ∀ x, OracleProgramNumberings.phi (piece a h (q % 2)) (q / 2) x =
    Part.some (indicator C x)

def Avoids (a : ℕ) (h : Approximation) (C : Set ℕ) (q : ℕ) : Prop :=
  ¬ Computes a h C q

def DiagonalPreserved (a : ℕ) (h : Approximation) (q : ℕ) : Prop :=
  ∃ T, ∀ s ≥ T,
    0 < finiteValue (stageCode a h s (q % 2)) (s + 1) (q / 2) (q / 2) →
      (OracleProgramNumberings.phi (piece a h (q % 2)) (q / 2) (q / 2)).Dom

theorem observation_data (s : ℕ) (z : State) (q : ℕ) :
    leastObservation s z q ≤ s + 1 ∧
      (0 < leastObservation s z q ↔
        ∃ k ≤ s + 1, 0 < finiteValue (sideCode z (q % 2)) k (q / 2) (q / 2)) ∧
      (0 < leastObservation s z q →
        0 < finiteValue (sideCode z (q % 2)) (leastObservation s z q) (q / 2) (q / 2) ∧
        ∀ k < leastObservation s z q,
          finiteValue (sideCode z (q % 2)) k (q / 2) (q / 2) = 0) := by
  let R := fun p : State × ℕ => fun k =>
    0 < finiteValue (sideCode p.1 (p.2 % 2)) k (p.2 / 2) (p.2 / 2)
  let k := boundedSearch R (z, q) (s + 2)
  have hb : k ≤ s + 2 := (boundedSearch_spec R (z, q) (s + 2)).1
  have hz : ¬ R (z, q) 0 := by
    dsimp [R]
    rw [finiteValue_outside _ 0 _ _ (Nat.zero_le _)]
    omega
  change (if k < s + 2 then k else 0) ≤ s + 1 ∧ _
  by_cases hk : k < s + 2
  · have hp := (boundedSearch_spec R (z, q) (s + 2)).2.1 hk
    have hpos : 0 < k := by
      by_contra hn
      have he : k = 0 := by omega
      exact hz (he ▸ hp.1)
    have he : leastObservation s z q = k := by simp [leastObservation, k, R, hk]
    rw [he]
    simp only [ite_eq_left hk]
    refine ⟨by omega, ⟨fun _ => ⟨k, by omega, hp.1⟩, fun _ => hpos⟩, ?_⟩
    intro _
    exact ⟨hp.1, fun j hj => by have := hp.2 j hj; dsimp [R] at this; omega⟩
  · have heq : k = s + 2 := by omega
    have hn := (boundedSearch_spec R (z, q) (s + 2)).2.2.mp heq
    have he : leastObservation s z q = 0 := by simp [leastObservation, k, R, hk]
    rw [he]
    simp only [ite_eq_right hk, Nat.zero_le, lt_self_iff_false, false_implies, and_true,
      true_and, false_iff]
    rintro ⟨j, hj, hv⟩
    exact hn j (by omega) hv

theorem priority_data (a : ℕ) (h : Approximation) (s : ℕ) (z : State) :
    chosenSide a h s z < 2 ∧ priority a h s z ≤ s + 1 ∧
      (priority a h s z < s + 1 →
        FriedbergSplitting.arrival a s < nextRestraint h s z (priority a h s z) ∧
        ∀ p < priority a h s z,
          nextRestraint h s z p ≤ FriedbergSplitting.arrival a s) ∧
      (priority a h s z = s + 1 ↔
        ∀ q < s + 1, nextRestraint h s z q ≤ FriedbergSplitting.arrival a s) := by
  have hs := boundedSearch_spec
    (fun p : ℕ × (ℕ × State) => fun q =>
      FriedbergSplitting.arrival p.1 p.2.1 < nextRestraint h p.2.1 p.2.2 q)
    (a, s, z) (s + 1)
  change priority a h s z ≤ s + 1 ∧
    (priority a h s z < s + 1 →
      FriedbergSplitting.arrival a s < nextRestraint h s z (priority a h s z) ∧
      ∀ p < priority a h s z, ¬ FriedbergSplitting.arrival a s < nextRestraint h s z p) ∧
    (priority a h s z = s + 1 ↔
      ∀ q < s + 1, ¬ FriedbergSplitting.arrival a s < nextRestraint h s z q) at hs
  refine ⟨?_, hs.1, ?_, ?_⟩
  · unfold chosenSide
    split_ifs <;> omega
  · intro hp
    have ht := hs.2.1 hp
    exact ⟨ht.1, fun p hlt => by have := ht.2 p hlt; omega⟩
  · exact ⟨fun he p hp => by have := hs.2.2.mp he p hp; omega,
      fun hn => hs.2.2.mpr (fun p hp => by have := hn p hp; omega)⟩

theorem record_update (a : ℕ) (h : Approximation) (s q : ℕ) :
    lengthAt a h (s + 1) q = nextLength h s (stage a h s) q ∧
      restraintAt a h (s + 1) q = nextRestraint h s (stage a h s) q := by
  change FiniteSequenceCoding.entry
      (FiniteInjury.tabulate (s + 1) (nextLength h s (stage a h s))) q = _ ∧
    FiniteSequenceCoding.entry
      (FiniteInjury.tabulate (s + 1) (nextRestraint h s (stage a h s))) q = _
  rw [FiniteInjury.tabulate_entry, FiniteInjury.tabulate_entry]
  by_cases hq : q < s + 1
  · simp [hq]
  · have hn : ¬ q ≤ s := by omega
    simp [hq, nextLength, nextRestraint, hn]

theorem sideCode_mod (z : State) (i : ℕ) : sideCode z (i % 2) = sideCode z i := by
  simp [sideCode]

private theorem state_lengths (a : ℕ) (h : Approximation) (s : ℕ) :
    (∀ i, FiniteSequenceCoding.length (stageCode a h s i) = s) ∧
      FiniteSequenceCoding.length (stage a h s).2.2.1 = s ∧
      FiniteSequenceCoding.length (stage a h s).2.2.2 = s := by
  cases s with
  | zero => simp [stageCode, sideCode, stage, FiniteSequenceCoding.length]
  | succ s =>
      refine ⟨?_, ?_, ?_⟩
      · intro i
        by_cases hi : i % 2 = 0 <;>
          simp [stageCode, sideCode, stage, next, nextSideCode, hi, FiniteInjury.tabulate_length]
      · simp [stage, next, FiniteInjury.tabulate_length]
      · simp [stage, next, FiniteInjury.tabulate_length]

private theorem bit_outside (a : ℕ) (h : Approximation) (s i x : ℕ) (hx : s ≤ x) :
    stageBit a h s i x = 0 := by
  unfold stageBit beta
  rw [FiniteSequenceCoding.entry_out_of_range _ _ (by rw [(state_lengths a h s).1 i]; exact hx)]

private theorem records_outside (a : ℕ) (h : Approximation) (s q : ℕ) (hq : s ≤ q) :
    lengthAt a h s q = 0 ∧ restraintAt a h s q = 0 := by
  exact ⟨FiniteSequenceCoding.entry_out_of_range _ _
      (by rw [(state_lengths a h s).2.1]; exact hq),
    FiniteSequenceCoding.entry_out_of_range _ _
      (by rw [(state_lengths a h s).2.2]; exact hq)⟩

private theorem beta_tabulate (n : ℕ) (f : ℕ → ℕ)
    (hf : ∀ j, f j = 0 ∨ f j = 1) (j : ℕ) :
    beta (FiniteInjury.tabulate n f) j = if j < n then f j else 0 := by
  unfold beta
  rw [FiniteInjury.tabulate_entry]
  by_cases hj : j < n
  · rcases hf j with h | h <;> simp [hj, h]
  · simp [hj]

private theorem next_side_code (a : ℕ) (h : Approximation) (s : ℕ) (z : State) (i : ℕ) :
    sideCode (next a h s z) i = nextSideCode a h s z i := by
  by_cases hi : i % 2 = 0
  · simp [sideCode, next, nextSideCode, hi]
  · have hi1 : i % 2 = 1 := by omega
    simp [sideCode, next, nextSideCode, hi1]

theorem stage_bit_succ (a : ℕ) (h : Approximation) (s i x : ℕ) :
    stageBit a h (s + 1) i x =
      if FriedbergSplitting.HasArrival a s ∧ chosenSide a h s (stage a h s) = i % 2 ∧
        x = FriedbergSplitting.arrival a s then 1 else stageBit a h s i x := by
  have hf : ∀ j, (if FriedbergSplitting.HasArrival a s ∧
      chosenSide a h s (stage a h s) = i % 2 ∧ j = FriedbergSplitting.arrival a s
      then 1 else beta (sideCode (stage a h s) i) j) = 0 ∨
    (if FriedbergSplitting.HasArrival a s ∧
      chosenSide a h s (stage a h s) = i % 2 ∧ j = FriedbergSplitting.arrival a s
      then 1 else beta (sideCode (stage a h s) i) j) = 1 := by
    intro j
    split_ifs <;> simp [beta_bits]
  have he := beta_tabulate (s + 1) _ hf x
  change beta (sideCode (next a h s (stage a h s)) i) x = _
  rw [next_side_code]
  change beta (FiniteInjury.tabulate (s + 1) _) x = _
  rw [he]
  by_cases hx : x < s + 1
  · simp [hx, stageBit, stageCode]
  · have ho := bit_outside a h s i x (by omega)
    have hn : ¬ (FriedbergSplitting.HasArrival a s ∧
        chosenSide a h s (stage a h s) = i % 2 ∧ x = FriedbergSplitting.arrival a s) := by
      rintro ⟨ha, _, hxa⟩
      have hb : FriedbergSplitting.arrival a s < s + 1 := ha
      omega
    simp [hx, hn, ho]

theorem stage_transition (a : ℕ) (h : Approximation) (s i x : ℕ) :
    x ∈ stageSet a h (s + 1) i ↔ x ∈ stageSet a h s i ∨
      FriedbergSplitting.HasArrival a s ∧
      chosenSide a h s (stage a h s) = i % 2 ∧ x = FriedbergSplitting.arrival a s := by
  change stageBit a h (s + 1) i x = 1 ↔ _
  rw [stage_bit_succ]
  by_cases hc : FriedbergSplitting.HasArrival a s ∧
      chosenSide a h s (stage a h s) = i % 2 ∧ x = FriedbergSplitting.arrival a s
  · simp [hc]
  · simp only [ite_eq_right hc]
    change stageBit a h s i x = 1 ↔ stageBit a h s i x = 1 ∨ _
    simp [hc]

private theorem records_bounded (a : ℕ) (h : Approximation) (s q : ℕ) :
    lengthAt a h s q ≤ s ∧ restraintAt a h s q ≤ s := by
  induction s with
  | zero => simp [lengthAt, restraintAt, stage, lengthRecord, restraintRecord, FiniteSequenceCoding.entry]
  | succ s ih =>
      rw [(record_update a h s q).1, (record_update a h s q).2]
      have hd := (observation_data s (stage a h s) q).1
      change lengthRecord (stage a h s) q ≤ s ∧ restraintRecord (stage a h s) q ≤ s at ih
      unfold nextLength nextRestraint
      split_ifs <;> simp_all <;> omega

private theorem side_bounds (a : ℕ) (h : Approximation) (s i : ℕ) :
    stageSet a h s i ⊆ Set.Iio s := by
  intro x hx
  change x < s
  by_contra hn
  have ho := bit_outside a h s i x (by omega)
  change stageBit a h s i x = 1 at hx
  omega

private theorem stage_partition (a : ℕ) (h : Approximation) (s : ℕ) :
    Disjoint (stageSet a h s 0) (stageSet a h s 1) ∧
      stageSet a h s 0 ∪ stageSet a h s 1 = FriedbergSplitting.processedSet a s := by
  induction s with
  | zero =>
      simp [stageSet, stageCode, sideCode, stage, finiteOracle, beta,
        FiniteSequenceCoding.entry, FriedbergSplitting.processedSet, FriedbergSplitting.processedList]
  | succ s ih =>
      have hf : FriedbergSplitting.HasArrival a s →
          FriedbergSplitting.arrival a s ∉ stageSet a h s 0 ∪ stageSet a h s 1 := by
        intro ha
        rw [ih.2]
        exact ((FriedbergSplitting.arrival_data a s).2.2.1 ha).2.1
      refine ⟨Set.disjoint_left.mpr ?_, ?_⟩
      · intro x hx0 hx1
        rcases (stage_transition a h s 0 x).mp hx0 with h0 | h0 <;>
          rcases (stage_transition a h s 1 x).mp hx1 with h1 | h1
        · exact Set.disjoint_left.mp ih.1 h0 h1
        · exact hf h1.1 (h1.2.2 ▸ (Or.inl h0))
        · exact hf h0.1 (h0.2.2 ▸ (Or.inr h1))
        · have hc0 := h0.2.1
          have hc1 := h1.2.1
          norm_num at hc0 hc1
          omega
      · ext x
        rw [Set.mem_union, stage_transition, stage_transition,
          FriedbergSplitting.scheduler_transition]
        have hp : x ∈ FriedbergSplitting.processedSet a s ↔
            x ∈ stageSet a h s 0 ∨ x ∈ stageSet a h s 1 := by rw [← ih.2]; rfl
        rw [hp]
        have hc := (priority_data a h s (stage a h s)).1
        have hd : chosenSide a h s (stage a h s) = 0 ∨
            chosenSide a h s (stage a h s) = 1 := by omega
        rcases hd with hd | hd <;> simp [hd] <;> tauto

theorem stage_invariants (a : ℕ) (h : Approximation) (s : ℕ) :
    Disjoint (stageSet a h s 0) (stageSet a h s 1) ∧
      stageSet a h s 0 ∪ stageSet a h s 1 = FriedbergSplitting.processedSet a s ∧
      (∀ i, stageSet a h s i ⊆ Set.Iio s) ∧
      (∀ q, lengthAt a h s q ≤ s ∧ restraintAt a h s q ≤ s) ∧
      (∀ q, s ≤ q → lengthAt a h s q = 0 ∧ restraintAt a h s q = 0) := by
  exact ⟨(stage_partition a h s).1, (stage_partition a h s).2,
    side_bounds a h s, records_bounded a h s, records_outside a h s⟩

theorem stage_monotone (a : ℕ) (h : Approximation) (i : ℕ) :
    Monotone (fun s => stageSet a h s i) := by
  apply monotone_nat_of_le_succ
  intro s x hx
  exact (stage_transition a h s i x).mpr (Or.inl hx)

theorem records_monotone (a : ℕ) (h : Approximation) (q : ℕ) :
    Monotone (fun s => lengthAt a h s q) ∧ Monotone (fun s => restraintAt a h s q) := by
  constructor
  · apply monotone_nat_of_le_succ
    intro s
    rw [(record_update a h s q).1]
    by_cases hq : q ≤ s
    · simp only [nextLength, ite_eq_left hq]
      change lengthAt a h s q ≤ lengthAt a h s q + _
      omega
    · rw [(records_outside a h s q (by omega)).1]
      exact Nat.zero_le _
  · apply monotone_nat_of_le_succ
    intro s
    rw [(record_update a h s q).2]
    by_cases hq : q ≤ s
    · simp only [nextRestraint, ite_eq_left hq]
      exact le_max_left _ _
    · rw [(records_outside a h s q (by omega)).2]
      exact Nat.zero_le _

end
end Lemmatheca.ComputabilityTheory.SacksSplitting
