import Lemmatheca.PostsTheorem.FiniteCertificates
import Lemmatheca.EffectiveEnumerations.Settling

/-! A completely specified finite-state priority enumeration. -/
namespace Lemmatheca.ComputabilityTheory.FiniteInjury

open PostsTheorem PrimitiveRecursion OracleComputation OracleProgramNumberings UniversalComputation

noncomputable section
attribute [local instance] Classical.propDecidable

abbrev State := ℕ × ℕ × ℕ × ℕ

def aCode (z : State) : ℕ := z.1
def bCode (z : State) : ℕ := z.2.1
def dCode (z : State) : ℕ := z.2.2.1
def rCode (z : State) : ℕ := z.2.2.2

def ValidState (s : ℕ) (z : State) : Prop :=
  FiniteSequenceCoding.length (aCode z) = s ∧
    FiniteSequenceCoding.length (bCode z) = s ∧
    FiniteSequenceCoding.length (dCode z) = s ∧
    FiniteSequenceCoding.length (rCode z) = s ∧
    ∀ j, (FiniteSequenceCoding.entry (aCode z) j = 0 ∨
        FiniteSequenceCoding.entry (aCode z) j = 1) ∧
      (FiniteSequenceCoding.entry (bCode z) j = 0 ∨
        FiniteSequenceCoding.entry (bCode z) j = 1) ∧
      (FiniteSequenceCoding.entry (dCode z) j = 0 ∨
        FiniteSequenceCoding.entry (dCode z) j = 1)

def packState (z : State) : ℕ :=
  Nat.pair (aCode z) (Nat.pair (bCode z) (Nat.pair (dCode z) (rCode z)))

def unpackState (w : ℕ) : State :=
  (w.unpair.1, w.unpair.2.unpair.1,
    w.unpair.2.unpair.2.unpair.1, w.unpair.2.unpair.2.unpair.2)

def tabulate (n : ℕ) (f : ℕ → ℕ) : ℕ :=
  FiniteSequenceCoding.code ((List.range n).map f)

def reservoir (i : ℕ) : Set ℕ := {x | x.unpair.1 = i}

def targetCode (z : State) (i : ℕ) : ℕ :=
  if i % 2 = 0 then aCode z else bCode z

def oracleCode (z : State) (i : ℕ) : ℕ :=
  if i % 2 = 0 then bCode z else aCode z

def flag (z : State) (i : ℕ) : ℕ := beta (dCode z) i
def restraint (z : State) (i : ℕ) : ℕ := FiniteSequenceCoding.entry (rCode z) i

def Eligible (s : ℕ) (z : State) (i x : ℕ) : Prop :=
  i ≤ s ∧ x ≤ s ∧ x ∈ reservoir i ∧ flag z i = 0 ∧
    beta (targetCode z i) x = 0 ∧
    (∀ j < i, restraint z j ≤ x) ∧
    finiteValue (oracleCode z i) (s + 1) (i / 2) x = 1

def witness (s : ℕ) (z : State) (i : ℕ) : ℕ :=
  boundedSearch (fun p : ℕ × State × ℕ => Eligible p.1 p.2.1 p.2.2)
    (s, z, i) (s + 1)

def priority (s : ℕ) (z : State) : ℕ :=
  boundedSearch (fun p : ℕ × State => fun i => witness p.1 p.2 i < p.1 + 1)
    (s, z) (s + 1)

def HasAction (s : ℕ) (z : State) : Prop := priority s z < s + 1

def chosenWitness (s : ℕ) (z : State) : ℕ := witness s z (priority s z)

def next (s : ℕ) (z : State) : State :=
  (tabulate (s + 1) (fun x =>
      if HasAction s z ∧ priority s z % 2 = 0 ∧ x = chosenWitness s z then 1
      else beta (aCode z) x),
    tabulate (s + 1) (fun x =>
      if HasAction s z ∧ priority s z % 2 ≠ 0 ∧ x = chosenWitness s z then 1
      else beta (bCode z) x),
    tabulate (s + 1) (fun j =>
      if HasAction s z then
        if j < priority s z then flag z j else if j = priority s z then 1 else 0
      else flag z j),
    tabulate (s + 1) (fun j =>
      if HasAction s z then
        if j < priority s z then restraint z j else if j = priority s z then s + 1 else 0
      else restraint z j))

def stage : ℕ → State
  | 0 => (0, 0, 0, 0)
  | s + 1 => next s (stage s)

def stateNumber (s : ℕ) : ℕ := packState (stage s)

def nextNumber (s w : ℕ) : ℕ := packState (next s (unpackState w))

def action (s : ℕ) : ℕ :=
  if HasAction s (stage s) then priority s (stage s) + 1 else 0

def Acts (i s : ℕ) : Prop := action s = i + 1
def witnessAt (s : ℕ) : ℕ := chosenWitness s (stage s)

def leftBit (s x : ℕ) : ℕ := beta (aCode (stage s)) x
def rightBit (s x : ℕ) : ℕ := beta (bCode (stage s)) x

def leftStage (s : ℕ) : Set ℕ := finiteOracle (aCode (stage s))
def rightStage (s : ℕ) : Set ℕ := finiteOracle (bCode (stage s))

def leftSet : Set ℕ := {x | ∃ s, x ∈ leftStage s}
def rightSet : Set ℕ := {x | ∃ s, x ∈ rightStage s}

def targetStage (i s : ℕ) : Set ℕ := if i % 2 = 0 then leftStage s else rightStage s
def oracleStage (i s : ℕ) : Set ℕ := if i % 2 = 0 then rightStage s else leftStage s
def targetSet (i : ℕ) : Set ℕ := if i % 2 = 0 then leftSet else rightSet
def oracleSet (i : ℕ) : Set ℕ := if i % 2 = 0 then rightSet else leftSet

def RequirementFor (A B : Set ℕ) (i : ℕ) : Prop :=
  ∃ x, OracleProgramNumberings.phi (if i % 2 = 0 then B else A) (i / 2) x ≠
    Part.some (indicator (if i % 2 = 0 then A else B) x)

def Requirement (i : ℕ) : Prop := RequirementFor leftSet rightSet i

theorem pack_state_inverse (z : State) : unpackState (packState z) = z := by
  rcases z with ⟨a, b, d, r⟩
  simp [packState, unpackState, aCode, bCode, dCode, rCode]

theorem unpack_state_inverse (w : ℕ) : packState (unpackState w) = w := by
  simp [packState, unpackState, aCode, bCode, dCode, rCode]

theorem numeric_stage_equations : stateNumber 0 = 0 ∧
    ∀ s, stateNumber (s + 1) = nextNumber s (stateNumber s) := by
  constructor
  · rfl
  · intro s
    simp [stateNumber, nextNumber, stage, pack_state_inverse]

theorem tabulate_length (n : ℕ) (f : ℕ → ℕ) :
    FiniteSequenceCoding.length (tabulate n f) = n := by
  simp [tabulate, FiniteSequenceCoding.length]

theorem tabulate_entry (n : ℕ) (f : ℕ → ℕ) (i : ℕ) :
    FiniteSequenceCoding.entry (tabulate n f) i = if i < n then f i else 0 := by
  rw [tabulate, FiniteSequenceCoding.entry_code]
  by_cases h : i < n
  · simp [h]
  · simp [h]

theorem reservoir_range (i : ℕ) : reservoir i = Set.range (Nat.pair i) := by
  ext x
  constructor
  · intro h
    change x.unpair.1 = i at h
    refine ⟨x.unpair.2, ?_⟩
    rw [← h]
    exact Nat.pair_unpair x
  · rintro ⟨y, rfl⟩
    simp [reservoir]

theorem reservoir_infinite (i : ℕ) : (reservoir i).Infinite := by
  rw [reservoir_range]
  apply Set.infinite_range_of_injective
  intro x y h
  simpa using congrArg (fun n : ℕ => n.unpair.2) h

theorem reservoirs_disjoint {i j : ℕ} (h : i ≠ j) :
    Disjoint (reservoir i) (reservoir j) := by
  apply Set.disjoint_left.mpr
  intro x hi hj
  exact h (hi.symm.trans hj)

theorem private_large_witness (i v : ℕ) :
    Nat.pair i (v + 1) ∈ reservoir i ∧ v < Nat.pair i (v + 1) := by
  constructor
  · simp [reservoir]
  · have h := (Nat.pair i (v + 1)).unpair_right_le
    simp only [Nat.unpair_pair] at h
    omega

theorem witness_bound (s : ℕ) (z : State) (i : ℕ) : witness s z i ≤ s + 1 := by
  exact (boundedSearch_spec _ (s, z, i) (s + 1)).1

theorem witness_success (s : ℕ) (z : State) (i : ℕ) (h : witness s z i < s + 1) :
    Eligible s z i (witness s z i) := by
  exact ((boundedSearch_spec _ (s, z, i) (s + 1)).2.1 h).1

theorem witness_minimal (s : ℕ) (z : State) (i x : ℕ) (h : Eligible s z i x) :
    witness s z i ≤ x := by
  have hs := boundedSearch_spec (fun p : ℕ × State × ℕ => Eligible p.1 p.2.1 p.2.2) (s, z, i) (s + 1)
  by_contra hn
  have hl : witness s z i < s + 1 := by
    by_contra hh
    have he : witness s z i = s + 1 := le_antisymm (witness_bound s z i) (by omega)
    exact hs.2.2.mp he x (by have := h.2.1; omega) h
  have hm : ∀ y < witness s z i, ¬ Eligible s z i y := (hs.2.1 hl).2
  exact hm x (by omega) h

theorem priority_bound (s : ℕ) (z : State) : priority s z ≤ s + 1 := by
  exact (boundedSearch_spec _ (s, z) (s + 1)).1

theorem chosen_eligible (s : ℕ) (z : State) (h : HasAction s z) :
    Eligible s z (priority s z) (chosenWitness s z) := by
  have hw := ((boundedSearch_spec
    (fun p : ℕ × State => fun i => witness p.1 p.2 i < p.1 + 1)
    (s, z) (s + 1)).2.1 h).1
  exact witness_success s z (priority s z) hw

theorem priority_minimal (s : ℕ) (z : State) (i x : ℕ) (h : Eligible s z i x) :
    HasAction s z ∧ priority s z ≤ i := by
  have hw : witness s z i < s + 1 := lt_of_le_of_lt (witness_minimal s z i x h) (by have := h.2.1; omega)
  have hs := boundedSearch_spec
    (fun p : ℕ × State => fun i => witness p.1 p.2 i < p.1 + 1) (s, z) (s + 1)
  have hp : HasAction s z := by
    by_contra hn
    have he : priority s z = s + 1 := by have := priority_bound s z; unfold HasAction at hn; omega
    exact hs.2.2.mp he i (by have := h.1; omega) hw
  refine ⟨hp, ?_⟩
  by_contra hn
  have hm : ∀ j < priority s z, ¬ witness s z j < s + 1 := (hs.2.1 hp).2
  exact hm i (by omega) hw

theorem no_action_iff (s : ℕ) (z : State) :
    ¬ HasAction s z ↔ ¬ ∃ i x, Eligible s z i x := by
  constructor
  · rintro hn ⟨i, x, hx⟩
    exact hn (priority_minimal s z i x hx).1
  · intro hn ha
    exact hn ⟨priority s z, chosenWitness s z, chosen_eligible s z ha⟩

theorem acts_iff (i s : ℕ) :
    Acts i s ↔ HasAction s (stage s) ∧ priority s (stage s) = i := by
  by_cases h : HasAction s (stage s)
  · simp [Acts, action, h]
  · simp [Acts, action, h]

theorem action_unique {i j s : ℕ} (hi : Acts i s) (hj : Acts j s) : i = j := by
  exact (acts_iff i s).mp hi |>.2.symm.trans ((acts_iff j s).mp hj).2

theorem acted_eligible {i s : ℕ} (h : Acts i s) :
    Eligible s (stage s) i (witnessAt s) := by
  obtain ⟨ha, hp⟩ := (acts_iff i s).mp h
  have he := chosen_eligible s (stage s) ha
  simpa only [hp, witnessAt] using he

theorem requirement_function_inequality (A B : Set ℕ) (i : ℕ) : RequirementFor A B i ↔
    (fun x => OracleProgramNumberings.phi (if i % 2 = 0 then B else A) (i / 2) x) ≠
      (fun x => Part.some (indicator (if i % 2 = 0 then A else B) x)) := by
  simp only [RequirementFor, ne_eq, funext_iff, not_forall]

end
end Lemmatheca.ComputabilityTheory.FiniteInjury
