import Lemmatheca.FiniteInjuryAndPostsProblem.Effectivity
import Lemmatheca.LowSimpleSets.Lowness
import Lemmatheca.PrimitiveRecursion.PrimitiveRecursiveAutomation

/-! The explicit fixed-certificate priority enumeration for a low simple set. -/
namespace Lemmatheca.ComputabilityTheory.LowSimpleSets

open PostsTheorem PrimitiveRecursion UniversalComputation

noncomputable section
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

abbrev State := ℕ × ℕ

def aCode (z : State) : ℕ := z.1

def rCode (z : State) : ℕ := z.2

def bit (z : State) (x : ℕ) : ℕ := beta (aCode z) x

def record (z : State) (i : ℕ) : ℕ := FiniteSequenceCoding.entry (rCode z) i

def NoMeeting (s : ℕ) (z : State) (e : ℕ) : Prop :=
  ∀ y < s + 1, ¬(bit z y = 1 ∧ EffectiveEnumerations.stageTest e (s + 1) y = 1)

def Eligible (s : ℕ) (z : State) (e x : ℕ) : Prop :=
  e ≤ s ∧ x ≤ s ∧ EffectiveEnumerations.stageTest e (s + 1) x = 1 ∧ 2 * e < x ∧
    NoMeeting s z e ∧ ∀ i < e, record z i ≤ x

def witness (s : ℕ) (z : State) (e : ℕ) : ℕ :=
  boundedSearch (fun p : ℕ × State × ℕ => Eligible p.1 p.2.1 p.2.2)
    (s, z, e) (s + 1)

def priority (s : ℕ) (z : State) : ℕ :=
  boundedSearch (fun p : ℕ × State => fun e => witness p.1 p.2 e < p.1 + 1)
    (s, z) (s + 1)

def HasAction (s : ℕ) (z : State) : Prop := priority s z < s + 1

def chosenWitness (s : ℕ) (z : State) : ℕ := witness s z (priority s z)

def nextACode (s : ℕ) (z : State) : ℕ :=
  FiniteInjury.tabulate (s + 1) (fun x =>
    if HasAction s z ∧ x = chosenWitness s z then 1 else bit z x)

def temporary (s : ℕ) (z : State) (i : ℕ) : ℕ :=
  if HasAction s z ∧ priority s z ≤ i then 0 else record z i

def fill (s : ℕ) (z : State) (i : ℕ) : ℕ :=
  if 0 < temporary s z i then temporary s z i
  else if 0 < finiteValue (nextACode s z) (s + 1) i i then s + 1 else 0

def next (s : ℕ) (z : State) : State :=
  (nextACode s z, FiniteInjury.tabulate (s + 1) (fill s z))

def stage : ℕ → State
  | 0 => (0, 0)
  | s + 1 => next s (stage s)

def stageBit (s x : ℕ) : ℕ := bit (stage s) x

def stageRecord (s i : ℕ) : ℕ := record (stage s) i

def stageSet (s : ℕ) : Set ℕ := finiteOracle (aCode (stage s))

def constructedSet : Set ℕ := {x | ∃ s, x ∈ stageSet s}

def Acts (e s : ℕ) : Prop := HasAction s (stage s) ∧ priority s (stage s) = e

def witnessAt (s : ℕ) : ℕ := chosenWitness s (stage s)

def jumpGuess (s i : ℕ) : ℕ := if 0 < stageRecord s i then 1 else 0

private theorem witness_bound (s : ℕ) (z : State) (e : ℕ) : witness s z e ≤ s + 1 :=
  (boundedSearch_spec _ (s, z, e) (s + 1)).1

private theorem witness_success (s : ℕ) (z : State) (e : ℕ)
    (h : witness s z e < s + 1) : Eligible s z e (witness s z e) :=
  ((boundedSearch_spec _ (s, z, e) (s + 1)).2.1 h).1

private theorem witness_minimal (s : ℕ) (z : State) (e x : ℕ)
    (h : Eligible s z e x) : witness s z e ≤ x := by
  have hs := boundedSearch_spec (fun p : ℕ × State × ℕ => Eligible p.1 p.2.1 p.2.2)
    (s, z, e) (s + 1)
  by_contra hn
  have hw : witness s z e < s + 1 := by
    by_contra hh
    have he : witness s z e = s + 1 := le_antisymm (witness_bound s z e) (by omega)
    exact hs.2.2.mp he x (by have := h.2.1; omega) h
  have hm : ∀ y < witness s z e, ¬ Eligible s z e y := (hs.2.1 hw).2
  exact hm x (by omega) h

private theorem chosen_eligible (s : ℕ) (z : State) (h : HasAction s z) :
    Eligible s z (priority s z) (chosenWitness s z) := by
  have hw := ((boundedSearch_spec
    (fun p : ℕ × State => fun e => witness p.1 p.2 e < p.1 + 1)
    (s, z) (s + 1)).2.1 h).1
  exact witness_success s z _ hw

private theorem priority_minimal (s : ℕ) (z : State) (e x : ℕ)
    (h : Eligible s z e x) : HasAction s z ∧ priority s z ≤ e := by
  have hw : witness s z e < s + 1 :=
    lt_of_le_of_lt (witness_minimal s z e x h) (by have := h.2.1; omega)
  have hs := boundedSearch_spec
    (fun p : ℕ × State => fun e => witness p.1 p.2 e < p.1 + 1) (s, z) (s + 1)
  have hp : HasAction s z := by
    by_contra hn
    have he : priority s z = s + 1 := by
      have hb : priority s z ≤ s + 1 := hs.1
      unfold HasAction at hn
      omega
    exact hs.2.2.mp he e (by have := h.1; omega) hw
  refine ⟨hp, ?_⟩
  by_contra hn
  have hm : ∀ j < priority s z, ¬ witness s z j < s + 1 := (hs.2.1 hp).2
  exact hm e (by omega) hw

theorem attention_data (s : ℕ) (z : State) :
    (HasAction s z ↔ ∃ e x, Eligible s z e x) ∧
      (HasAction s z → Eligible s z (priority s z) (chosenWitness s z) ∧
        ∀ e x, Eligible s z e x → priority s z ≤ e ∧
          (e = priority s z → chosenWitness s z ≤ x)) := by
  refine ⟨⟨fun h => ⟨_, _, chosen_eligible s z h⟩,
    fun ⟨e, x, h⟩ => (priority_minimal s z e x h).1⟩, ?_⟩
  intro h
  refine ⟨chosen_eligible s z h, fun e x he => ⟨(priority_minimal s z e x he).2, ?_⟩⟩
  intro heq
  subst e
  exact witness_minimal s z _ x he

private theorem bit_primitive : Primrec₂ bit := beta_primitive.comp (Primrec.fst.comp Primrec.fst) Primrec.snd

private theorem record_primitive : Primrec₂ record :=
  FiniteSequenceCoding.primrec_entry.comp (Primrec.snd.comp Primrec.fst) Primrec.snd

private theorem noMeeting_primitive :
    PrimrecPred (fun p : ℕ × State × ℕ => NoMeeting p.1 p.2.1 p.2.2) := by
  let P := ℕ × State × ℕ
  have hs : Primrec (fun p : P × ℕ => p.1.1 + 1) := Primrec.succ.comp (Primrec.fst.comp Primrec.fst)
  have hz : Primrec (fun p : P × ℕ => p.1.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have he : Primrec (fun p : P × ℕ => p.1.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have hb : PrimrecPred (fun p : P × ℕ => bit p.1.2.1 p.2 = 1) :=
    Primrec.eq.comp (bit_primitive.comp hz Primrec.snd) (Primrec.const 1)
  have hw : PrimrecPred (fun p : P × ℕ => EffectiveEnumerations.stageTest p.1.2.2
      (p.1.1 + 1) p.2 = 1) :=
    Primrec.eq.comp (EffectiveEnumerations.stage_test_primitive.comp ((he.pair hs).pair Primrec.snd))
      (Primrec.const 1)
  have hR : PrimrecRel (fun p : P => fun y => ¬(bit p.2.1 y = 1 ∧
      EffectiveEnumerations.stageTest p.2.2 (p.1 + 1) y = 1)) := (hb.and hw).not
  exact (bounded_forall_primrec hR).comp Primrec.id
    (Primrec.succ.comp Primrec.fst)

private theorem eligible_primitive :
    PrimrecPred (fun p : (ℕ × State × ℕ) × ℕ => Eligible p.1.1 p.1.2.1 p.1.2.2 p.2) := by
  let P := (ℕ × State × ℕ) × ℕ
  have hs : Primrec (fun p : P => p.1.1) := Primrec.fst.comp Primrec.fst
  have hz : Primrec (fun p : P => p.1.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have he : Primrec (fun p : P => p.1.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have hx : Primrec (fun p : P => p.2) := Primrec.snd
  have hw : PrimrecPred (fun p : P => EffectiveEnumerations.stageTest p.1.2.2
      (p.1.1 + 1) p.2 = 1) :=
    Primrec.eq.comp (EffectiveEnumerations.stage_test_primitive.comp
      ((he.pair (Primrec.succ.comp hs)).pair hx)) (Primrec.const 1)
  have hr : PrimrecRel (fun p : P => fun i => record p.1.2.1 i ≤ p.2) :=
    Primrec.nat_le.comp (record_primitive.comp (hz.comp Primrec.fst) Primrec.snd)
      (hx.comp Primrec.fst)
  have hrest := (bounded_forall_primrec hr).comp Primrec.id he
  have hnom : PrimrecPred (fun p : P => NoMeeting p.1.1 p.1.2.1 p.1.2.2) :=
    noMeeting_primitive.comp Primrec.fst
  exact (Primrec.nat_le.comp he hs).and ((Primrec.nat_le.comp hx hs).and
    (hw.and ((Primrec.nat_lt.comp (Primrec.nat_mul.comp (Primrec.const 2) he) hx).and
      (hnom.and hrest))))

private theorem witness_primitive :
    Primrec (fun p : ℕ × State × ℕ => witness p.1 p.2.1 p.2.2) :=
  (boundedSearch_primrec (R := fun p : ℕ × State × ℕ => Eligible p.1 p.2.1 p.2.2) eligible_primitive).comp Primrec.id (Primrec.succ.comp Primrec.fst)

private theorem priority_primitive : Primrec₂ priority := by
  have hw : Primrec (fun p : (ℕ × State) × ℕ => witness p.1.1 p.1.2 p.2) :=
    witness_primitive.comp ((Primrec.fst.comp Primrec.fst).pair
      ((Primrec.snd.comp Primrec.fst).pair Primrec.snd))
  have hR : PrimrecRel (fun p : ℕ × State => fun e => witness p.1 p.2 e < p.1 + 1) :=
    Primrec.nat_lt.comp hw (Primrec.succ.comp (Primrec.fst.comp Primrec.fst))
  exact (boundedSearch_primrec hR).comp Primrec.id (Primrec.succ.comp Primrec.fst)

private theorem nextACode_primitive : Primrec₂ nextACode := by
  let P := ℕ × State
  have hp : Primrec (fun p : P => priority p.1 p.2) := priority_primitive
  have hact : PrimrecPred (fun p : P => HasAction p.1 p.2) :=
    Primrec.nat_lt.comp hp (Primrec.succ.comp Primrec.fst)
  have hw : Primrec (fun p : P => chosenWitness p.1 p.2) :=
    witness_primitive.comp (Primrec.fst.pair (Primrec.snd.pair hp))
  have htest : PrimrecPred (fun p : P × ℕ => HasAction p.1.1 p.1.2 ∧ p.2 = chosenWitness p.1.1 p.1.2) :=
    (hact.comp Primrec.fst).and (Primrec.eq.comp Primrec.snd (hw.comp Primrec.fst))
  have hbit : Primrec (fun p : P × ℕ => bit p.1.2 p.2) :=
    bit_primitive.comp (Primrec.snd.comp Primrec.fst) Primrec.snd
  have hf : Primrec₂ (fun p : P => fun x => if HasAction p.1 p.2 ∧
      x = chosenWitness p.1 p.2 then 1 else bit p.2 x) :=
    Primrec.ite htest (Primrec.const 1) hbit
  exact (FiniteInjury.tabulate_primitive hf).comp Primrec.id (Primrec.succ.comp Primrec.fst)

private theorem temporary_primitive : Primrec (fun p : (ℕ × State) × ℕ => temporary p.1.1 p.1.2 p.2) := by
  have hp : Primrec (fun p : (ℕ × State) × ℕ => priority p.1.1 p.1.2) :=
    Primrec.comp priority_primitive Primrec.fst
  have hact : PrimrecPred (fun p : (ℕ × State) × ℕ => HasAction p.1.1 p.1.2) :=
    Primrec.nat_lt.comp hp (Primrec.succ.comp (Primrec.fst.comp Primrec.fst))
  exact Primrec.ite (hact.and (Primrec.nat_le.comp hp Primrec.snd)) (Primrec.const 0)
    (record_primitive.comp (Primrec.snd.comp Primrec.fst) Primrec.snd)

private theorem fill_primitive : Primrec (fun p : (ℕ × State) × ℕ => fill p.1.1 p.1.2 p.2) := by
  let P := (ℕ × State) × ℕ
  have hs : Primrec (fun p : P => p.1.1 + 1) := Primrec.succ.comp (Primrec.fst.comp Primrec.fst)
  have hu : Primrec (fun p : P => nextACode p.1.1 p.1.2) :=
    nextACode_primitive.comp (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.fst)
  have hv : Primrec (fun p : P => finiteValue (nextACode p.1.1 p.1.2) (p.1.1 + 1) p.2 p.2) :=
    (finiteValue_primitive.comp (Primrec₂.natPair.comp hu
      (Primrec₂.natPair.comp hs (Primrec₂.natPair.comp Primrec.snd Primrec.snd)))).of_eq
        (fun p => by simp [finiteValueInput])
  exact Primrec.ite (Primrec.nat_lt.comp (Primrec.const 0) temporary_primitive)
    temporary_primitive (Primrec.ite (Primrec.nat_lt.comp (Primrec.const 0) hv) hs (Primrec.const 0))

private theorem next_primitive : Primrec₂ next := by
  have ha : Primrec (fun p : ℕ × State => nextACode p.1 p.2) := nextACode_primitive
  have hf : Primrec₂ (fun p : ℕ × State => fill p.1 p.2) := fill_primitive
  exact ha.pair ((FiniteInjury.tabulate_primitive hf).comp
    Primrec.id (Primrec.succ.comp Primrec.fst))

theorem stage_primitive : Primrec stage := by
  apply (Primrec.nat_rec₁ (0, 0) next_primitive).of_eq
  intro s
  induction s with
  | zero => rfl
  | succ s ih => exact congrArg (next s) ih

theorem selection_primitive :
    Primrec (fun s => priority s (stage s)) ∧ Primrec witnessAt := by
  have hp := priority_primitive.comp Primrec.id stage_primitive
  exact ⟨hp, witness_primitive.comp (Primrec.id.pair (stage_primitive.pair hp))⟩

theorem stage_data_primitive : Primrec₂ stageBit ∧ Primrec₂ stageRecord :=
  ⟨bit_primitive.comp (stage_primitive.comp Primrec.fst) Primrec.snd,
    record_primitive.comp (stage_primitive.comp Primrec.fst) Primrec.snd⟩

private theorem state_lengths (s : ℕ) :
    FiniteSequenceCoding.length (aCode (stage s)) = s ∧
      FiniteSequenceCoding.length (rCode (stage s)) = s := by
  cases s with
  | zero => simp [stage, aCode, rCode, FiniteSequenceCoding.length]
  | succ s => simp [stage, next, nextACode, aCode, rCode, FiniteInjury.tabulate_length]

private theorem bit_outside (s x : ℕ) (h : s ≤ x) : stageBit s x = 0 := by
  unfold stageBit bit beta
  rw [FiniteSequenceCoding.entry_out_of_range _ _ (by rw [(state_lengths s).1]; exact h)]

private theorem record_outside (s i : ℕ) (h : s ≤ i) : stageRecord s i = 0 := by
  exact FiniteSequenceCoding.entry_out_of_range _ _ (by rw [(state_lengths s).2]; exact h)

private theorem beta_tabulate (n : ℕ) (f : ℕ → ℕ)
    (hf : ∀ j, f j = 0 ∨ f j = 1) (j : ℕ) :
    beta (FiniteInjury.tabulate n f) j = if j < n then f j else 0 := by
  unfold beta
  rw [FiniteInjury.tabulate_entry]
  by_cases hj : j < n
  · rcases hf j with h | h <;> simp [hj, h]
  · simp [hj]

theorem stage_bit_succ (s x : ℕ) :
    stageBit (s + 1) x = if HasAction s (stage s) ∧ x = witnessAt s then 1 else stageBit s x := by
  have hf : ∀ j, (if HasAction s (stage s) ∧ j = chosenWitness s (stage s) then 1
      else bit (stage s) j) = 0 ∨
      (if HasAction s (stage s) ∧ j = chosenWitness s (stage s) then 1 else bit (stage s) j) = 1 := by
    intro j
    split_ifs <;> simp [bit, beta_bits]
  have htab := beta_tabulate (s + 1) _ hf x
  change stageBit (s + 1) x = _ at htab
  rw [htab]
  by_cases hx : x < s + 1
  · simp [hx, witnessAt, stageBit]
  · have ho := bit_outside s x (by omega)
    have hn : ¬(HasAction s (stage s) ∧ x = witnessAt s) := by
      rintro ⟨ha, he⟩
      have hw := (chosen_eligible s (stage s) ha).2.1
      change witnessAt s ≤ s at hw
      omega
    simp [hx, hn, ho]

theorem stage_set_succ (s : ℕ) :
    stageSet (s + 1) = if HasAction s (stage s) then insert (witnessAt s) (stageSet s) else stageSet s := by
  ext x
  change stageBit (s + 1) x = 1 ↔ _
  rw [stage_bit_succ]
  by_cases ha : HasAction s (stage s) <;> by_cases hx : x = witnessAt s <;>
    simp [ha, hx, stageSet, finiteOracle, stageBit, bit]

theorem stage_monotone : Monotone stageSet := by
  apply monotone_nat_of_le_succ
  intro s x hx
  rw [stage_set_succ]
  split_ifs <;> simp_all

theorem positive_action_data {e s : ℕ} (h : Acts e s) :
    e ≤ s ∧ witnessAt s ≤ s ∧ 2 * e < witnessAt s ∧
      witnessAt s ∈ EffectiveEnumerations.stage e (s + 1) ∧
      witnessAt s ∉ stageSet s ∧
      stageSet (s + 1) = insert (witnessAt s) (stageSet s) ∧
      (∀ i < e, stageRecord s i ≤ witnessAt s) := by
  obtain ⟨ha, he⟩ := h
  have hel := chosen_eligible s (stage s) ha
  rw [he] at hel
  change Eligible s (stage s) e (witnessAt s) at hel
  rcases hel with ⟨hes, hxs, hW, hlarge, hnom, hrest⟩
  refine ⟨hes, hxs, hlarge, (EffectiveEnumerations.stage_test_spec e (s + 1) _).2.mp hW,
    ?_, by rw [stage_set_succ, ite_eq_left ha], hrest⟩
  intro hx
  exact hnom _ (by omega) ⟨hx, hW⟩

theorem no_action_update {s : ℕ} (h : ¬ HasAction s (stage s)) :
    stageSet (s + 1) = stageSet s := by
  rw [stage_set_succ, ite_eq_right h]

theorem record_update (s i : ℕ) (hi : i < s + 1) :
    stageRecord (s + 1) i = fill s (stage s) i := by
  exact (FiniteInjury.tabulate_entry (s + 1) (fill s (stage s)) i).trans (ite_eq_left hi)

private theorem records_bounded (s i : ℕ) : stageRecord s i ≤ s := by
  induction s with
  | zero => simp [stageRecord, stage, record, rCode, FiniteSequenceCoding.entry]
  | succ s ih =>
      by_cases hi : i < s + 1
      · rw [record_update s i hi]
        unfold fill temporary
        split_ifs <;> simp_all [stageRecord]
        omega
      · rw [record_outside (s + 1) i (by omega)]
        omega

private theorem finiteValue_congr (u v k e x : ℕ)
    (h : ∀ q < k, beta u q = beta v q) : finiteValue u k e x = finiteValue v k e x := by
  have ha : Agreement u k (finiteOracle v) := by
    intro q hq
    rw [finiteOracle_indicator]
    exact h q hq
  rw [finiteValue_agreement (finiteOracle v) u k e x ha, finiteValue_identity]

private theorem record_certificate (s i : ℕ) (hp : 0 < stageRecord s i) :
    0 < finiteValue (aCode (stage s)) (stageRecord s i) i i := by
  induction s with
  | zero => simp [stageRecord, stage, record, rCode, FiniteSequenceCoding.entry] at hp
  | succ s ih =>
      have hi : i < s + 1 := by
        by_contra hn
        rw [record_outside (s + 1) i (by omega)] at hp
        omega
      have hr := record_update s i hi
      by_cases htemp : 0 < temporary s (stage s) i
      · have htempEq : temporary s (stage s) i = stageRecord s i := by
          unfold temporary at htemp ⊢
          split_ifs with hreset <;> simp_all [stageRecord]
        have hrec : stageRecord (s + 1) i = stageRecord s i := by
          rw [hr, fill, ite_eq_left htemp, htempEq]
        rw [hrec] at hp ⊢
        have hold := ih hp
        have hprefix : ∀ q < stageRecord s i,
            beta (aCode (stage s)) q = beta (aCode (stage (s + 1))) q := by
          intro q hq
          change stageBit s q = stageBit (s + 1) q
          rw [stage_bit_succ]
          have hnot : ¬(HasAction s (stage s) ∧ q = witnessAt s) := by
            rintro ⟨ha, hqw⟩
            have hlt : i < priority s (stage s) := by
              by_contra hn
              simp [temporary, ha, show priority s (stage s) ≤ i by omega] at htemp
            have hb := (chosen_eligible s (stage s) ha).2.2.2.2.2 i hlt
            change stageRecord s i ≤ witnessAt s at hb
            omega
          simp [hnot]
        exact (finiteValue_congr _ _ _ i i hprefix) ▸ hold
      · by_cases hv : 0 < finiteValue (nextACode s (stage s)) (s + 1) i i
        · have hrec : stageRecord (s + 1) i = s + 1 := by simp [hr, fill, htemp, hv]
          rw [hrec]
          exact hv
        · simp [hr, fill, htemp, hv] at hp

theorem state_invariants (s : ℕ) :
    FiniteSequenceCoding.length (aCode (stage s)) = s ∧
      FiniteSequenceCoding.length (rCode (stage s)) = s ∧
      stageSet s ⊆ Set.Iio s ∧
      (∀ x, FiniteSequenceCoding.entry (aCode (stage s)) x = 0 ∨
        FiniteSequenceCoding.entry (aCode (stage s)) x = 1) ∧
      (∀ x, stageBit s x = 0 ∨ stageBit s x = 1) ∧
      (∀ i, stageRecord s i ≤ s) ∧
      (∀ i, 0 < stageRecord s i →
        0 < finiteValue (aCode (stage s)) (stageRecord s i) i i) := by
  refine ⟨(state_lengths s).1, (state_lengths s).2, ?_, ?_, fun x => beta_bits _ _,
    records_bounded s, record_certificate s⟩
  · intro x hx
    change x < s
    by_contra hn
    have hz := bit_outside s x (by omega)
    change stageBit s x = 1 at hx
    omega
  · intro x
    cases s with
    | zero => simp [stage, aCode, FiniteSequenceCoding.entry]
    | succ s =>
        simp only [stage, next, aCode, nextACode, FiniteInjury.tabulate_entry]
        split_ifs <;> simp [bit, beta_bits]

end
end Lemmatheca.ComputabilityTheory.LowSimpleSets
