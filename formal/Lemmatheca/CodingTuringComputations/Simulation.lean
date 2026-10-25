import Lemmatheca.CodingTuringComputations.Representation
import Lemmatheca.CodingTuringComputations.Numerical

namespace Lemmatheca.ComputabilityTheory.TapeCoding

open TuringMachines (Alphabet Config)

variable {Γ Q : Type*} {A : Alphabet Γ} [Fintype Γ] [Fintype Q]
variable {T : TuringMachines.Machine A Q}

private theorem entry_cons_zero (a c : ℕ) :
    FiniteSequenceCoding.entry (FiniteSequenceCoding.cons a c) 0 = a := by
  have h : FiniteSequenceCoding.entry (FiniteSequenceCoding.code
      (a :: FiniteSequenceCoding.decode c)) 0 = a := by
    rw [FiniteSequenceCoding.entry_code]
    rfl
  simpa only [FiniteSequenceCoding.code_cons, FiniteSequenceCoding.code_decode] using h

private theorem entry_cons_succ (a c i : ℕ) :
    FiniteSequenceCoding.entry (FiniteSequenceCoding.cons a c) (i + 1) =
      FiniteSequenceCoding.entry c i := by
  have h : FiniteSequenceCoding.entry (FiniteSequenceCoding.code
      (a :: FiniteSequenceCoding.decode c)) (i + 1) =
      FiniteSequenceCoding.entry (FiniteSequenceCoding.code (FiniteSequenceCoding.decode c)) i := by
    rw [FiniteSequenceCoding.entry_code, FiniteSequenceCoding.entry_code]
    rfl
  simpa only [FiniteSequenceCoding.code_cons, FiniteSequenceCoding.code_decode] using h

private theorem entry_tail (c i : ℕ) :
    FiniteSequenceCoding.entry (FiniteSequenceCoding.tail c) i =
      FiniteSequenceCoding.entry c (i + 1) := by
  rw [← FiniteSequenceCoding.code_decode c, FiniteSequenceCoding.tail_code]
  simp [FiniteSequenceCoding.entry]

private theorem head_entry (c : ℕ) :
    FiniteSequenceCoding.head c = FiniteSequenceCoding.entry c 0 := by
  simpa [FiniteSequenceCoding.tails] using (FiniteSequenceCoding.entry_eq_head c 0).symm

omit [Fintype Γ] [Fintype Q] in
private theorem written_away (X : Config A Q) (b : Γ) (z : ℤ) (hz : z ≠ X.head) :
    (X.tape.write X.head b) z = X.tape z := by
  exact Function.update_of_ne hz _ _

theorem halt_simulation (L : Labeling T) (X : Config A Q) (c : ℕ)
    (hc : Represents L X c) : haltCode L c = 1 ↔ TuringMachines.Halted T X := by
  have hv := (validTest_spec _ _ c).mpr hc.1
  rw [(haltCode_spec L c).1]
  simp only [haltTest, hv, Bool.not_true, Bool.false_or, beq_iff_eq,
    hc.2.1, hc.2.2.1, lookup_actual, TuringMachines.Halted]
  cases T.table X.state (X.tape X.head) <;> simp

theorem transition_simulation (L : Labeling T) (X Y : Config A Q) (c : ℕ)
    (hc : Represents L X c) (hXY : TuringMachines.Step T X Y) :
    Represents L Y (transition L c) := by
  classical
  unfold TuringMachines.Step TuringMachines.step at hXY
  cases ht : T.table X.state (X.tape X.head) with
  | none => simp [ht] at hXY
  | some row =>
    rcases row with ⟨q, b, m⟩
    simp only [ht, Option.map_some, Option.some.injEq] at hXY
    subst Y
    have hw : lookup L (stateCode c) (currentCode c) =
        1 + Nat.pair (L.state q).val (Nat.pair (L.symbol b).val (moveCode m)) := by
      rw [hc.2.1, hc.2.2.1, lookup_actual, ht]
    have hd := transition_rows L c (L.state q).val (L.symbol b).val m hc.1 hw
    have hv := transition_valid L c hc.1
    rw [hd] at hv ⊢
    cases m with
    | left =>
      refine ⟨hv, ?_, ?_, ?_, ?_⟩
      · exact (pack_fields _ _ _ _).1
      · change currentCode (pack _ _ _ _) =
          (L.symbol ((X.tape.write X.head b) (X.head + (-1)))).val
        rw [(pack_fields _ _ _ _).2.1, head_entry, hc.2.2.2.1 0,
          written_away X b _ (by omega)]
        simp [sub_eq_add_neg]
      · intro i
        change FiniteSequenceCoding.entry (leftCode (pack _ _ _ _)) i =
          (L.symbol ((X.tape.write X.head b) (X.head + (-1) - (i : ℤ) - 1))).val
        rw [(pack_fields _ _ _ _).2.2.1, entry_tail, hc.2.2.2.1 (i + 1),
          written_away X b _ (by omega)]
        congr 3
        push_cast
        ring
      · intro i
        change FiniteSequenceCoding.entry (rightCode (pack _ _ _ _)) i =
          (L.symbol ((X.tape.write X.head b) (X.head + (-1) + (i : ℤ) + 1))).val
        rw [(pack_fields _ _ _ _).2.2.2]
        cases i with
        | zero =>
          rw [entry_cons_zero]
          simp [TuringMachines.Tape.write]
        | succ i =>
          rw [entry_cons_succ, hc.2.2.2.2 i,
            written_away X b _ (by push_cast; omega)]
          congr 3
          push_cast
          ring
    | stay =>
      refine ⟨hv, ?_, ?_, ?_, ?_⟩
      · exact (pack_fields _ _ _ _).1
      · change currentCode (pack _ _ _ _) =
          (L.symbol ((X.tape.write X.head b) (X.head + 0))).val
        rw [(pack_fields _ _ _ _).2.1]
        simp [TuringMachines.Tape.write]
      · intro i
        change FiniteSequenceCoding.entry (leftCode (pack _ _ _ _)) i =
          (L.symbol ((X.tape.write X.head b) (X.head + 0 - (i : ℤ) - 1))).val
        rw [(pack_fields _ _ _ _).2.2.1, hc.2.2.2.1 i,
          written_away X b _ (by omega)]
        simp
      · intro i
        change FiniteSequenceCoding.entry (rightCode (pack _ _ _ _)) i =
          (L.symbol ((X.tape.write X.head b) (X.head + 0 + (i : ℤ) + 1))).val
        rw [(pack_fields _ _ _ _).2.2.2, hc.2.2.2.2 i,
          written_away X b _ (by omega)]
        simp
    | right =>
      refine ⟨hv, ?_, ?_, ?_, ?_⟩
      · exact (pack_fields _ _ _ _).1
      · change currentCode (pack _ _ _ _) =
          (L.symbol ((X.tape.write X.head b) (X.head + 1))).val
        rw [(pack_fields _ _ _ _).2.1, head_entry, hc.2.2.2.2 0,
          written_away X b _ (by omega)]
        simp
      · intro i
        change FiniteSequenceCoding.entry (leftCode (pack _ _ _ _)) i =
          (L.symbol ((X.tape.write X.head b) (X.head + 1 - (i : ℤ) - 1))).val
        rw [(pack_fields _ _ _ _).2.2.1]
        cases i with
        | zero =>
          rw [entry_cons_zero]
          simp [TuringMachines.Tape.write]
        | succ i =>
          rw [entry_cons_succ, hc.2.2.2.1 i,
            written_away X b _ (by push_cast; omega)]
          congr 3
          push_cast
          ring
      · intro i
        change FiniteSequenceCoding.entry (rightCode (pack _ _ _ _)) i =
          (L.symbol ((X.tape.write X.head b) (X.head + 1 + (i : ℤ) + 1))).val
        rw [(pack_fields _ _ _ _).2.2.2, entry_tail, hc.2.2.2.2 (i + 1),
          written_away X b _ (by omega)]
        congr 3
        push_cast
        ring

theorem advance_simulation (L : Labeling T) (X : Config A Q) (c : ℕ)
    (hc : Represents L X c) :
    Represents L (TuringMachines.advance T X) (transition L c) := by
  cases hs : TuringMachines.step T X with
  | none =>
    have hh := (TuringMachines.halted_no_step T X).mpr hs
    have ht := (haltCode_spec L c).1.mp ((halt_simulation L X c hc).mpr hh)
    simpa [TuringMachines.advance, hs, halted_fixed L c ht] using hc
  | some Y =>
    have hr := transition_simulation L X Y c hc hs
    simpa [TuringMachines.advance, hs] using hr

theorem input_represents (L : Labeling T) (n : ℕ) :
    Represents L (TuringMachines.input A T n) (initialCode n) := by
  have hq : stateCode (initialCode n) = (L.state (TuringMachines.input A T n).state).val := by
    cases n <;>
      simpa only [initialCode, stateCode, pack, Nat.unpair_pair, Prod.fst, TuringMachines.input]
        using L.initial_zero.symm
  have ha : currentCode (initialCode n) =
      (L.symbol ((TuringMachines.input A T n).tape (TuringMachines.input A T n).head)).val := by
    cases n with
    | zero =>
      simpa [initialCode, currentCode, pack, TuringMachines.input, TuringMachines.unaryTape]
        using L.blank_zero.symm
    | succ n =>
      simpa [initialCode, currentCode, pack, TuringMachines.input, TuringMachines.unaryTape]
        using L.mark_one.symm
  have hl : ∀ i : ℕ, FiniteSequenceCoding.entry (leftCode (initialCode n)) i =
      (L.symbol ((TuringMachines.input A T n).tape
        ((TuringMachines.input A T n).head - (i : ℤ) - 1))).val := by
    intro i
    have hb : ¬ (0 ≤ (0 : ℤ) - i - 1 ∧ (0 : ℤ) - i - 1 < n) := by omega
    have ht : (TuringMachines.input A T n).tape
        ((TuringMachines.input A T n).head - (i : ℤ) - 1) = A.blank := by
      change (if 0 ≤ (0 : ℤ) - i - 1 ∧ (0 : ℤ) - i - 1 < n then A.mark else A.blank) = A.blank
      rw [ite_eq_right hb]
    rw [ht, L.blank_zero]
    cases n <;> simp [initialCode, leftCode, pack, FiniteSequenceCoding.entry]
  have hr : ∀ i : ℕ, FiniteSequenceCoding.entry (rightCode (initialCode n)) i =
      (L.symbol ((TuringMachines.input A T n).tape
        ((TuringMachines.input A T n).head + (i : ℤ) + 1))).val := by
    intro i
    cases n with
    | zero =>
      have hb : ¬ (0 ≤ (0 : ℤ) + i + 1 ∧ (0 : ℤ) + i + 1 < 0) := by omega
      have ht : (TuringMachines.input A T 0).tape
          ((TuringMachines.input A T 0).head + (i : ℤ) + 1) = A.blank := by
        change (if 0 ≤ (0 : ℤ) + i + 1 ∧ (0 : ℤ) + i + 1 < 0 then A.mark else A.blank) = A.blank
        rw [ite_eq_right hb]
      rw [ht, L.blank_zero]
      simp [initialCode, rightCode, pack, FiniteSequenceCoding.entry]
    | succ n =>
      simp only [initialCode, rightCode, pack, Nat.unpair_pair,
        marks_list, FiniteSequenceCoding.entry_code, TuringMachines.input]
      change (List.replicate n 1)[i]?.getD 0 =
        (L.symbol (if 0 ≤ (0 : ℤ) + i + 1 ∧ (0 : ℤ) + i + 1 < (n + 1 : ℕ)
          then A.mark else A.blank)).val
      by_cases hi : i < n
      · have hh : 0 ≤ (0 : ℤ) + i + 1 ∧ (0 : ℤ) + i + 1 < (n + 1 : ℕ) := by omega
        rw [ite_eq_left hh]
        simp [hi, L.mark_one]
      · have hh : ¬ (0 ≤ (0 : ℤ) + i + 1 ∧ (0 : ℤ) + i + 1 < (n + 1 : ℕ)) := by omega
        rw [ite_eq_right hh]
        simp [hi, L.blank_zero]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, hq, ha, hl, hr⟩
  · rw [hq]; exact Fin.isLt _
  · rw [ha]; exact Fin.isLt _
  · intro i _; rw [hl]; exact Fin.isLt _
  · intro i _; rw [hr]; exact Fin.isLt _

theorem readout_simulation (L : Labeling T) (X : Config A Q) (c : ℕ)
    (hc : Represents L X c) :
    readoutCode (Fintype.card Γ) (Fintype.card Q) c = TuringMachines.readout A X := by
  have he (i : ℕ) :
      FiniteSequenceCoding.entry (FiniteSequenceCoding.cons (currentCode c) (rightCode c)) i =
        (L.symbol (X.tape (X.head + (i : ℤ)))).val := by
    cases i with
    | zero => simpa only [entry_cons_zero, Int.natCast_zero, add_zero] using hc.2.2.1
    | succ i =>
      rw [entry_cons_succ, hc.2.2.2.2 i]
      congr 3
      push_cast
      ring
  rw [readoutCode, ite_eq_left ((validTest_spec _ _ _).mpr hc.1)]
  have hs := rawReadout_spec c
  have hn := TuringMachines.readout_spec A X
  apply le_antisymm
  · by_contra h
    have hm := hs.2.1 (TuringMachines.readout A X) (by omega)
    rw [he] at hm
    have ht : X.tape (X.head + TuringMachines.readout A X) = A.mark :=
      L.symbol.injective (Fin.ext (hm.trans L.mark_one.symm))
    exact hn.1 ht
  · by_contra h
    have hm := hn.2 (rawReadout c) (by omega)
    have hb := hs.1
    rw [he, hm, L.mark_one] at hb
    exact hb rfl

noncomputable def numericalRun (L : Labeling T) (n : ℕ) : ℕ → ℕ
  | 0 => initialCode n
  | k + 1 => transition L (numericalRun L n k)

noncomputable def prefixCode (L : Labeling T) (n : ℕ) : ℕ → ℕ
  | 0 => FiniteSequenceCoding.cons (initialCode n) 0
  | k + 1 => FiniteSequenceCoding.append (prefixCode L n k)
      (FiniteSequenceCoding.cons (numericalRun L n (k + 1)) 0)

theorem prefixCode_correct (L : Labeling T) (n k : ℕ) :
    prefixCode L n k = FiniteSequenceCoding.code ((List.range (k + 1)).map (numericalRun L n)) ∧
    FiniteSequenceCoding.length (prefixCode L n k) = k + 1 ∧
    ∀ i ≤ k, FiniteSequenceCoding.entry (prefixCode L n k) i = numericalRun L n i := by
  have hcode : prefixCode L n k =
      FiniteSequenceCoding.code ((List.range (k + 1)).map (numericalRun L n)) := by
    induction k with
    | zero => simp [prefixCode, numericalRun, FiniteSequenceCoding.cons, Nat.add_comm]
    | succ k ih =>
      have hone (x : ℕ) : FiniteSequenceCoding.cons x 0 = FiniteSequenceCoding.code [x] := by
        simpa [FiniteSequenceCoding.code] using (FiniteSequenceCoding.code_cons x []).symm
      rw [prefixCode, ih, hone]
      rw [FiniteSequenceCoding.append_code]
      simp [List.range_succ, List.map_append]
  refine ⟨hcode, ?_, ?_⟩
  · simp [hcode, FiniteSequenceCoding.length]
  · intro i hi
    simp [hcode, FiniteSequenceCoding.entry_code, show i < k + 1 by omega]

theorem numericalRun_primrec (L : Labeling T) : Primrec₂ (numericalRun L) := by
  exact (Primrec.nat_rec initialCode_primrec
    ((transition_primrec L).comp (Primrec.snd.comp Primrec.snd)).to₂).of_eq
      (fun n k => by induction k <;> simp_all [numericalRun])
theorem prefixCode_primrec (L : Labeling T) : Primrec₂ (prefixCode L) := by
  have hinit : Primrec (fun n => FiniteSequenceCoding.cons (initialCode n) 0) :=
    FiniteSequenceCoding.primrec_cons.comp initialCode_primrec (Primrec.const 0)
  have hrun : Primrec (fun t : ℕ × (ℕ × ℕ) => numericalRun L t.1 (t.2.1 + 1)) :=
    (numericalRun_primrec L).comp Primrec.fst
      (Primrec.succ.comp (Primrec.fst.comp Primrec.snd))
  have hstep : Primrec (fun t : ℕ × (ℕ × ℕ) =>
      FiniteSequenceCoding.append t.2.2
        (FiniteSequenceCoding.cons (numericalRun L t.1 (t.2.1 + 1)) 0)) :=
    FiniteSequenceCoding.primrec_append.comp (Primrec.snd.comp Primrec.snd)
      (FiniteSequenceCoding.primrec_cons.comp hrun (Primrec.const 0))
  exact (Primrec.nat_rec hinit hstep.to₂).of_eq
    (fun n k => by induction k <;> simp_all [prefixCode])

theorem run_simulation (L : Labeling T) (n k : ℕ) :
    Represents L (TuringMachines.run T (TuringMachines.input A T n) k) (numericalRun L n k) := by
  induction k with
  | zero => exact input_represents L n
  | succ k ih => exact advance_simulation L _ _ ih

theorem numericalRun_valid (L : Labeling T) (n k : ℕ) :
    Valid (Fintype.card Γ) (Fintype.card Q) (numericalRun L n k) := by
  exact (run_simulation L n k).1

theorem arithmetic_run_eq (L : Labeling T) (n k : ℕ) :
    MachinesAndComputationHistories.run (arithmeticMachine L) n k = numericalRun L n k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [MachinesAndComputationHistories.run, ih]
    change (if haltTest L (numericalRun L n k) then numericalRun L n k
      else transition L (numericalRun L n k)) = transition L (numericalRun L n k)
    cases hh : haltTest L (numericalRun L n k) with
    | false => simp
    | true => simp [halted_fixed L _ hh]

theorem compute_eq_native (L : Labeling T) :
    MachinesAndComputationHistories.compute (arithmeticMachine L) =
      fun n => Part.ofOption (TuringMachines.computed T n) := by
  funext n
  apply Part.ext
  intro m
  rw [MachinesAndComputationHistories.compute_output, Part.mem_ofOption]
  change (∃ k, (arithmeticMachine L).halt
      (MachinesAndComputationHistories.run (arithmeticMachine L) n k) = true ∧
    (arithmeticMachine L).output
      (MachinesAndComputationHistories.run (arithmeticMachine L) n k) = m) ↔
    TuringMachines.computed T n = some m
  rw [TuringMachines.computed_spec]
  constructor
  · rintro ⟨k, hk, ho⟩
    have hc := run_simulation L n k
    have hh : haltTest L (numericalRun L n k) = true := by
      rw [arithmetic_run_eq] at hk
      exact hk
    refine ⟨k, (halt_simulation L _ _ hc).mp ((haltCode_spec L _).1.mpr hh), ?_⟩
    rw [← readout_simulation L _ _ hc]
    rw [arithmetic_run_eq] at ho
    exact ho
  · rintro ⟨k, hk, ho⟩
    have hc := run_simulation L n k
    have hh : haltTest L (numericalRun L n k) = true :=
      (haltCode_spec L _).1.mp ((halt_simulation L _ _ hc).mpr hk)
    refine ⟨k, ?_, ?_⟩
    · change haltTest L (MachinesAndComputationHistories.run (arithmeticMachine L) n k) = true
      rw [arithmetic_run_eq]
      exact hh
    · change readoutCode (Fintype.card Γ) (Fintype.card Q)
        (MachinesAndComputationHistories.run (arithmeticMachine L) n k) = m
      rw [arithmetic_run_eq, readout_simulation L _ _ hc]
      exact ho

def History (L : Labeling T) (n s : ℕ) : Prop :=
  0 < FiniteSequenceCoding.length s ∧
  (∀ i < FiniteSequenceCoding.length s,
    Valid (Fintype.card Γ) (Fintype.card Q) (FiniteSequenceCoding.entry s i)) ∧
  FiniteSequenceCoding.entry s 0 = initialCode n ∧
  haltCode L (FiniteSequenceCoding.entry s (FiniteSequenceCoding.length s - 1)) = 1 ∧
  ∀ i < FiniteSequenceCoding.length s - 1,
    haltCode L (FiniteSequenceCoding.entry s i) = 0 ∧
    FiniteSequenceCoding.entry s (i + 1) = transition L (FiniteSequenceCoding.entry s i)

def Certificate (L : Labeling T) (n w : ℕ) : Prop :=
  History L n (Nat.unpair w).2 ∧
  (Nat.unpair w).1 = readoutCode (Fintype.card Γ) (Fintype.card Q)
    (FiniteSequenceCoding.entry (Nat.unpair w).2 (FiniteSequenceCoding.length (Nat.unpair w).2 - 1))

theorem history_iff_arithmetic (L : Labeling T) (n s : ℕ) :
    History L n s ↔ MachinesAndComputationHistories.History (arithmeticMachine L) n s := by
  constructor
  · rintro ⟨hlen, hvalid, hinit, hhalt, hstep⟩
    refine ⟨hlen, hinit, (haltCode_spec L _).1.mp hhalt, ?_⟩
    intro i hi
    exact ⟨(haltCode_spec L _).2.mp (hstep i hi).1, (hstep i hi).2⟩
  · intro hs
    refine ⟨hs.1, ?_, hs.2.1, (haltCode_spec L _).1.mpr hs.2.2.1, ?_⟩
    · intro i hi
      rw [MachinesAndComputationHistories.history_run (arithmeticMachine L) n s i hs hi,
        arithmetic_run_eq]
      exact numericalRun_valid L n i
    · intro i hi
      exact ⟨(haltCode_spec L _).2.mpr (hs.2.2.2 i hi).1, (hs.2.2.2 i hi).2⟩

theorem certificate_iff_arithmetic (L : Labeling T) (n w : ℕ) :
    Certificate L n w ↔ MachinesAndComputationHistories.Certificate (arithmeticMachine L) n w := by
  exact and_congr_left (fun _ => history_iff_arithmetic L n (Nat.unpair w).2)

theorem history_primrec (L : Labeling T) : PrimrecRel (History L) := by
  exact (MachinesAndComputationHistories.history_primrec (arithmeticMachine L)
    (arithmeticMachine_primitive L)).of_eq
      (fun n s => (history_iff_arithmetic L n s).symm)
theorem certificate_primrec (L : Labeling T) : PrimrecRel (Certificate L) := by
  exact (MachinesAndComputationHistories.certificate_primrec (arithmeticMachine L)
    (arithmeticMachine_primitive L)).of_eq
      (fun n w => (certificate_iff_arithmetic L n w).symm)

theorem history_run (L : Labeling T) (n s i : ℕ) (hs : History L n s)
    (hi : i < FiniteSequenceCoding.length s) :
    FiniteSequenceCoding.entry s i = numericalRun L n i := by
  exact (MachinesAndComputationHistories.history_run (arithmeticMachine L) n s i
    ((history_iff_arithmetic L n s).mp hs) hi).trans (arithmetic_run_eq L n i)

theorem history_empty (L : Labeling T) (n : ℕ) : ¬ History L n 0 := by
  intro hs
  have hpos := hs.1
  simp [FiniteSequenceCoding.length] at hpos

theorem history_singleton (L : Labeling T) (n : ℕ) :
    History L n (FiniteSequenceCoding.code [initialCode n]) ↔ haltCode L (initialCode n) = 1 := by
  have hlen : FiniteSequenceCoding.length (FiniteSequenceCoding.code [initialCode n]) = 1 := by
    rw [FiniteSequenceCoding.length, FiniteSequenceCoding.decode_code]
    rfl
  have hentry : FiniteSequenceCoding.entry (FiniteSequenceCoding.code [initialCode n]) 0 =
      initialCode n := by
    rw [FiniteSequenceCoding.entry_code]
    rfl
  constructor
  · intro hs
    have hh := hs.2.2.2.1
    rw [hlen, Nat.sub_self, hentry] at hh
    exact hh
  · intro hh
    refine ⟨by omega, ?_, hentry, ?_, ?_⟩
    · intro i hi
      have hzero : i = 0 := by omega
      subst i
      rw [hentry]
      exact (input_represents L n).1
    · rw [hlen, Nat.sub_self, hentry]
      exact hh
    · intro i hi
      rw [hlen] at hi
      omega

theorem first_halt_history (L : Labeling T) (n k : ℕ)
    (hk : TuringMachines.FirstHaltingTime T (TuringMachines.input A T n) k) :
    History L n (prefixCode L n k) := by
  obtain ⟨hcode, hlen, hentry⟩ := prefixCode_correct L n k
  have hi (i : ℕ) (hit : i < k) : haltCode L (numericalRun L n i) = 0 := by
    apply (haltCode_spec L _).2.mpr
    apply Bool.eq_false_iff.mpr
    intro hh
    exact hk.2 i hit ((halt_simulation L _ _ (run_simulation L n i)).mp
      ((haltCode_spec L _).1.mpr hh))
  refine ⟨by omega, ?_, ?_, ?_, ?_⟩
  · intro i hit
    rw [hentry i (by omega)]
    exact numericalRun_valid L n i
  · rw [hentry 0 (by omega)]
    rfl
  · rw [hlen, Nat.add_sub_cancel, hentry k (by omega)]
    exact (halt_simulation L _ _ (run_simulation L n k)).mpr hk.1
  · intro i hit
    rw [hlen] at hit
    rw [hentry i (by omega), hentry (i + 1) (by omega)]
    exact ⟨hi i (by omega), rfl⟩

theorem certificate_output (L : Labeling T) (n m : ℕ) :
    TuringMachines.Output T n m ↔ ∃ w, Certificate L n w ∧ (Nat.unpair w).1 = m := by
  have hnative : m ∈ Part.ofOption (TuringMachines.computed T n) ↔
      TuringMachines.Output T n m := by
    rw [Part.mem_ofOption]
    exact TuringMachines.computed_spec T n m
  rw [← hnative, ← congrFun (compute_eq_native L) n,
    MachinesAndComputationHistories.certificate_output]
  simp only [← certificate_iff_arithmetic, MachinesAndComputationHistories.extract]

theorem certificate_unique (L : Labeling T) (n w v : ℕ)
    (hw : Certificate L n w) (hv : Certificate L n v) :
    (Nat.unpair w).1 = (Nat.unpair v).1 := by
  exact Part.mem_unique
    ((MachinesAndComputationHistories.certificate_output (arithmeticMachine L) n _).mpr
      ⟨w, (certificate_iff_arithmetic L n w).mp hw, rfl⟩)
    ((MachinesAndComputationHistories.certificate_output (arithmeticMachine L) n _).mpr
      ⟨v, (certificate_iff_arithmetic L n v).mp hv, rfl⟩)

noncomputable def certificateTest (L : Labeling T) (n w : ℕ) : Bool := by
  classical
  exact decide (Certificate L n w)

theorem certificateTest_primrec (L : Labeling T) : Primrec₂ (certificateTest L) := by
  classical
  exact (certificate_primrec L).decide

noncomputable def certificateOutput (L : Labeling T) (n : ℕ) : Part ℕ :=
  (Nat.rfind (fun w => Part.some (certificateTest L n w))).map (fun w => (Nat.unpair w).1)

theorem certificateOutput_eq_native (L : Labeling T) :
    certificateOutput L = fun n => Part.ofOption (TuringMachines.computed T n) := by
  have htest : certificateTest L =
      MachinesAndComputationHistories.certificateTest (arithmeticMachine L) := by
    funext n w
    apply Bool.eq_iff_iff.mpr
    simp only [certificateTest, MachinesAndComputationHistories.certificateTest,
      decide_eq_true_eq]
    exact certificate_iff_arithmetic L n w
  funext n
  calc
    certificateOutput L n =
        (MachinesAndComputationHistories.firstCertificate (arithmeticMachine L) n).map
          MachinesAndComputationHistories.extract := by
      unfold certificateOutput MachinesAndComputationHistories.firstCertificate
      rw [htest]
      rfl
    _ = MachinesAndComputationHistories.compute (arithmeticMachine L) n :=
      (MachinesAndComputationHistories.compute_search (arithmeticMachine L) n).symm
    _ = Part.ofOption (TuringMachines.computed T n) := congrFun (compute_eq_native L) n

theorem turing_recursive (T : TuringMachines.Machine A Q) :
    PartialRecursiveFunctions.Recursive (fun v : PartialRecursiveFunctions.Args 1 =>
      Part.ofOption (TuringMachines.computed T (v.get 0))) := by
  let L := chooseLabeling T
  exact (MachinesAndComputationHistories.compute_recursive (arithmeticMachine L)
    (arithmeticMachine_primitive L)).of_eq
      (fun v => congrFun (compute_eq_native L) (v.get 0))

end Lemmatheca.ComputabilityTheory.TapeCoding
