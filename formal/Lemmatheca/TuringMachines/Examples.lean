import Lemmatheca.TuringMachines.Unary

namespace Lemmatheca.Entry.TuringMachines
open Lemmatheca.ComputabilityTheory.TuringMachines

def binary : Alphabet Bool := ⟨false, true, Bool.noConfusion⟩

inductive SuccessorState
  | scan | back | halt
  deriving DecidableEq

instance successorStateFintype : Fintype SuccessorState :=
  ⟨{.scan, .back, .halt}, by intro q; cases q <;> simp⟩

open SuccessorState

def successor : Machine binary SuccessorState where
  initial := scan
  table
    | scan, true => some (scan, true, .right)
    | scan, false => some (back, true, .left)
    | back, true => some (back, true, .left)
    | back, false => some (halt, false, .right)
    | halt, _ => none

private theorem succ_tape_ext {t u : Tape Bool binary.blank}
    (he : ∀ z, t z = u z) : t = u := by
  cases t with
  | mk t ht =>
    cases u with
    | mk u hu =>
      have htu : t = u := funext he
      cases htu
      rfl

private theorem successor_nonhalting (q : SuccessorState) (h : ℤ)
    (t : Tape Bool binary.blank) (hq : q = scan ∨ q = back) :
    ¬ Halted successor ⟨q, h, t⟩ := by
  rcases hq with rfl | rfl <;> cases hs : t h <;> simp [Halted, successor, hs]

private theorem succ_unary_mark (n : ℕ) (z : ℤ) (h : 0 ≤ z ∧ z < (n : ℤ)) :
    (unaryTape binary n) z = true := by
  change (if 0 ≤ z ∧ z < (n : ℤ) then true else false) = true
  rw [ite_eq_left h]

private theorem succ_unary_blank (n : ℕ) (z : ℤ) (h : ¬ (0 ≤ z ∧ z < (n : ℤ))) :
    (unaryTape binary n) z = false := by
  change (if 0 ≤ z ∧ z < (n : ℤ) then true else false) = false
  rw [ite_eq_right h]

theorem unary_extend (n : ℕ) :
    (unaryTape binary n).write n true = unaryTape binary (n + 1) := by
  classical
  apply succ_tape_ext
  intro z
  by_cases hz : z = (n : ℤ)
  · subst z
    have hn : 0 ≤ (n : ℤ) ∧ (n : ℤ) < ((n + 1 : ℕ) : ℤ) := by
      constructor <;> omega
    change Function.update (unaryTape binary n).cells (n : ℤ) true (n : ℤ) =
      (unaryTape binary (n + 1)).cells (n : ℤ)
    rw [Function.update_self, succ_unary_mark (n + 1) n hn]
  · change Function.update (unaryTape binary n).cells (n : ℤ) true z =
      (unaryTape binary (n + 1)).cells z
    rw [Function.update_of_ne hz]
    by_cases hp : 0 ≤ z ∧ z < (n : ℤ)
    · have hp' : 0 ≤ z ∧ z < ((n + 1 : ℕ) : ℤ) := by omega
      rw [succ_unary_mark n z hp, succ_unary_mark (n + 1) z hp']
    · have hp' : ¬ (0 ≤ z ∧ z < ((n + 1 : ℕ) : ℤ)) := by omega
      rw [succ_unary_blank n z hp, succ_unary_blank (n + 1) z hp']

theorem successor_scan (n i : ℕ) (hi : i ≤ n) :
    run successor (input binary successor n) i = ⟨scan, i, unaryTape binary n⟩ := by
  induction i with
  | zero => rfl
  | succ i ih =>
    have hi' : i < n := by omega
    have hs : (unaryTape binary n) (i : ℤ) = true := by
      exact succ_unary_mark n i ⟨by omega, by omega⟩
    have hw : (unaryTape binary n).write i true = unaryTape binary n := by
      simpa only [hs] using Tape.write_same (unaryTape binary n) (i : ℤ)
    rw [run, ih (by omega)]
    simp [advance, step, successor, hs, Move.displacement, hw]

theorem successor_back (n j : ℕ) (hj : j ≤ n) :
    run successor (input binary successor n) (n + 1 + j) =
      ⟨back, (n : ℤ) - 1 - j, unaryTape binary (n + 1)⟩ := by
  induction j with
  | zero =>
    rw [Nat.add_zero, run, successor_scan n n (by omega)]
    have hs : (unaryTape binary n) (n : ℤ) = false := by simp [unaryTape, binary]
    simp [advance, step, successor, hs, Move.displacement, unary_extend, sub_eq_add_neg]
  | succ j ih =>
    have hj' : j < n := by omega
    have hp : 0 ≤ (n : ℤ) - 1 - j ∧ (n : ℤ) - 1 - j < ((n + 1 : ℕ) : ℤ) := by
      constructor <;> omega
    have hs : (unaryTape binary (n + 1)) ((n : ℤ) - 1 - j) = true := by
      exact succ_unary_mark (n + 1) _ hp
    have hw : (unaryTape binary (n + 1)).write ((n : ℤ) - 1 - j) true =
        unaryTape binary (n + 1) := by
      simpa only [hs] using Tape.write_same (unaryTape binary (n + 1)) ((n : ℤ) - 1 - j)
    rw [Nat.add_succ, run, ih (by omega)]
    simp [advance, step, successor, hs, Move.displacement, hw]
    omega

theorem successor_final (n : ℕ) :
    run successor (input binary successor n) (2 * n + 2) =
      ⟨halt, 0, unaryTape binary (n + 1)⟩ := by
  have he : 2 * n + 2 = (n + 1 + n) + 1 := by omega
  rw [he, run, successor_back n n (by omega)]
  have hh : (n : ℤ) - 1 - n = -1 := by omega
  rw [hh]
  have hs : (unaryTape binary (n + 1)) (-1) = false := by simp [unaryTape, binary]
  have hw : (unaryTape binary (n + 1)).write (-1) false = unaryTape binary (n + 1) := by
    simpa only [hs] using Tape.write_same (unaryTape binary (n + 1)) (-1)
  simp [advance, step, successor, hs, Move.displacement, hw]

theorem successor_first_halt (n : ℕ) :
    FirstHaltingTime successor (input binary successor n) (2 * n + 2) := by
  constructor
  · change Halted successor (run successor (input binary successor n) (2 * n + 2))
    rw [successor_final]
    rfl
  · intro k hk
    change ¬ Halted successor (run successor (input binary successor n) k)
    by_cases hkn : k ≤ n
    · rw [successor_scan n k hkn]
      exact successor_nonhalting scan k _ (Or.inl rfl)
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (show n + 1 ≤ k by omega)
      have hj : j ≤ n := by omega
      rw [successor_back n j hj]
      exact successor_nonhalting back _ _ (Or.inr rfl)

theorem successor_output (n : ℕ) : Output successor n (n + 1) := by
  refine ⟨2 * n + 2, ?_, ?_⟩
  · rw [successor_final]
    rfl
  · rw [successor_final]
    change readout binary (input binary successor (n + 1)) = n + 1
    exact input_readout binary successor (n + 1)

theorem successor_step_two :
    Step successor ⟨scan, 2, unaryTape binary 2⟩ ⟨back, 1, unaryTape binary 3⟩ := by
  change (some (⟨back, (2 : ℤ) - 1, (unaryTape binary 2).write 2 true⟩ :
    Config binary SuccessorState)) = some ⟨back, 1, unaryTape binary 3⟩
  have hw := unary_extend 2
  norm_num at hw
  rw [hw]
  rfl

theorem successor_trace_zero :
    (List.range 3).map (fun k =>
      let C := run successor (input binary successor 0) k
      (C.state, C.head)) = [(scan, 0), (back, -1), (halt, 0)] := by
  have h0 := successor_scan 0 0 (by omega)
  have h1 := successor_back 0 0 (by omega)
  have h2 := successor_final 0
  norm_num at h0 h1 h2
  simp [List.range_succ, h0, h1, h2]

theorem successor_trace_two :
    (List.range 7).map (fun k =>
      let C := run successor (input binary successor 2) k
      (C.state, C.head)) =
      [(scan, 0), (scan, 1), (scan, 2), (back, 1), (back, 0), (back, -1), (halt, 0)] ∧
    (run successor (input binary successor 2) 2).tape = unaryTape binary 2 ∧
    (∀ k ≥ 3, (run successor (input binary successor 2) k).tape = unaryTape binary 3) := by
  have h0 := successor_scan 2 0 (by omega)
  have h1 := successor_scan 2 1 (by omega)
  have h2 := successor_scan 2 2 (by omega)
  have h3 := successor_back 2 0 (by omega)
  have h4 := successor_back 2 1 (by omega)
  have h5 := successor_back 2 2 (by omega)
  have h6 := successor_final 2
  norm_num at h0 h1 h2 h3 h4 h5 h6
  refine ⟨?_, ?_, ?_⟩
  · simp [List.range_succ, h0, h1, h2, h3, h4, h5, h6]
  · rw [h2]
  · intro k hk
    by_cases hlarge : 6 ≤ k
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hlarge
      have hh : Halted successor (run successor (input binary successor 2) 6) :=
        (successor_first_halt 2).1
      rw [run_halted_add successor (input binary successor 2) 6 j hh, h6]
    · rcases (show k = 3 ∨ k = 4 ∨ k = 5 by omega) with rfl | rfl | rfl <;>
        simp [h3, h4, h5]

def drift : Machine binary Unit where
  initial := ()
  table _ a := some ((), a, .right)

theorem drift_run (n k : ℕ) :
    run drift (input binary drift n) k = ⟨(), k, unaryTape binary n⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [run, ih]
    simp [advance, step, drift, Move.displacement, Tape.write_same, Nat.cast_add]

theorem drift_no_output (n : ℕ) :
    (∀ k, ¬ Halted drift (run drift (input binary drift n) k)) ∧
    ¬ ∃ m, Output drift n m := by
  have hh (k : ℕ) : ¬ Halted drift (run drift (input binary drift n) k) := by
    rw [drift_run]
    simp [Halted, drift]
  refine ⟨hh, ?_⟩
  rintro ⟨m, k, hk, _⟩
  exact hh k hk

theorem drift_visited (n k : ℕ) :
    visited drift (input binary drift n) k = Set.Icc 0 (k : ℤ) ∧
    (visited drift (input binary drift n) k).ncard = k + 1 := by
  have hs : visited drift (input binary drift n) k = Set.Icc 0 (k : ℤ) := by
    ext z
    change (∃ i, i ≤ k ∧ (run drift (input binary drift n) i).head = z) ↔
      0 ≤ z ∧ z ≤ (k : ℤ)
    simp only [drift_run]
    constructor
    · rintro ⟨i, hi, rfl⟩
      constructor <;> omega
    · rintro ⟨hz, hk⟩
      refine ⟨z.toNat, ?_, ?_⟩ <;> omega
  refine ⟨hs, ?_⟩
  rw [hs, Set.ncard_Icc, Int.card_Icc]
  omega

theorem drift_unbounded (n : ℕ) :
    ¬ ∃ s : Set ℤ, s.Finite ∧ ∀ k, (run drift (input binary drift n) k).head ∈ s := by
  rintro ⟨s, hs, hk⟩
  have hsub : Set.range (fun k : ℕ => (k : ℤ)) ⊆ s := by
    rintro z ⟨k, rfl⟩
    simpa only [drift_run] using hk k
  have hi : Function.Injective (fun k : ℕ => (k : ℤ)) := by
    intro a b h
    exact Int.ofNat_inj.mp h
  exact (Set.infinite_range_of_injective hi) (hs.subset hsub)

def stayLoop : Machine binary Unit where
  initial := ()
  table _ a := some ((), a, .stay)

theorem stayLoop_step (C : Config binary Unit) : Step stayLoop C C := by
  rcases C with ⟨q, h, t⟩
  cases q
  simp [Step, step, stayLoop, Move.displacement, Tape.write_same]

theorem stayLoop_run (C : Config binary Unit) (k : ℕ) :
    run stayLoop C k = C ∧ ¬ Halted stayLoop (run stayLoop C k) := by
  have hr : run stayLoop C k = C := by
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [run, ih]
      have hs := stayLoop_step C
      change (step stayLoop C).getD C = C
      rw [hs]
      rfl
  refine ⟨hr, ?_⟩
  rw [hr]
  simp [Halted, stayLoop]

theorem stayLoop_visited (C : Config binary Unit) (k : ℕ) :
    visited stayLoop C k = {C.head} := by
  ext z
  change (∃ i, i ≤ k ∧ (run stayLoop C i).head = z) ↔ z = C.head
  simp only [(stayLoop_run C _).1]
  constructor
  · rintro ⟨i, _, hz⟩
    exact hz.symm
  · intro hz
    exact ⟨0, Nat.zero_le _, hz.symm⟩

theorem stayLoop_blank :
    (∀ k, readout binary (run stayLoop (input binary stayLoop 0) k) = 0) ∧
    ¬ ∃ m, Output stayLoop 0 m := by
  refine ⟨?_, ?_⟩
  · intro k
    rw [(stayLoop_run (input binary stayLoop 0) k).1]
    exact input_readout binary stayLoop 0
  · rintro ⟨m, k, hk, _⟩
    exact (stayLoop_run (input binary stayLoop 0) k).2 hk

end Lemmatheca.Entry.TuringMachines
