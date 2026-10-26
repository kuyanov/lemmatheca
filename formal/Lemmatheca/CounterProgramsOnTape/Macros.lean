import Lemmatheca.CounterProgramsOnTape.Compiler

namespace Lemmatheca.ComputabilityTheory.CounterPrograms

variable {k : ℕ} {L : Type*} [Fintype L]

private theorem native_run_add (P : Program k L) (i o : Fin k)
    (C : NativeConfig k L i) (a b : ℕ) :
    TuringMachines.run (compiled P i o) C (a + b) =
      TuringMachines.run (compiled P i o) (TuringMachines.run (compiled P i o) C a) b := by
  induction b with
  | zero => rfl
  | succ b ih =>
    change TuringMachines.advance _ (TuringMachines.run _ C (a + b)) =
      TuringMachines.advance _ (TuringMachines.run _ (TuringMachines.run _ C a) b)
    exact congrArg (TuringMachines.advance (compiled P i o)) ih

private theorem boundary_frame (i r : Fin k) (R : Registers k) :
    Frame R r (boundaryTape i R) := by
  intro z
  exact ⟨rfl, fun _ _ => rfl⟩

private theorem updated_frame (i r : Fin k) (R : Registers k) (n : ℕ) :
    Frame R r (boundaryTape i (updateRegister R r n)) := by
  intro z
  refine ⟨rfl, ?_⟩
  intro s hs
  simp [boundaryTape, boundaryCell, updateRegister, hs]

private theorem actual_of_not_final (P : Program k L) (i o : Fin k)
    (C : NativeConfig k L i) (N : ℕ)
    (h : ∀ j < N, (TuringMachines.run (compiled P i o) C j).state ≠ .final) :
    TuringMachines.ActualRun (compiled P i o) N
      (fun j => TuringMachines.run (compiled P i o) C j.val) := by
  apply TuringMachines.run_actual_prefix
  intro j hj hh
  exact h j hj ((halted_iff_final P i o _).mp hh)

private theorem advance_row (P : Program k L) (i o : Fin k)
    {s q : Control k L} {h : ℤ}
    {t : TuringMachines.Tape (Symbol k) (alphabet i).blank}
    {b : Symbol k} {m : TuringMachines.Move}
    (ht : table P i o s (t h) = some (q, b, m)) :
    TuringMachines.advance (compiled P i o) (⟨s, h, t⟩ : NativeConfig k L i) =
      ⟨q, h + m.displacement, t.write h b⟩ := by
  change (Option.map _ (table P i o s (t h))).getD _ = _
  rw [ht]
  rfl

private theorem advance_same_row (P : Program k L) (i o : Fin k)
    {s q : Control k L} {h : ℤ}
    {t : TuringMachines.Tape (Symbol k) (alphabet i).blank} {m : TuringMachines.Move}
    (ht : table P i o s (t h) = some (q, t h, m)) :
    TuringMachines.advance (compiled P i o) (⟨s, h, t⟩ : NativeConfig k L i) =
      ⟨q, h + m.displacement, t⟩ := by
  simpa only [TuringMachines.Tape.write_same] using advance_row P i o ht

private theorem back_scan (P : Program k L) (i o : Fin k) (q : L)
    (t : TuringMachines.Tape (Symbol k) (alphabet i).blank)
    (ht : ∀ z, (t z).1 = decide (z = 0)) (N j : ℕ) (hj : j ≤ N) :
    TuringMachines.run (compiled P i o) (⟨.back q, (N : ℤ), t⟩ : NativeConfig k L i) j =
      ⟨.back q, (N : ℤ) - (j : ℤ), t⟩ := by
  induction j with
  | zero => simp [TuringMachines.run]
  | succ j ih =>
    have hj' : j ≤ N := by omega
    have hn : (N : ℤ) - (j : ℤ) ≠ 0 := by omega
    rw [TuringMachines.run, ih hj']
    have hb : (t ((N : ℤ) - (j : ℤ))).1 = false := by simp [ht, hn]
    simp [TuringMachines.advance, TuringMachines.step, compiled, table, hb,
      TuringMachines.Move.displacement, TuringMachines.Tape.write_same]
    ring

private theorem back_finish (P : Program k L) (i o : Fin k) (q : L)
    (t : TuringMachines.Tape (Symbol k) (alphabet i).blank)
    (ht : ∀ z, (t z).1 = decide (z = 0)) (N : ℕ) :
    TuringMachines.run (compiled P i o) (⟨.back q, (N : ℤ), t⟩ : NativeConfig k L i) (N + 1) =
      ⟨.run q, 0, t⟩ := by
  rw [TuringMachines.run, back_scan P i o q t ht N N le_rfl]
  have hb : (t 0).1 = true := by simp [ht]
  simp [TuringMachines.advance, TuringMachines.step, compiled, table, hb,
    TuringMachines.Move.displacement, TuringMachines.Tape.write_same]

theorem increment_scan (P : Program k L) (i o r : Fin k) (p q : L) (R : Registers k)
    (hp : P.code p = .inc r q) (j : ℕ) (hj : j ≤ R r) :
    TuringMachines.run (compiled P i o) (boundary i ⟨p, R⟩) (1 + j) =
      (⟨.inc r q, (j : ℤ), boundaryTape i R⟩ : NativeConfig k L i) := by
  induction j with
  | zero =>
    simp [TuringMachines.run, TuringMachines.advance, TuringMachines.step, compiled,
      table, boundary, hp, TuringMachines.Move.displacement, TuringMachines.Tape.write_same]
  | succ j ih =>
    have hj' : j ≤ R r := by omega
    have hb : (boundaryTape i R (j : ℤ)).2 r = true := by
      simp [boundaryTape, boundaryCell]
      omega
    rw [show 1 + (j + 1) = (1 + j) + 1 by omega, TuringMachines.run, ih hj']
    simp [TuringMachines.advance, TuringMachines.step, compiled, table, hb,
      TuringMachines.Move.displacement, TuringMachines.Tape.write_same, Nat.cast_add]


theorem increment_back (P : Program k L) (i o r : Fin k) (p q : L) (R : Registers k)
    (hp : P.code p = .inc r q) (hn : 0 < R r) (j : ℕ) (hj : j < R r) :
    TuringMachines.run (compiled P i o) (boundary i ⟨p, R⟩) (R r + 2 + j) =
      (⟨.back q, (R r : ℤ) - 1 - (j : ℤ),
        boundaryTape i (updateRegister R r (R r + 1))⟩ : NativeConfig k L i) := by
  have hstart := increment_scan P i o r p q R hp (R r) le_rfl
  have hb : (boundaryTape i R (R r : ℤ)).2 r = false := by
    simp [boundaryTape, boundaryCell]
  have ho : (boundaryTape i R (R r : ℤ)).1 = false := by
    simp [boundaryTape, boundaryCell, Nat.ne_of_gt hn]
  have hbase : TuringMachines.run (compiled P i o) (boundary i ⟨p, R⟩) (R r + 2) =
      (⟨.back q, (R r : ℤ) - 1,
        boundaryTape i (updateRegister R r (R r + 1))⟩ : NativeConfig k L i) := by
    rw [show R r + 2 = (1 + R r) + 1 by omega, TuringMachines.run, hstart]
    rw [advance_row P i o (q := .back q) (b := setBit (boundaryCell R (R r)) r true) (m := .left) (by simp [table, hb, ho]; rfl)]
    simp only [TuringMachines.Move.displacement, TuringMachines.Config.mk.injEq, true_and]
    exact ⟨by omega, boundary_write_inc i r R⟩
  rw [native_run_add, hbase]
  have hncast : ((R r - 1 : ℕ) : ℤ) = (R r : ℤ) - 1 := by omega
  have hh := back_scan P i o q (boundaryTape i (updateRegister R r (R r + 1)))
    (fun _ => rfl) (R r - 1) j (by omega)
  simpa only [hncast] using hh


theorem increment_correct (P : Program k L) (i o r : Fin k) (p q : L) (R : Registers k)
    (hp : P.code p = .inc r q) :
    MacroTrace P i o ⟨p, R⟩ ⟨q, updateRegister R r (R r + 1)⟩ r (2 * R r + 2) := by
  have hend : TuringMachines.run (compiled P i o) (boundary i ⟨p, R⟩) (2 * R r + 2) =
      boundary i ⟨q, updateRegister R r (R r + 1)⟩ := by
    by_cases hn : R r = 0
    · have hs := increment_scan P i o r p q R hp 0 (by omega)
      rw [show 2 * R r + 2 = (1 + 0) + 1 by omega, TuringMachines.run, hs]
      have hb : (boundaryTape i R 0).2 r = false := by simp [boundaryTape, boundaryCell, hn]
      have ho : (boundaryTape i R 0).1 = true := by simp [boundaryTape, boundaryCell]
      rw [advance_row P i o (q := .run q) (b := setBit (boundaryCell R 0) r true) (m := .stay) (by simp [table, hb, ho]; rfl)]
      simp only [TuringMachines.Move.displacement, add_zero, boundary,
        TuringMachines.Config.mk.injEq, true_and]
      exact ⟨rfl, by simpa only [hn, Nat.cast_zero] using boundary_write_inc i r R⟩
    · have hpos : 0 < R r := by omega
      have hs := increment_back P i o r p q R hp hpos (R r - 1) (by omega)
      rw [show 2 * R r + 2 = (R r + 2 + (R r - 1)) + 1 by omega,
        TuringMachines.run, hs]
      have he : (R r : ℤ) - 1 - ((R r - 1 : ℕ) : ℤ) = 0 := by omega
      rw [he]
      have hb : (boundaryTape i (updateRegister R r (R r + 1)) 0).1 = true := by rfl
      rw [advance_same_row P i o (q := .run q) (m := .stay) (by simp [table, hb])]
      rfl
  have htrace : ∀ j ≤ 2 * R r + 2,
      let C := TuringMachines.run (compiled P i o) (boundary i ⟨p, R⟩) j
      C.state ≠ .final ∧ 0 ≤ C.head ∧ Frame R r C.tape := by
    intro j hj
    dsimp only
    by_cases hz : j = 0
    · subst j
      exact ⟨by simp [TuringMachines.run, boundary], le_refl 0, boundary_frame i r R⟩
    by_cases he : j = 2 * R r + 2
    · rw [he, hend]
      exact ⟨by simp [boundary], le_refl 0, updated_frame i r R _⟩
    by_cases hf : j ≤ R r + 1
    · have hs := increment_scan P i o r p q R hp (j - 1) (by omega)
      rw [show j = 1 + (j - 1) by omega, hs]
      exact ⟨by simp, by positivity, boundary_frame i r R⟩
    · have hs := increment_back P i o r p q R hp (by omega) (j - (R r + 2)) (by omega)
      rw [show j = R r + 2 + (j - (R r + 2)) by omega, hs]
      exact ⟨by simp, by change 0 ≤ (R r : ℤ) - 1 - ((j - (R r + 2) : ℕ) : ℤ); omega, updated_frame i r R _⟩
  exact ⟨by omega, hend, actual_of_not_final P i o _ _
    (fun j hj => (htrace j (by omega)).1), htrace⟩


theorem decrement_scan (P : Program k L) (i o r : Fin k) (p qp qz : L) (R : Registers k)
    (hp : P.code p = .dec r qp qz) (j : ℕ) (hj : 1 ≤ j ∧ j ≤ R r) :
    TuringMachines.run (compiled P i o) (boundary i ⟨p, R⟩) j =
      (⟨.dec r qp, (j : ℤ), boundaryTape i R⟩ : NativeConfig k L i) := by
  induction j with
  | zero => omega
  | succ j ih =>
    by_cases hz : j = 0
    · subst j
      have hb : (boundaryTape i R 0).2 r = true := by
        simp [boundaryTape, boundaryCell]
        omega
      simp [TuringMachines.run, TuringMachines.advance, TuringMachines.step,
        compiled, table, boundary, hp, hb, TuringMachines.Move.displacement,
        TuringMachines.Tape.write_same]
    · have hb : (boundaryTape i R (j : ℤ)).2 r = true := by
        simp [boundaryTape, boundaryCell]
        omega
      rw [TuringMachines.run, ih ⟨by omega, by omega⟩]
      simp [TuringMachines.advance, TuringMachines.step, compiled, table, hb,
        TuringMachines.Move.displacement, TuringMachines.Tape.write_same, Nat.cast_add]


theorem decrement_erase (P : Program k L) (i o r : Fin k) (p qp qz : L) (R : Registers k)
    (hp : P.code p = .dec r qp qz) (hn : 0 < R r) :
    TuringMachines.run (compiled P i o) (boundary i ⟨p, R⟩) (R r + 1) =
      (⟨.erase r qp, (R r : ℤ) - 1, boundaryTape i R⟩ : NativeConfig k L i) := by
  rw [TuringMachines.run, decrement_scan P i o r p qp qz R hp (R r) ⟨hn, le_rfl⟩]
  have hb : (boundaryTape i R (R r : ℤ)).2 r = false := by simp [boundaryTape, boundaryCell]
  simp [TuringMachines.advance, TuringMachines.step, compiled, table, hb,
    TuringMachines.Move.displacement, TuringMachines.Tape.write_same]
  ring


theorem decrement_back (P : Program k L) (i o r : Fin k) (p qp qz : L) (R : Registers k)
    (hp : P.code p = .dec r qp qz) (hn : 1 < R r) (j : ℕ) (hj : j < R r - 1) :
    TuringMachines.run (compiled P i o) (boundary i ⟨p, R⟩) (R r + 2 + j) =
      (⟨.back qp, (R r : ℤ) - 2 - (j : ℤ),
        boundaryTape i (updateRegister R r (R r - 1))⟩ : NativeConfig k L i) := by
  have hstart := decrement_erase P i o r p qp qz R hp (by omega)
  have ho : (boundaryTape i R ((R r : ℤ) - 1)).1 = false := by
    simp [boundaryTape, boundaryCell]
    omega
  have hbase : TuringMachines.run (compiled P i o) (boundary i ⟨p, R⟩) (R r + 2) =
      (⟨.back qp, (R r : ℤ) - 2,
        boundaryTape i (updateRegister R r (R r - 1))⟩ : NativeConfig k L i) := by
    rw [show R r + 2 = (R r + 1) + 1 by omega, TuringMachines.run, hstart]
    rw [advance_row P i o (q := .back qp) (b := setBit (boundaryCell R ((R r : ℤ) - 1)) r false) (m := .left) (by simp [table, ho]; rfl)]
    simp only [TuringMachines.Move.displacement, TuringMachines.Config.mk.injEq, true_and]
    exact ⟨by omega, boundary_write_dec i r R (by omega)⟩
  rw [native_run_add, hbase]
  have hncast : ((R r - 2 : ℕ) : ℤ) = (R r : ℤ) - 2 := by omega
  have hh := back_scan P i o qp (boundaryTape i (updateRegister R r (R r - 1)))
    (fun _ => rfl) (R r - 2) j (by omega)
  simpa only [hncast] using hh


theorem decrement_zero (P : Program k L) (i o r : Fin k) (p qp qz : L) (R : Registers k)
    (hp : P.code p = .dec r qp qz) (hn : R r = 0) :
    MacroTrace P i o ⟨p, R⟩ ⟨qz, R⟩ r 1 := by
  have hb : (boundaryTape i R 0).2 r = false := by simp [boundaryTape, boundaryCell, hn]
  have hend : TuringMachines.run (compiled P i o) (boundary i ⟨p, R⟩) 1 = boundary i ⟨qz, R⟩ := by
    simp [TuringMachines.run, TuringMachines.advance, TuringMachines.step, compiled,
      table, boundary, hp, hb, TuringMachines.Move.displacement, TuringMachines.Tape.write_same]
  have ht : ∀ j ≤ 1, let C := TuringMachines.run (compiled P i o) (boundary i ⟨p, R⟩) j
      C.state ≠ .final ∧ 0 ≤ C.head ∧ Frame R r C.tape := by
    intro j hj
    rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
    · exact ⟨by simp [TuringMachines.run, boundary], le_refl 0, boundary_frame i r R⟩
    · dsimp only; rw [hend]
      exact ⟨by simp [boundary], le_refl 0, boundary_frame i r R⟩
  exact ⟨by omega, hend, actual_of_not_final P i o _ _
    (fun j hj => (ht j (by omega)).1), ht⟩


theorem decrement_positive (P : Program k L) (i o r : Fin k) (p qp qz : L) (R : Registers k)
    (hp : P.code p = .dec r qp qz) (hn : 0 < R r) :
    MacroTrace P i o ⟨p, R⟩ ⟨qp, updateRegister R r (R r - 1)⟩ r (2 * R r + 1) := by
  have hend : TuringMachines.run (compiled P i o) (boundary i ⟨p, R⟩) (2 * R r + 1) =
      boundary i ⟨qp, updateRegister R r (R r - 1)⟩ := by
    by_cases he : R r = 1
    · have hs := decrement_erase P i o r p qp qz R hp hn
      rw [show 2 * R r + 1 = (R r + 1) + 1 by omega, TuringMachines.run, hs]
      have hz : (R r : ℤ) - 1 = 0 := by omega
      rw [hz]
      have ho : (boundaryTape i R 0).1 = true := by rfl
      rw [advance_row P i o (q := .run qp) (b := setBit (boundaryCell R 0) r false)
        (m := .stay) (by simp [table, ho]; rfl)]
      simp only [TuringMachines.Move.displacement, zero_add, boundary,
        TuringMachines.Config.mk.injEq, true_and]
      simpa only [hz] using boundary_write_dec i r R hn
    · have hs := decrement_back P i o r p qp qz R hp (by omega) (R r - 2) (by omega)
      rw [show 2 * R r + 1 = (R r + 2 + (R r - 2)) + 1 by omega,
        TuringMachines.run, hs]
      have hz : (R r : ℤ) - 2 - ((R r - 2 : ℕ) : ℤ) = 0 := by omega
      rw [hz]
      have ho : (boundaryTape i (updateRegister R r (R r - 1)) 0).1 = true := by rfl
      rw [advance_same_row P i o (q := .run qp) (m := .stay) (by simp [table, ho])]
      rfl
  have ht : ∀ j ≤ 2 * R r + 1,
      let C := TuringMachines.run (compiled P i o) (boundary i ⟨p, R⟩) j
      C.state ≠ .final ∧ 0 ≤ C.head ∧ Frame R r C.tape := by
    intro j hj
    dsimp only
    by_cases hz : j = 0
    · subst j
      exact ⟨by simp [TuringMachines.run, boundary], le_refl 0, boundary_frame i r R⟩
    by_cases he : j = 2 * R r + 1
    · rw [he, hend]
      exact ⟨by simp [boundary], le_refl 0, updated_frame i r R _⟩
    by_cases hf : j ≤ R r
    · rw [decrement_scan P i o r p qp qz R hp j ⟨by omega, hf⟩]
      exact ⟨by simp, by positivity, boundary_frame i r R⟩
    by_cases hg : j = R r + 1
    · rw [hg, decrement_erase P i o r p qp qz R hp hn]
      exact ⟨by simp, by change 0 ≤ (R r : ℤ) - 1; omega, boundary_frame i r R⟩
    · have hs := decrement_back P i o r p qp qz R hp (by omega) (j - (R r + 2)) (by omega)
      rw [show j = R r + 2 + (j - (R r + 2)) by omega, hs]
      exact ⟨by simp, by change 0 ≤ (R r : ℤ) - 2 - ((j - (R r + 2) : ℕ) : ℤ); omega,
        updated_frame i r R _⟩
  exact ⟨by omega, hend, actual_of_not_final P i o _ _
    (fun j hj => (ht j (by omega)).1), ht⟩


theorem instruction_simulation (P : Program k L) (i o : Fin k) (S U : Config k L)
    (hSU : Step P S U) :
    ∃ r, instructionRegister P S = some r ∧
      MacroTrace P i o S U r (instructionLength P S) := by
  rcases S with ⟨p, R⟩
  cases hp : P.code p with
  | inc r q =>
    change step P ⟨p, R⟩ = some U at hSU
    simp only [step, hp] at hSU
    cases hSU
    exact ⟨r, by simp [instructionRegister, hp],
      by simpa only [instructionLength, hp] using increment_correct P i o r p q R hp⟩
  | dec r qp qz =>
    by_cases hn : R r = 0
    · change step P ⟨p, R⟩ = some U at hSU
      simp only [step, hp, hn, ite_true, Option.some.injEq] at hSU
      subst U
      exact ⟨r, by simp [instructionRegister, hp],
        by simpa only [instructionLength, hp, hn, ite_true] using decrement_zero P i o r p qp qz R hp hn⟩
    · change step P ⟨p, R⟩ = some U at hSU
      simp only [step, hp, hn, ite_false, Option.some.injEq] at hSU
      subst U
      exact ⟨r, by simp [instructionRegister, hp],
        by simpa only [instructionLength, hp, hn, ite_false] using decrement_positive P i o r p qp qz R hp (by omega)⟩
  | halt => simp [Step, step, hp] at hSU


theorem cleanup_scan (P : Program k L) (i o : Fin k) (p : L) (R : Registers k)
    (hp : P.code p = .halt) (j : ℕ) (hj : j ≤ maxRegister R) :
    TuringMachines.run (compiled P i o) (boundary i ⟨p, R⟩) (1 + j) =
      (⟨.clean, (j : ℤ), boundaryTape i R⟩ : NativeConfig k L i) := by
  induction j with
  | zero =>
    simp [TuringMachines.run, TuringMachines.advance, TuringMachines.step,
      compiled, table, boundary, hp, TuringMachines.Move.displacement, TuringMachines.Tape.write_same]
  | succ j ih =>
    have hj' : j ≤ maxRegister R := by omega
    obtain ⟨_, r, hr⟩ := maxRegister_spec (by have := i.isLt; omega : 0 < k) R
    have hb : anyBit (boundaryTape i R (j : ℤ)) = true := by
      simp only [anyBit, decide_eq_true_eq]
      refine ⟨r, ?_⟩
      simp [boundaryTape, boundaryCell]
      omega
    rw [show 1 + (j + 1) = (1 + j) + 1 by omega, TuringMachines.run, ih hj']
    simp [TuringMachines.advance, TuringMachines.step, compiled, table, hb,
      TuringMachines.Move.displacement, TuringMachines.Tape.write_same, Nat.cast_add]


private theorem tape_ext (i : Fin k)
    (t u : TuringMachines.Tape (Symbol k) (alphabet i).blank)
    (h : ∀ z, t z = u z) : t = u := by
  cases t; cases u; congr; funext z; exact h z

private theorem projection_blank (i o : Fin k) : outputProjection i o blank = blank := by
  apply Prod.ext
  · rfl
  · funext r; simp [outputProjection, blank]

private theorem boundary_right_blank (i : Fin k) (R : Registers k) (z : ℤ)
    (hz : 0 < z) (hM : (maxRegister R : ℤ) ≤ z) : boundaryCell R z = blank := by
  have hle := (maxRegister_spec (by have := i.isLt; omega) R).1
  apply Prod.ext
  · simp [boundaryCell, blank, ne_of_gt hz]
  · funext r
    have := hle r
    simp [boundaryCell, blank]
    omega

private theorem cleaned_start (i o : Fin k) (R : Registers k) (hM : 0 < maxRegister R) :
    cleanedAboveTape i o R ((maxRegister R : ℤ) - 1) = boundaryTape i R := by
  apply tape_ext i
  intro z
  change (if (maxRegister R : ℤ) - 1 < z then outputProjection i o (boundaryCell R z)
    else boundaryCell R z) = boundaryCell R z
  by_cases hz : (maxRegister R : ℤ) - 1 < z
  · rw [ite_eq_left hz, boundary_right_blank i R z (by omega) (by omega), projection_blank]
  · rw [ite_eq_right hz]

private theorem cleaned_write (i o : Fin k) (R : Registers k) (h : ℤ) :
    (cleanedAboveTape i o R h).write h (outputProjection i o (boundaryCell R h)) =
      cleanedAboveTape i o R (h - 1) := by
  classical
  apply tape_ext i
  intro z
  change Function.update (cleanedAboveCell i o R h) h
    (outputProjection i o (boundaryCell R h)) z = cleanedAboveCell i o R (h - 1) z
  rw [Function.update_apply]
  by_cases hz : z = h
  · subst z; simp [cleanedAboveCell]
  · have hc : h < z ↔ h - 1 < z := by omega
    simp [hz, cleanedAboveCell, hc]

private theorem cleaned_full (i o : Fin k) (R : Registers k) :
    cleanedAboveTape i o R (-1) = TuringMachines.unaryTape (alphabet i) (R o) := by
  apply tape_ext i
  intro z
  change cleanedAboveCell i o R (-1) z = _
  rw [← projection_boundary i o R z]
  by_cases hz : -1 < z
  · simp [cleanedAboveCell, hz]
  · have hb : boundaryCell R z = blank := by
      apply Prod.ext
      · simp [boundaryCell, blank]; omega
      · funext r; simp [boundaryCell, blank]; omega
    simp [cleanedAboveCell, hz, hb, projection_blank]

private theorem anyBit_at_max (i : Fin k) (R : Registers k) :
    anyBit (boundaryTape i R (maxRegister R : ℤ)) = false := by
  have hle := (maxRegister_spec (by have := i.isLt; omega) R).1
  simp [anyBit, boundaryTape, boundaryCell]
  intro r
  have := hle r
  omega

theorem cleanup_back (P : Program k L) (i o : Fin k) (p : L) (R : Registers k)
    (hp : P.code p = .halt) (hm : 0 < maxRegister R) (j : ℕ) (hj : j < maxRegister R) :
    TuringMachines.run (compiled P i o) (boundary i ⟨p, R⟩) (maxRegister R + 2 + j) =
      (⟨.cleanBack, (maxRegister R : ℤ) - 1 - (j : ℤ),
        cleanedAboveTape i o R ((maxRegister R : ℤ) - 1 - (j : ℤ))⟩ :
          NativeConfig k L i) := by
  have hstart := cleanup_scan P i o p R hp (maxRegister R) le_rfl
  have hb := anyBit_at_max i R
  have ho : (boundaryTape i R (maxRegister R : ℤ)).1 = false := by
    simp [boundaryTape, boundaryCell, Nat.ne_of_gt hm]
  have hbase : TuringMachines.run (compiled P i o) (boundary i ⟨p, R⟩) (maxRegister R + 2) =
      (⟨.cleanBack, (maxRegister R : ℤ) - 1,
        cleanedAboveTape i o R ((maxRegister R : ℤ) - 1)⟩ : NativeConfig k L i) := by
    rw [show maxRegister R + 2 = (1 + maxRegister R) + 1 by omega,
      TuringMachines.run, hstart]
    rw [advance_same_row P i o (q := .cleanBack) (m := .left) (by simp [table, hb, ho])]
    simp only [TuringMachines.Move.displacement, cleaned_start i o R hm]
    congr 1
  induction j with
  | zero => simpa only [Nat.add_zero, Nat.cast_zero, sub_zero] using hbase
  | succ j ih =>
    have hj' : j < maxRegister R := by omega
    rw [show maxRegister R + 2 + (j + 1) = (maxRegister R + 2 + j) + 1 by omega,
      TuringMachines.run, ih hj']
    have hh : 0 < (maxRegister R : ℤ) - 1 - (j : ℤ) := by omega
    have ho' : (cleanedAboveTape i o R ((maxRegister R : ℤ) - 1 - (j : ℤ))
        ((maxRegister R : ℤ) - 1 - (j : ℤ))).1 = false := by
      simp [cleanedAboveTape, cleanedAboveCell, boundaryCell, ne_of_gt hh]
    rw [advance_row P i o (q := .cleanBack)
      (b := outputProjection i o (boundaryCell R ((maxRegister R : ℤ) - 1 - (j : ℤ))))
      (m := .left) (by simp [table, ho']; simp [cleanedAboveTape, cleanedAboveCell])]
    rw [cleaned_write]
    have he : (maxRegister R : ℤ) - 1 - (j : ℤ) + TuringMachines.Move.left.displacement =
        (maxRegister R : ℤ) - 1 - ((j + 1 : ℕ) : ℤ) := by
      simp [TuringMachines.Move.displacement]; ring
    have he' : (maxRegister R : ℤ) - 1 - (j : ℤ) - 1 =
        (maxRegister R : ℤ) - 1 - ((j + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [he, he']


theorem cleanup_correct (P : Program k L) (i o : Fin k) (S : Config k L)
    (hS : Halted P S) : CleanupTrace P i o S (2 * maxRegister S.regs + 2) := by
  rcases S with ⟨p, R⟩
  change P.code p = .halt at hS
  have hend : TuringMachines.run (compiled P i o) (boundary i ⟨p, R⟩) (2 * maxRegister R + 2) =
      finalConfig i o R := by
    by_cases hm : maxRegister R = 0
    · have hs := cleanup_scan P i o p R hS 0 (by omega)
      rw [show 2 * maxRegister R + 2 = (1 + 0) + 1 by omega, TuringMachines.run, hs]
      have hb : anyBit (boundaryTape i R 0) = false := by
        simpa only [hm, Nat.cast_zero] using anyBit_at_max i R
      have ho : (boundaryTape i R 0).1 = true := by rfl
      rw [advance_row P i o (q := .final) (b := clearOrigin (boundaryCell R 0))
        (m := .stay) (by simp [table, hb, ho]; rfl)]
      have hR : ∀ r, R r = 0 := by
        intro r
        have := (maxRegister_spec (by have := i.isLt; omega) R).1 r
        omega
      have hcell : clearOrigin (boundaryCell R 0) = outputProjection i o (boundaryCell R 0) := by
        apply Prod.ext
        · rfl
        · funext r; simp [clearOrigin, outputProjection, boundaryCell, hR]
      have ht : cleanedAboveTape i o R 0 = boundaryTape i R := by
        apply tape_ext i
        intro z
        change cleanedAboveCell i o R 0 z = boundaryCell R z
        by_cases hz : 0 < z
        · simp [cleanedAboveCell, hz, boundary_right_blank i R z hz (by omega), projection_blank]
        · simp [cleanedAboveCell, hz]
      rw [hcell, ← ht]
      simp only [Nat.cast_zero]
      rw [cleaned_write]
      norm_num only at *
      rw [cleaned_full]
      rfl
    · have hp : 0 < maxRegister R := by omega
      have hs := cleanup_back P i o p R hS hp (maxRegister R - 1) (by omega)
      rw [show 2 * maxRegister R + 2 = (maxRegister R + 2 + (maxRegister R - 1)) + 1 by omega,
        TuringMachines.run, hs]
      have he : (maxRegister R : ℤ) - 1 - ((maxRegister R - 1 : ℕ) : ℤ) = 0 := by omega
      rw [he]
      have ho : (cleanedAboveTape i o R 0 0).1 = true := by rfl
      rw [advance_row P i o (q := .final) (b := outputProjection i o (boundaryCell R 0))
        (m := .stay) (by simp [table, ho]; rfl), cleaned_write]
      norm_num only
      rw [cleaned_full]
      rfl
  have ht : ∀ j < 2 * maxRegister R + 2,
      let C := TuringMachines.run (compiled P i o) (boundary i ⟨p, R⟩) j
      C.state ≠ .final ∧ 0 ≤ C.head := by
    intro j hj
    dsimp only
    by_cases hz : j = 0
    · subst j; simp [TuringMachines.run, boundary]
    by_cases hf : j ≤ maxRegister R + 1
    · have hs := cleanup_scan P i o p R hS (j - 1) (by omega)
      rw [show j = 1 + (j - 1) by omega, hs]
      exact ⟨by simp, by positivity⟩
    · have hs := cleanup_back P i o p R hS (by omega) (j - (maxRegister R + 2)) (by omega)
      rw [show j = maxRegister R + 2 + (j - (maxRegister R + 2)) by omega, hs]
      exact ⟨by simp, by change 0 ≤ (maxRegister R : ℤ) - 1 - ((j - (maxRegister R + 2) : ℕ) : ℤ); omega⟩
  refine ⟨by omega, hend, actual_of_not_final P i o _ _ (fun j hj => (ht j hj).1),
    fun j hj => (ht j hj).1, ?_⟩
  change ∀ j ≤ 2 * maxRegister R + 2,
    0 ≤ (TuringMachines.run (compiled P i o) (boundary i ⟨p, R⟩) j).head
  intro j hj
  by_cases he : j = 2 * maxRegister R + 2
  · rw [he, hend]; exact le_refl 0
  · exact (ht j (by omega)).2


end Lemmatheca.ComputabilityTheory.CounterPrograms
