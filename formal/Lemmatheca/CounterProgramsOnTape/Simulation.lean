import Lemmatheca.CounterProgramsOnTape.Macros

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

omit [Fintype L] in
private theorem step_advance (P : Program k L) (S : Config k L) (h : ¬ Halted P S) :
    Step P S (advance P S) := by
  cases hs : step P S with
  | none => exact (h ((halted_iff_step_none P S).mpr hs)).elim
  | some U => simp [Step, advance, hs]

omit [Fintype L] in
private theorem instruction_pos (P : Program k L) (S : Config k L) (h : ¬ Halted P S) :
    0 < instructionLength P S := by
  cases hp : P.code S.pc with
  | inc r q => simp [instructionLength, hp]
  | dec r qp qz => simp [instructionLength, hp]; split_ifs <;> omega
  | halt => exact (h hp).elim

def boundaryClock (P : Program k L) (i : Fin k) (n : ℕ) : ℕ → ℕ
  | 0 => 1
  | j + 1 => boundaryClock P i n j + instructionLength P (run P (input P i n) j)

theorem boundary_clock_simulation (P : Program k L) (i o : Fin k) (n j : ℕ) :
    TuringMachines.run (compiled P i o)
      (TuringMachines.input (alphabet i) (compiled P i o) n) (boundaryClock P i n j) =
      boundary i (run P (input P i n) j) := by
  induction j with
  | zero =>
    have hb := boot_correct P i o n
    change TuringMachines.step (compiled P i o)
      (TuringMachines.input (alphabet i) (compiled P i o) n) = some (boundary i (input P i n)) at hb
    change TuringMachines.advance (compiled P i o)
      (TuringMachines.input (alphabet i) (compiled P i o) n) = boundary i (input P i n)
    simp only [TuringMachines.advance, hb, Option.getD_some]
  | succ j ih =>
    rw [boundaryClock, native_run_add, ih]
    by_cases hj : Halted P (run P (input P i n) j)
    · have he : instructionLength P (run P (input P i n) j) = 0 := by
        simp [instructionLength, show P.code (run P (input P i n) j).pc = .halt from hj]
      rw [he, TuringMachines.run]
      congr 1
      exact (run_halted_add P (input P i n) j 1 hj).symm
    · obtain ⟨r, _, hm⟩ := instruction_simulation P i o _ _ (step_advance P _ hj)
      exact hm.2.1


omit [Fintype L] in
theorem clock_nonhalting [Fintype L] (P : Program k L) (i : Fin k) (n : ℕ)
    (h : ∀ j, ¬ Halted P (run P (input P i n) j)) :
    StrictMono (boundaryClock P i n) ∧
      (∀ j, j + 1 ≤ boundaryClock P i n j) ∧
      ∀ t, ∃ j, t < boundaryClock P i n j := by
  have hs : StrictMono (boundaryClock P i n) := by
    apply strictMono_nat_of_lt_succ
    intro j
    have hp := instruction_pos P _ (h j)
    simp only [boundaryClock]
    omega
  have hb : ∀ j, j + 1 ≤ boundaryClock P i n j := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih =>
      have hh := hs (Nat.lt_succ_self j)
      change boundaryClock P i n j < boundaryClock P i n (j + 1) at hh
      change j + 1 + 1 ≤ boundaryClock P i n (j + 1)
      omega
  exact ⟨hs, hb, fun t => ⟨t, by have := hb t; omega⟩⟩


private theorem native_prefix (P : Program k L) (i o : Fin k) (n j : ℕ)
    (hprev : ∀ a < j, ¬ Halted P (run P (input P i n) a)) :
    ∀ t < boundaryClock P i n j, ¬ TuringMachines.Halted (compiled P i o)
      (TuringMachines.run (compiled P i o)
        (TuringMachines.input (alphabet i) (compiled P i o) n) t) := by
  induction j with
  | zero =>
    intro t ht
    have he : t = 0 := by simp only [boundaryClock] at ht; omega
    rw [he, TuringMachines.run, halted_iff_final]
    simp [TuringMachines.input, compiled]
  | succ j ih =>
    intro t ht
    by_cases hlt : t < boundaryClock P i n j
    · exact ih (fun a ha => hprev a (by omega)) t hlt
    · have hstep := step_advance P _ (hprev j (by omega))
      obtain ⟨r, _, hm⟩ := instruction_simulation P i o _ _ hstep
      have hd : t - boundaryClock P i n j ≤ instructionLength P (run P (input P i n) j) := by
        simp only [boundaryClock] at ht
        omega
      have hn := (hm.2.2.2 (t - boundaryClock P i n j) hd).1
      rw [show t = boundaryClock P i n j + (t - boundaryClock P i n j) by omega,
        native_run_add, boundary_clock_simulation]
      exact fun hh => hn ((halted_iff_final P i o _).mp hh)

private theorem native_finish (P : Program k L) (i o : Fin k) (n j : ℕ)
    (hj : Halted P (run P (input P i n) j)) :
    TuringMachines.run (compiled P i o)
      (TuringMachines.input (alphabet i) (compiled P i o) n)
      (boundaryClock P i n j + 2 * maxRegister (run P (input P i n) j).regs + 2) =
      finalConfig i o (run P (input P i n) j).regs := by
  rw [show boundaryClock P i n j + 2 * maxRegister (run P (input P i n) j).regs + 2 =
    boundaryClock P i n j + (2 * maxRegister (run P (input P i n) j).regs + 2) by omega,
    native_run_add, boundary_clock_simulation]
  exact (cleanup_correct P i o _ hj).2.1

private theorem final_halted (P : Program k L) (i o : Fin k) (R : Registers k) :
    TuringMachines.Halted (compiled P i o) (finalConfig i o R : NativeConfig k L i) := by
  rw [halted_iff_final]
  rfl

private theorem final_readout (P : Program k L) (i o : Fin k) (R : Registers k) :
    TuringMachines.readout (alphabet i) (finalConfig i o R : NativeConfig k L i) = R o := by
  simpa only [TuringMachines.readout, TuringMachines.input, finalConfig] using
    TuringMachines.input_readout (alphabet i) (compiled P i o) (R o)

theorem first_halt_simulation (P : Program k L) (i o : Fin k) (n j : ℕ)
    (hj : Halted P (run P (input P i n) j))
    (hprev : ∀ a < j, ¬ Halted P (run P (input P i n) a)) :
    let R := (run P (input P i n) j).regs
    let t := boundaryClock P i n j + 2 * maxRegister R + 2
    TuringMachines.FirstHaltingTime (compiled P i o)
      (TuringMachines.input (alphabet i) (compiled P i o) n) t ∧
    TuringMachines.run (compiled P i o)
      (TuringMachines.input (alphabet i) (compiled P i o) n) t =
      finalConfig i o R := by
  dsimp only
  have hend := native_finish P i o n j hj
  refine ⟨⟨?_, ?_⟩, hend⟩
  · change TuringMachines.Halted _ _
    rw [hend]
    exact final_halted P i o _
  · intro t ht
    change ¬ TuringMachines.Halted _ _
    by_cases hlt : t < boundaryClock P i n j
    · exact native_prefix P i o n j hprev t hlt
    · have hc := cleanup_correct P i o _ hj
      have hd : t - boundaryClock P i n j < 2 * maxRegister (run P (input P i n) j).regs + 2 := by omega
      have hn := hc.2.2.2.1 (t - boundaryClock P i n j) hd
      rw [show t = boundaryClock P i n j + (t - boundaryClock P i n j) by omega,
        native_run_add, boundary_clock_simulation]
      exact fun hh => hn ((halted_iff_final P i o _).mp hh)


theorem divergence_simulation (P : Program k L) (i o : Fin k) (n : ℕ) :
    (∀ j, ¬ Halted P (run P (input P i n) j)) ↔
      ∀ t, ¬ TuringMachines.Halted (compiled P i o)
        (TuringMachines.run (compiled P i o)
          (TuringMachines.input (alphabet i) (compiled P i o) n) t) := by
  constructor
  · intro h t
    obtain ⟨j, hj⟩ := (clock_nonhalting P i n h).2.2 t
    exact native_prefix P i o n j (fun a _ => h a) t hj
  · intro h j hj
    have he := native_finish P i o n j hj
    have hh := h (boundaryClock P i n j + 2 * maxRegister (run P (input P i n) j).regs + 2)
    rw [he] at hh
    exact hh (final_halted P i o _)


theorem output_simulation (P : Program k L) (i o : Fin k) (n m : ℕ) :
    TuringMachines.Output (compiled P i o) n m ↔ Output P i o n m := by
  classical
  constructor
  · rintro ⟨t, ht, hm⟩
    have hex : ∃ j, Halted P (run P (input P i n) j) := by
      by_contra hn
      have hcounter : ∀ j, ¬ Halted P (run P (input P i n) j) := by simpa using hn
      exact ((divergence_simulation P i o n).mp hcounter t) ht
    obtain ⟨j, hj⟩ := hex
    have he := native_finish P i o n j hj
    have hf : TuringMachines.Halted (compiled P i o)
        (TuringMachines.run (compiled P i o) (TuringMachines.input (alphabet i) (compiled P i o) n)
          (boundaryClock P i n j + 2 * maxRegister (run P (input P i n) j).regs + 2)) := by
      rw [he]; exact final_halted P i o _
    have heq := TuringMachines.halting_configs_equal (compiled P i o)
      (TuringMachines.input (alphabet i) (compiled P i o) n) t _ ht hf
    rw [heq, he, final_readout P i o] at hm
    exact ⟨j, hj, hm⟩
  · rintro ⟨j, hj, hm⟩
    refine ⟨boundaryClock P i n j + 2 * maxRegister (run P (input P i n) j).regs + 2, ?_, ?_⟩
    · rw [native_finish P i o n j hj]; exact final_halted P i o _
    · rw [native_finish P i o n j hj, final_readout P i o]
      exact hm


theorem computed_simulation (P : Program k L) (i o : Fin k) (n : ℕ) :
    TuringMachines.computed (compiled P i o) n = computed P i o n := by
  apply Option.ext
  intro m
  simp only [TuringMachines.computed_spec, computed_spec,
    output_simulation]


theorem eval_simulation (P : Program k L) (i o : Fin k) :
    (fun n => Part.ofOption (TuringMachines.computed (compiled P i o) n)) =
      eval P i o := by
  funext n
  simp only [computed_simulation, eval, evalFrom, computed]


end Lemmatheca.ComputabilityTheory.CounterPrograms
