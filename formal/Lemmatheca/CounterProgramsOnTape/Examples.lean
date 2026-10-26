import Lemmatheca.CounterProgramsOnTape.Simulation

namespace Lemmatheca.Entry.CounterProgramsOnTape

open Lemmatheca.ComputabilityTheory
open CounterPrograms

def twoFile (u v : ℕ) : Registers 2 := fun r => if r = 0 then u else v

def transfer : Program 2 (Fin 3) where
  initial := 0
  code p := match p.val with
    | 0 => .dec 1 1 2
    | 1 => .inc 0 0
    | _ => .halt

private theorem two_update_zero (u v n : ℕ) :
    updateRegister (twoFile u v) 0 n = twoFile n v := by
  funext r; fin_cases r <;> simp [twoFile, updateRegister]

private theorem two_update_one (u v n : ℕ) :
    updateRegister (twoFile u v) 1 n = twoFile u n := by
  funext r; fin_cases r <;> simp [twoFile, updateRegister]

private theorem transfer_pos (u v : ℕ) (hv : 0 < v) :
    advance transfer ⟨0, twoFile u v⟩ = ⟨1, twoFile u (v - 1)⟩ := by
  have h1 : twoFile u v 1 = v := rfl
  simp [advance, step, transfer, h1, Nat.ne_of_gt hv, two_update_one]

private theorem transfer_inc (u v : ℕ) :
    advance transfer ⟨1, twoFile u v⟩ = ⟨0, twoFile (u + 1) v⟩ := by
  have h0 : twoFile u v 0 = u := rfl
  simp [advance, step, transfer, h0, two_update_zero]

private theorem transfer_zero (u : ℕ) :
    advance transfer ⟨0, twoFile u 0⟩ = ⟨2, twoFile u 0⟩ := by
  have h1 : twoFile u 0 1 = 0 := rfl
  simp [advance, step, transfer, h1]

private theorem transfer_input (n : ℕ) : input transfer 1 n = ⟨0, twoFile 0 n⟩ := by
  change (⟨0, inputFile (1 : Fin 2) n⟩ : Config 2 (Fin 3)) = _
  congr 1
  funext r; fin_cases r <;> simp [inputFile, twoFile]

theorem transfer_invariant (u v j : ℕ) (hj : j ≤ v) :
    run transfer ⟨0, twoFile u v⟩ (2 * j) = ⟨0, twoFile (u + j) (v - j)⟩ := by
  induction j with
  | zero => simp [run]
  | succ j ih =>
    rw [show 2 * (j + 1) = 2 * j + 2 by omega, run_add, ih (by omega)]
    change advance transfer (advance transfer ⟨0, twoFile (u + j) (v - j)⟩) = _
    rw [transfer_pos _ _ (by omega), transfer_inc]
    congr 1


theorem transfer_correct (u v : ℕ) :
    run transfer ⟨0, twoFile u v⟩ (2 * v + 1) = ⟨2, twoFile (u + v) 0⟩ ∧
    ∀ j < 2 * v + 1, ¬ Halted transfer (run transfer ⟨0, twoFile u v⟩ j) := by
  constructor
  · rw [run, transfer_invariant u v v le_rfl]
    simpa only [Nat.sub_self] using transfer_zero (u + v)
  · intro j hj
    have hv : j / 2 ≤ v := by omega
    by_cases he : j % 2 = 0
    · rw [show j = 2 * (j / 2) by omega, transfer_invariant u v (j / 2) hv]
      simp [Halted, transfer]
    · rw [show j = 2 * (j / 2) + 1 by omega, run, transfer_invariant u v (j / 2) hv,
        transfer_pos _ _ (by omega)]
      simp [Halted, transfer]


theorem transfer_output (n : ℕ) :
    computed transfer 1 0 n = some n ∧
    TuringMachines.computed (compiled transfer 1 0) n = some n := by
  have hc : computed transfer 1 0 n = some n := by
    apply (computed_spec _ _ _ _ _).mpr
    change OutputFrom transfer (input transfer 1 n) 0 n
    rw [transfer_input]
    refine ⟨2 * n + 1, ?_, ?_⟩
    · rw [(transfer_correct 0 n).1]; rfl
    · rw [(transfer_correct 0 n).1]; simp [twoFile]
  exact ⟨hc, by rw [computed_simulation, hc]⟩


def cleanupProgram : Program 2 Unit := ⟨(), fun _ => .halt⟩
def cleanupFile : Registers 2 := twoFile 2 1

noncomputable def clearOnlyTape : TuringMachines.Tape (Symbol 2) (alphabet (0 : Fin 2)).blank :=
  (boundaryTape 0 cleanupFile).write 0 (clearOrigin (boundaryCell cleanupFile 0))

def erasedOnlyCell (z : ℤ) : Symbol 2 := setBit (boundaryCell cleanupFile z) 1 false

theorem erasedOnly_support : {z | erasedOnlyCell z ≠ blank} ⊆ Set.Ico 0 (2 : ℤ) := by
  intro z hz
  by_contra hn
  change ¬(0 ≤ z ∧ z < 2) at hn
  have hb : erasedOnlyCell z = blank := by
    apply Prod.ext
    · simp [erasedOnlyCell, setBit, boundaryCell, blank]
      omega
    · funext r
      fin_cases r <;> simp [erasedOnlyCell, setBit, boundaryCell, cleanupFile, twoFile, blank]
      omega
  exact hz hb


def erasedOnlyTape : TuringMachines.Tape (Symbol 2) (alphabet (0 : Fin 2)).blank :=
  ⟨erasedOnlyCell, (Set.finite_Ico _ _).subset erasedOnly_support⟩

def erasedOutputCell (z : ℤ) : Symbol 2 :=
  clearOrigin (setBit (boundaryCell cleanupFile z) 1 false)

theorem erasedOutput_support : {z | erasedOutputCell z ≠ blank} ⊆ Set.Ico 0 (2 : ℤ) := by
  intro z hz
  by_contra hn
  change ¬(0 ≤ z ∧ z < 2) at hn
  have hb : erasedOutputCell z = blank := by
    apply Prod.ext
    · rfl
    · funext r
      fin_cases r <;> simp [erasedOutputCell, clearOrigin, setBit, boundaryCell, cleanupFile, twoFile, blank]
      omega
  exact hz hb


def erasedOutputTape : TuringMachines.Tape (Symbol 2) (alphabet (0 : Fin 2)).blank :=
  ⟨erasedOutputCell, (Set.finite_Ico _ _).subset erasedOutput_support⟩

private theorem tape_ext {k : ℕ} (i : Fin k)
    (t u : TuringMachines.Tape (Symbol k) (alphabet i).blank)
    (h : ∀ z, t z = u z) : t = u := by
  cases t; cases u; congr; funext z; exact h z

private theorem readout_zero {k : ℕ} {L : Type*} (i : Fin k) (C : NativeConfig k L i)
    (h : C.tape C.head ≠ (alphabet i).mark) : TuringMachines.readout (alphabet i) C = 0 := by
  classical
  let : DecidableEq (Symbol k) := fun _ _ => Classical.propDecidable _
  unfold TuringMachines.readout
  apply (Nat.find_eq_iff (TuringMachines.readout_exists (alphabet i) C)).mpr
  exact ⟨by simpa only [Nat.cast_zero, add_zero] using h, by omega⟩

private theorem unary_readout {k : ℕ} {L : Type*} (i : Fin k) (q : Control k L) (n : ℕ) :
    TuringMachines.readout (alphabet i)
      (⟨q, 0, TuringMachines.unaryTape (alphabet i) n⟩ : NativeConfig k L i) = n := by
  classical
  let : DecidableEq (Symbol k) := fun _ _ => Classical.propDecidable _
  unfold TuringMachines.readout
  apply (Nat.find_eq_iff (TuringMachines.readout_exists (alphabet i) _)).mpr
  constructor
  · simp [TuringMachines.unaryTape, (alphabet i).mark_ne_blank.symm]
  · intro r hr
    have hr' : (r : ℤ) < (n : ℤ) := by exact_mod_cast hr
    simp [TuringMachines.unaryTape, hr']

theorem cleanup_counterexample :
    TuringMachines.readout (alphabet (0 : Fin 2))
      (boundary 0 (⟨(), cleanupFile⟩ : Config 2 Unit)) = 0 ∧
    TuringMachines.readout (alphabet (0 : Fin 2))
      (⟨.run (), 0, clearOnlyTape⟩ : NativeConfig 2 Unit 0) = 0 ∧
    TuringMachines.readout (alphabet (0 : Fin 2))
      (⟨.run (), 0, erasedOnlyTape⟩ : NativeConfig 2 Unit 0) = 0 ∧
    erasedOutputTape = TuringMachines.unaryTape (alphabet (0 : Fin 2)) 2 ∧
    TuringMachines.readout (alphabet (0 : Fin 2))
      (⟨.run (), 0, erasedOutputTape⟩ : NativeConfig 2 Unit 0) = 2 ∧
    TuringMachines.run (compiled cleanupProgram 0 1) (boundary 0 ⟨(), cleanupFile⟩) 6 =
      finalConfig 0 1 cleanupFile ∧
    TuringMachines.readout (alphabet (0 : Fin 2))
      (finalConfig 0 1 cleanupFile : NativeConfig 2 Unit 0) = 1 := by
  have he : erasedOutputTape = TuringMachines.unaryTape (alphabet (0 : Fin 2)) 2 := by
    have hc : ∀ z, erasedOutputTape z = TuringMachines.unaryTape (alphabet (0 : Fin 2)) 2 z := by
      intro z
      apply Prod.ext
      · simp [erasedOutputTape, erasedOutputCell, clearOrigin, TuringMachines.unaryTape, alphabet, mark, blank]
        split_ifs <;> rfl
      · funext r
        fin_cases r <;> simp [erasedOutputTape, erasedOutputCell, clearOrigin, setBit,
          boundaryCell, cleanupFile, twoFile, TuringMachines.unaryTape, alphabet, mark, blank]
        all_goals split_ifs <;> simp_all
    exact tape_ext 0 _ _ hc
  have hmax : maxRegister cleanupFile = 2 := by
    norm_num [maxRegister, cleanupFile, twoFile, Finset.univ_fin2]
  refine ⟨?_, ?_, ?_, he, ?_, ?_, ?_⟩
  · apply readout_zero
    intro hm
    have hflag := congrArg Prod.fst hm
    norm_num [boundary, boundaryTape, boundaryCell, alphabet, mark] at hflag
  · apply readout_zero
    intro hm
    have hbit := congrArg (fun a : Symbol 2 => a.2 1) hm
    norm_num [clearOnlyTape, TuringMachines.Tape.write, boundaryTape, boundaryCell,
      clearOrigin, cleanupFile, twoFile, alphabet, mark] at hbit
  · apply readout_zero
    intro hm
    have hflag := congrArg Prod.fst hm
    norm_num [erasedOnlyTape, erasedOnlyCell, setBit, boundaryCell, alphabet, mark] at hflag
  · rw [he]; exact unary_readout 0 (.run ()) 2
  · have hc := (cleanup_correct cleanupProgram 0 1 (⟨(), cleanupFile⟩ : Config 2 Unit) rfl).2.1
    simpa only [hmax] using hc
  · exact unary_readout 0 .final 1


theorem immediate_zero {k : ℕ} {L : Type*} [Fintype L]
    (P : Program k L) (i o : Fin k) (hp : P.code P.initial = .halt) :
    TuringMachines.FirstHaltingTime (compiled P i o)
      (TuringMachines.input (alphabet i) (compiled P i o) 0) 3 ∧
    TuringMachines.run (compiled P i o)
      (TuringMachines.input (alphabet i) (compiled P i o) 0) 3 =
      finalConfig i o (inputFile i 0) ∧
    TuringMachines.computed (compiled P i o) 0 = some 0 := by
  have hmax : maxRegister (inputFile i 0) = 0 := by simp [maxRegister, inputFile]
  have hfirst := first_halt_simulation P i o 0 0 hp (by intro a ha; omega)
  have hpair : TuringMachines.FirstHaltingTime (compiled P i o)
      (TuringMachines.input (alphabet i) (compiled P i o) 0) 3 ∧
      TuringMachines.run (compiled P i o)
        (TuringMachines.input (alphabet i) (compiled P i o) 0) 3 =
        finalConfig i o (inputFile i 0) := by
    simpa only [run, boundaryClock, input, hmax] using hfirst
  refine ⟨hpair.1, hpair.2, ?_⟩
  rw [computed_simulation]
  apply (computed_spec _ _ _ _ _).mpr
  exact ⟨0, hp, by simp [run, input, inputFile]⟩


def threeFile (x y z : ℕ) : Registers 3 := fun r => match r.val with
  | 0 => x | 1 => y | _ => z

def copyProgram : Program 3 (Fin 6) where
  initial := 0
  code p := match p.val with
    | 0 => .dec 0 1 3
    | 1 => .inc 1 2
    | 2 => .inc 2 0
    | 3 => .dec 2 4 5
    | 4 => .inc 0 3
    | _ => .halt

private theorem three_update_zero (x y z n : ℕ) :
    updateRegister (threeFile x y z) 0 n = threeFile n y z := by
  funext r; fin_cases r <;> simp [threeFile, updateRegister]

private theorem three_update_one (x y z n : ℕ) :
    updateRegister (threeFile x y z) 1 n = threeFile x n z := by
  funext r; fin_cases r <;> simp [threeFile, updateRegister]

private theorem three_update_two (x y z n : ℕ) :
    updateRegister (threeFile x y z) 2 n = threeFile x y n := by
  funext r; fin_cases r <;> simp [threeFile, updateRegister]

private theorem copy_a_pos (x y z : ℕ) (hx : 0 < x) :
    advance copyProgram ⟨0, threeFile x y z⟩ = ⟨1, threeFile (x - 1) y z⟩ := by
  have h0 : threeFile x y z 0 = x := rfl
  simp [advance, step, copyProgram, h0, Nat.ne_of_gt hx, three_update_zero]

private theorem copy_b (x y z : ℕ) :
    advance copyProgram ⟨1, threeFile x y z⟩ = ⟨2, threeFile x (y + 1) z⟩ := by
  have h1 : threeFile x y z 1 = y := rfl
  simp [advance, step, copyProgram, h1, three_update_one]

private theorem copy_c (x y z : ℕ) :
    advance copyProgram ⟨2, threeFile x y z⟩ = ⟨0, threeFile x y (z + 1)⟩ := by
  have h2 : threeFile x y z 2 = z := rfl
  simp [advance, step, copyProgram, h2, three_update_two]

private theorem copy_a_zero (y z : ℕ) :
    advance copyProgram ⟨0, threeFile 0 y z⟩ = ⟨3, threeFile 0 y z⟩ := by
  have h0 : threeFile 0 y z 0 = 0 := rfl
  simp [advance, step, copyProgram, h0]

private theorem copy_d_pos (x y z : ℕ) (hz : 0 < z) :
    advance copyProgram ⟨3, threeFile x y z⟩ = ⟨4, threeFile x y (z - 1)⟩ := by
  have h2 : threeFile x y z 2 = z := rfl
  simp [advance, step, copyProgram, h2, Nat.ne_of_gt hz, three_update_two]

private theorem copy_e (x y z : ℕ) :
    advance copyProgram ⟨4, threeFile x y z⟩ = ⟨3, threeFile (x + 1) y z⟩ := by
  have h0 : threeFile x y z 0 = x := rfl
  simp [advance, step, copyProgram, h0, three_update_zero]

private theorem copy_d_zero (x y : ℕ) :
    advance copyProgram ⟨3, threeFile x y 0⟩ = ⟨5, threeFile x y 0⟩ := by
  have h2 : threeFile x y 0 2 = 0 := rfl
  simp [advance, step, copyProgram, h2]

private theorem copy_input (n : ℕ) : input copyProgram 0 n = ⟨0, threeFile n 0 0⟩ := by
  change (⟨0, inputFile (0 : Fin 3) n⟩ : Config 3 (Fin 6)) = _
  congr 1
  funext r; fin_cases r <;> simp [inputFile, threeFile]

theorem copy_forward (n j : ℕ) (hj : j ≤ n) :
    run copyProgram (input copyProgram 0 n) (3 * j) = ⟨0, threeFile (n - j) j j⟩ := by
  induction j with
  | zero => simpa only [Nat.mul_zero, run, Nat.sub_zero] using copy_input n
  | succ j ih =>
    rw [show 3 * (j + 1) = 3 * j + 3 by omega, run_add, ih (by omega)]
    change advance copyProgram (advance copyProgram (advance copyProgram
      ⟨0, threeFile (n - j) j j⟩)) = _
    rw [copy_a_pos _ _ _ (by omega), copy_b, copy_c]
    congr 1


theorem copy_restore (n j : ℕ) (hj : j ≤ n) :
    run copyProgram (input copyProgram 0 n) (3 * n + 1 + 2 * j) =
      ⟨3, threeFile j n (n - j)⟩ := by
  induction j with
  | zero =>
    rw [show 3 * n + 1 + 2 * 0 = 3 * n + 1 by omega, run, copy_forward n n le_rfl]
    simpa only [Nat.sub_self, Nat.sub_zero] using copy_a_zero n n
  | succ j ih =>
    rw [show 3 * n + 1 + 2 * (j + 1) = (3 * n + 1 + 2 * j) + 2 by omega,
      run_add, ih (by omega)]
    change advance copyProgram (advance copyProgram ⟨3, threeFile j n (n - j)⟩) = _
    rw [copy_d_pos _ _ _ (by omega), copy_e]
    congr 1


theorem copy_correct (n : ℕ) :
    run copyProgram (input copyProgram 0 n) (5 * n + 2) = ⟨5, threeFile n n 0⟩ ∧
    ∀ j < 5 * n + 2, ¬ Halted copyProgram (run copyProgram (input copyProgram 0 n) j) := by
  constructor
  · rw [show 5 * n + 2 = (3 * n + 1 + 2 * n) + 1 by omega, run, copy_restore n n le_rfl]
    simpa only [Nat.sub_self] using copy_d_zero n n
  · intro j hj
    by_cases hfront : j < 3 * n + 1
    · have hjn : j / 3 ≤ n := by omega
      have hr : j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2 := by omega
      rcases hr with hr | hr | hr
      · rw [show j = 3 * (j / 3) by omega, copy_forward n (j / 3) hjn]
        simp [Halted, copyProgram]
      · rw [show j = 3 * (j / 3) + 1 by omega, run, copy_forward n (j / 3) hjn,
          copy_a_pos _ _ _ (by omega)]
        simp [Halted, copyProgram]
      · rw [show j = (3 * (j / 3) + 1) + 1 by omega, run, run,
          copy_forward n (j / 3) hjn, copy_a_pos _ _ _ (by omega), copy_b]
        simp [Halted, copyProgram]
    · let d := j - (3 * n + 1)
      have hd : d ≤ 2 * n := by dsimp [d]; omega
      have hdn : d / 2 ≤ n := by omega
      by_cases hr : d % 2 = 0
      · rw [show j = 3 * n + 1 + 2 * (d / 2) by dsimp [d] at *; omega,
          copy_restore n (d / 2) hdn]
        simp [Halted, copyProgram]
      · rw [show j = (3 * n + 1 + 2 * (d / 2)) + 1 by dsimp [d] at *; omega,
          run, copy_restore n (d / 2) hdn, copy_d_pos _ _ _ (by omega)]
        simp [Halted, copyProgram]


theorem copy_output (n : ℕ) :
    computed copyProgram 0 1 n = some n ∧
    TuringMachines.computed (compiled copyProgram 0 1) n = some n := by
  have hc : computed copyProgram 0 1 n = some n := by
    apply (computed_spec _ _ _ _ _).mpr
    refine ⟨5 * n + 2, ?_, ?_⟩
    · rw [(copy_correct n).1]; rfl
    · rw [(copy_correct n).1]; rfl
  exact ⟨hc, by rw [computed_simulation, hc]⟩


def loopProgram {k : ℕ} (i : Fin k) : Program k Unit := ⟨(), fun _ => .inc i ()⟩

theorem loop_run {k : ℕ} (i : Fin k) (n j : ℕ) :
    run (loopProgram i) (input (loopProgram i) i n) j = ⟨(), inputFile i (n + j)⟩ ∧
    ¬ Halted (loopProgram i) (run (loopProgram i) (input (loopProgram i) i n) j) := by
  have hr : run (loopProgram i) (input (loopProgram i) i n) j =
      (⟨(), inputFile i (n + j)⟩ : Config k Unit) := by
    induction j with
    | zero => simp [run, input, loopProgram]
    | succ j ih =>
      rw [run, ih]
      have hf : updateRegister (inputFile i (n + j)) i ((inputFile i (n + j)) i + 1) =
          inputFile i (n + (j + 1)) := by
        funext r
        by_cases he : r = i <;> simp [updateRegister, inputFile, he, Nat.add_assoc]
      simpa only [advance, step, loopProgram, Option.getD_some] using
        congrArg (fun R => (⟨(), R⟩ : Config k Unit)) hf
  exact ⟨hr, by simp [Halted, loopProgram]⟩


theorem loop_divergence {k : ℕ} (i o : Fin k) (n : ℕ) :
    (∀ t, ¬ TuringMachines.Halted (compiled (loopProgram i) i o)
      (TuringMachines.run (compiled (loopProgram i) i o)
        (TuringMachines.input (alphabet i) (compiled (loopProgram i) i o) n) t)) ∧
    TuringMachines.computed (compiled (loopProgram i) i o) n = none := by
  have hn := (divergence_simulation (loopProgram i) i o n).mp
    (fun j => (loop_run i n j).2)
  refine ⟨hn, ?_⟩
  rw [computed_simulation]
  cases hc : computed (loopProgram i) i o n with
  | none => rfl
  | some m =>
    obtain ⟨j, hj, _⟩ := (computed_spec (loopProgram i) i o n m).mp hc
    exact ((loop_run i n j).2 hj).elim


def figureProgram : Program 3 Bool where
  initial := false
  code p := if p then .halt else .inc 1 true

theorem figure_example :
    updateRegister (threeFile 2 3 1) 1 4 = threeFile 2 4 1 ∧
    TuringMachines.run (compiled figureProgram 0 1)
      (boundary 0 ⟨false, threeFile 2 3 1⟩) 8 = boundary 0 ⟨true, threeFile 2 4 1⟩ ∧
    TuringMachines.run (compiled figureProgram 0 1)
      (boundary 0 ⟨false, threeFile 2 3 1⟩) 18 = finalConfig 0 1 (threeFile 2 4 1) ∧
    TuringMachines.readout (alphabet (0 : Fin 3))
      (finalConfig 0 1 (threeFile 2 4 1) : NativeConfig 3 Bool 0) = 4 := by
  have hu : updateRegister (threeFile 2 3 1) 1 4 = threeFile 2 4 1 := three_update_one 2 3 1 4
  have hi := (increment_correct figureProgram (0 : Fin 3) 1 1 false true
    (threeFile 2 3 1) (by rfl)).2.1
  have hb : TuringMachines.run (compiled figureProgram 0 1)
      (boundary 0 ⟨false, threeFile 2 3 1⟩) 8 = boundary 0 ⟨true, threeFile 2 4 1⟩ := by
    change TuringMachines.run (compiled figureProgram 0 1)
      (boundary 0 ⟨false, threeFile 2 3 1⟩) 8 =
      boundary 0 ⟨true, updateRegister (threeFile 2 3 1) 1 4⟩ at hi
    rw [hu] at hi
    exact hi
  have hmax : maxRegister (threeFile 2 4 1) = 4 := by
    norm_num [maxRegister, threeFile, Fin.univ_succ]
  have hc := (cleanup_correct figureProgram (0 : Fin 3) 1
    (⟨true, threeFile 2 4 1⟩ : Config 3 Bool) (by rfl)).2.1
  have hfinish : TuringMachines.run (compiled figureProgram 0 1)
      (boundary 0 ⟨false, threeFile 2 3 1⟩) 18 = finalConfig 0 1 (threeFile 2 4 1) := by
    have hadd (C : NativeConfig 3 Bool 0) (a b : ℕ) :
        TuringMachines.run (compiled figureProgram 0 1) C (a + b) =
        TuringMachines.run (compiled figureProgram 0 1)
          (TuringMachines.run (compiled figureProgram 0 1) C a) b := by
      induction b with
      | zero => rfl
      | succ b ih => exact congrArg (TuringMachines.advance (compiled figureProgram 0 1)) ih
    rw [show 18 = 8 + 10 by rfl, hadd, hb]
    simpa only [hmax] using hc
  exact ⟨hu, hb, hfinish, unary_readout 0 .final 4⟩


end Lemmatheca.Entry.CounterProgramsOnTape
