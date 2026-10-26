import Lemmatheca.TuringComputationAndRecursion.Compiler
import Lemmatheca.CounterProgramsOnTape.Simulation
import Lemmatheca.CodingTuringComputations.Simulation

namespace Lemmatheca.ComputabilityTheory.RecursiveTapeCompiler

open CounterPrograms PartialRecursiveFunctions

def unaryArgs (n : ℕ) : Args 1 := List.Vector.ofFn (fun _ => n)

def nativeMachine (A : Routine 1) :
    TuringMachines.Machine (alphabet (inputPort 1 A.work 0))
      (Control (1 + 2 + A.work) (Option A.body.Label)) :=
  compiled A.body.program (inputPort 1 A.work 0) (outputPort 1 A.work)

structure NativeWitness (f : ℕ → Part ℕ) where
  Symbol : Type
  State : Type
  symbols : Fintype Symbol
  states : Fintype State
  alphabet : TuringMachines.Alphabet Symbol
  machine : @TuringMachines.Machine Symbol alphabet State symbols states
  correct : ∀ n, Part.ofOption (@TuringMachines.computed Symbol State alphabet symbols states machine n) = f n

attribute [instance] NativeWitness.symbols NativeWitness.states

def NativeComputable (f : ℕ → Part ℕ) : Prop := Nonempty (NativeWitness f)

theorem unary_initial_file (A : Routine 1) (n : ℕ) :
    initialFile A.work (unaryArgs n) = inputFile (inputPort 1 A.work 0) n := by
  funext r
  by_cases hr : r = inputPort 1 A.work 0
  · subst r
    simp [initialFile, inputFile, inputPort, unaryArgs]
  · have hv : r.val ≠ 1 := by
      intro h
      apply hr
      apply Fin.ext
      exact h
    have hg : ¬ (1 ≤ r.val ∧ r.val ≤ 1) := by omega
    simp [initialFile, inputFile, hr, hg]

theorem clean_counter_unary (A : Routine 1) (f : ℕ → Part ℕ)
    (hA : Clean A (fun x => f (x.get 0))) :
    eval A.body.program (inputPort 1 A.work 0) (outputPort 1 A.work) = f := by
  funext n
  have h := congrFun (clean_eval A (fun x => f (x.get 0)) hA) (unaryArgs n)
  change evalFrom A.body.program ⟨A.body.entry, inputFile (inputPort 1 A.work 0) n⟩
    (outputPort 1 A.work) = f n
  rw [← unary_initial_file A n]
  exact h

theorem native_machine_eval (A : Routine 1) (f : ℕ → Part ℕ)
    (hA : Clean A (fun x => f (x.get 0))) :
    (fun n => Part.ofOption (TuringMachines.computed (nativeMachine A) n)) = f := by
  exact (eval_simulation A.body.program (inputPort 1 A.work 0) (outputPort 1 A.work)).trans
    (clean_counter_unary A f hA)

theorem native_machine_final (A : Routine 1) (f : ℕ → Part ℕ)
    (hA : Clean A (fun x => f (x.get 0))) (n m : ℕ) (hm : m ∈ f n) :
    ∃ t, TuringMachines.FirstHaltingTime (nativeMachine A)
      (TuringMachines.input (alphabet (inputPort 1 A.work 0)) (nativeMachine A) n) t ∧
      TuringMachines.run (nativeMachine A)
        (TuringMachines.input (alphabet (inputPort 1 A.work 0)) (nativeMachine A) n) t =
      (⟨.final, 0, TuringMachines.unaryTape (alphabet (inputPort 1 A.work 0)) m⟩ :
        NativeConfig (1 + 2 + A.work) (Option A.body.Label) (inputPort 1 A.work 0)) := by
  classical
  let P := A.body.program
  let i := inputPort 1 A.work 0
  let o := outputPort 1 A.work
  have hout : Output P i o n m := (eval_spec P i o n m).mp (by
    rw [clean_counter_unary A f hA]
    exact hm)
  have hex : ∃ j, Halted P (run P (input P i n) j) := by
    obtain ⟨j, hj, _⟩ := hout
    exact ⟨j, hj⟩
  let j := Nat.find hex
  have hj : Halted P (run P (input P i n) j) := Nat.find_spec hex
  have hprev : ∀ a < j, ¬ Halted P (run P (input P i n) a) :=
    fun a ha => Nat.find_min hex ha
  have hval : (run P (input P i n) j).regs o = m :=
    outputFrom_unique P (input P i n) o _ m ⟨j, hj, rfl⟩ hout
  have hs := first_halt_simulation P i o n j hj hprev
  refine ⟨boundaryClock P i n j + 2 * maxRegister (run P (input P i n) j).regs + 2,
    hs.1, ?_⟩
  change TuringMachines.run (compiled P i o)
    (TuringMachines.input (alphabet i) (compiled P i o) n) _ = _
  rw [hs.2]
  simp only [finalConfig, hval]
  rfl

theorem native_machine_divergence (A : Routine 1) (f : ℕ → Part ℕ)
    (hA : Clean A (fun x => f (x.get 0))) (n : ℕ) (hn : ¬ (f n).Dom) :
    ∀ t, ¬ TuringMachines.Halted (nativeMachine A)
      (TuringMachines.run (nativeMachine A)
        (TuringMachines.input (alphabet (inputPort 1 A.work 0)) (nativeMachine A) n) t) := by
  apply (divergence_simulation A.body.program (inputPort 1 A.work 0)
    (outputPort 1 A.work) n).mp
  simpa only [input, Fragment.program, unary_initial_file] using
    clean_undefined A (fun x => f (x.get 0)) hA (unaryArgs n)
      (by simpa [unaryArgs] using hn)

theorem specified_native_compiler (f : ℕ → Part ℕ)
    (hf : Recursive (fun x : Args 1 => f (x.get 0))) :
    ∃ c : Code 1, c.eval = (fun x => f (x.get 0)) ∧
      let A := compile c
      Clean A (fun x => f (x.get 0)) ∧
      (∀ n m, TuringMachines.Output (nativeMachine A) n m ↔ m ∈ f n) ∧
      (fun n => Part.ofOption (TuringMachines.computed (nativeMachine A) n)) = f ∧
      (∀ n m, m ∈ f n → ∃ t,
        TuringMachines.run (nativeMachine A)
          (TuringMachines.input (alphabet (inputPort 1 A.work 0)) (nativeMachine A) n) t =
        (⟨.final, 0, TuringMachines.unaryTape (alphabet (inputPort 1 A.work 0)) m⟩ :
          NativeConfig (1 + 2 + A.work) (Option A.body.Label) (inputPort 1 A.work 0))) ∧
      ∀ n, ¬ (f n).Dom → ∀ t, ¬ TuringMachines.Halted (nativeMachine A)
        (TuringMachines.run (nativeMachine A)
          (TuringMachines.input (alphabet (inputPort 1 A.work 0)) (nativeMachine A) n) t) := by
  obtain ⟨c, hc⟩ := recursive_code (fun x => f (x.get 0)) hf
  have hA : Clean (compile c) (fun x => f (x.get 0)) := hc ▸ compile_clean c
  refine ⟨c, hc, hA, ?_, native_machine_eval (compile c) f hA, ?_,
    native_machine_divergence (compile c) f hA⟩
  · intro n m
    rw [← TuringMachines.computed_spec]
    have hh : m ∈ Part.ofOption (TuringMachines.computed (nativeMachine (compile c)) n) ↔
        m ∈ f n := by rw [congrFun (native_machine_eval (compile c) f hA) n]
    simpa only [Part.mem_ofOption, Option.mem_def] using hh
  · intro n m hm
    obtain ⟨t, _, ht⟩ := native_machine_final (compile c) f hA n m hm
    exact ⟨t, ht⟩

theorem recursive_iff_native (f : ℕ → Part ℕ) :
    Recursive (fun x : Args 1 => f (x.get 0)) ↔ NativeComputable f := by
  constructor
  · intro hf
    obtain ⟨c, hc⟩ := recursive_code (fun x => f (x.get 0)) hf
    let A := compile c
    have hA : Clean A (fun x => f (x.get 0)) := hc ▸ compile_clean c
    exact ⟨{ Symbol := Symbol (1 + 2 + A.work)
             State := Control (1 + 2 + A.work) (Option A.body.Label)
             symbols := inferInstance
             states := inferInstance
             alphabet := alphabet (inputPort 1 A.work 0)
             machine := nativeMachine A
             correct := fun n => congrFun (native_machine_eval A f hA) n }⟩
  · rintro ⟨W⟩
    exact (TapeCoding.turing_recursive W.machine).of_eq (fun v => W.correct (v.get 0))

theorem nat_partrec_iff_native (f : ℕ → Part ℕ) : Nat.Partrec f ↔ NativeComputable f := by
  exact MachinesAndComputationHistories.unary_recursive_iff.symm.trans (recursive_iff_native f)

theorem total_recursive_iff_native (f : ℕ → Part ℕ) :
    (Recursive (fun x : Args 1 => f (x.get 0)) ∧ ∀ n, (f n).Dom) ↔
      ∃ W : NativeWitness f, ∀ n, ∃ t,
        TuringMachines.Halted W.machine
          (TuringMachines.run W.machine (TuringMachines.input W.alphabet W.machine n) t) := by
  constructor
  · rintro ⟨hf, htotal⟩
    obtain ⟨W⟩ := (recursive_iff_native f).mp hf
    refine ⟨W, fun n => ?_⟩
    obtain ⟨m, hm⟩ := (Part.dom_iff_mem).mp (htotal n)
    have hc : TuringMachines.computed W.machine n = some m := by
      apply Part.mem_ofOption.mp
      rw [W.correct]
      exact hm
    obtain ⟨t, ht, _⟩ := (TuringMachines.computed_spec W.machine n m).mp hc
    exact ⟨t, ht⟩
  · rintro ⟨W, hhalt⟩
    refine ⟨(recursive_iff_native f).mpr ⟨W⟩, fun n => ?_⟩
    obtain ⟨t, ht⟩ := hhalt n
    have hc := (TuringMachines.computed_spec W.machine n
      (TuringMachines.readout W.alphabet
        (TuringMachines.run W.machine (TuringMachines.input W.alphabet W.machine n) t))).mpr
      ⟨t, ht, rfl⟩
    have hm := Part.mem_ofOption.mpr hc
    rw [W.correct] at hm
    exact hm.1

end Lemmatheca.ComputabilityTheory.RecursiveTapeCompiler
