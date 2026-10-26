import Lemmatheca.CounterProgramsOnTape.Tracks

namespace Lemmatheca.ComputabilityTheory.CounterPrograms

inductive Control (k : ℕ) (L : Type*)
  | boot
  | run (pc : L)
  | inc (register : Fin k) (next : L)
  | dec (register : Fin k) (next : L)
  | erase (register : Fin k) (next : L)
  | back (next : L)
  | clean
  | cleanBack
  | final
  deriving DecidableEq, Fintype

abbrev NativeConfig (k : ℕ) (L : Type*) (i : Fin k) :=
  TuringMachines.Config (alphabet i) (Control k L)

variable {k : ℕ} {L : Type*}

def boundary (i : Fin k) (S : Config k L) : NativeConfig k L i :=
  ⟨.run S.pc, 0, boundaryTape i S.regs⟩

def finalConfig (i o : Fin k) (R : Registers k) : NativeConfig k L i :=
  ⟨.final, 0, TuringMachines.unaryTape (alphabet i) (R o)⟩

def table (P : Program k L) (i o : Fin k) (s : Control k L) (a : Symbol k) :
    Option (Control k L × Symbol k × TuringMachines.Move) :=
  match s with
  | .boot => some (.run P.initial, setOrigin a, .stay)
  | .run p => match P.code p with
    | .inc r q => some (.inc r q, a, .stay)
    | .dec r qp qz => if a.2 r then some (.dec r qp, a, .right)
        else some (.run qz, a, .stay)
    | .halt => some (.clean, a, .stay)
  | .inc r q => if a.2 r then some (.inc r q, a, .right)
      else if a.1 then some (.run q, setBit a r true, .stay)
      else some (.back q, setBit a r true, .left)
  | .dec r q => if a.2 r then some (.dec r q, a, .right)
      else some (.erase r q, a, .left)
  | .erase r q => if a.1 then some (.run q, setBit a r false, .stay)
      else some (.back q, setBit a r false, .left)
  | .back q => if a.1 then some (.run q, a, .stay) else some (.back q, a, .left)
  | .clean => if anyBit a then some (.clean, a, .right)
      else if a.1 then some (.final, clearOrigin a, .stay)
      else some (.cleanBack, a, .left)
  | .cleanBack => if a.1 then some (.final, outputProjection i o a, .stay)
      else some (.cleanBack, outputProjection i o a, .left)
  | .final => none

def compiled [Fintype L] (P : Program k L) (i o : Fin k) :
    TuringMachines.Machine (alphabet i) (Control k L) where
  initial := .boot
  table := table P i o

def instructionRegister (P : Program k L) (S : Config k L) : Option (Fin k) :=
  match P.code S.pc with | .inc r _ => some r | .dec r _ _ => some r | .halt => none

def instructionLength (P : Program k L) (S : Config k L) : ℕ :=
  match P.code S.pc with
  | .inc r _ => 2 * S.regs r + 2
  | .dec r _ _ => if S.regs r = 0 then 1 else 2 * S.regs r + 1
  | .halt => 0

noncomputable def MacroTrace [Fintype L] (P : Program k L) (i o : Fin k)
    (S U : Config k L) (r : Fin k) (N : ℕ) : Prop :=
  0 < N ∧
  TuringMachines.run (compiled P i o) (boundary i S) N = boundary i U ∧
  TuringMachines.ActualRun (compiled P i o) N
    (fun j => TuringMachines.run (compiled P i o) (boundary i S) j.val) ∧
  ∀ j ≤ N, let C := TuringMachines.run (compiled P i o) (boundary i S) j
    C.state ≠ .final ∧ 0 ≤ C.head ∧ Frame S.regs r C.tape

noncomputable def CleanupTrace [Fintype L] (P : Program k L) (i o : Fin k)
    (S : Config k L) (N : ℕ) : Prop :=
  0 < N ∧
  TuringMachines.run (compiled P i o) (boundary i S) N = finalConfig i o S.regs ∧
  TuringMachines.ActualRun (compiled P i o) N
    (fun j => TuringMachines.run (compiled P i o) (boundary i S) j.val) ∧
  (∀ j < N, (TuringMachines.run (compiled P i o) (boundary i S) j).state ≠ .final) ∧
  ∀ j ≤ N, 0 ≤ (TuringMachines.run (compiled P i o) (boundary i S) j).head

theorem halted_iff_final [Fintype L] (P : Program k L) (i o : Fin k)
    (C : NativeConfig k L i) :
    TuringMachines.Halted (compiled P i o) C ↔ C.state = .final := by
  unfold TuringMachines.Halted compiled
  cases hs : C.state with
  | run p =>
    cases hp : P.code p <;> simp [table, hp]
    split_ifs <;> simp
  | inc r q => simp [table]; split_ifs <;> simp
  | dec r q => simp [table]; split_ifs <;> simp
  | erase r q => simp [table]; split_ifs <;> simp
  | back q => simp [table]; split_ifs <;> simp
  | clean => simp [table]; split_ifs <;> simp
  | cleanBack => simp [table]; split_ifs <;> simp
  | boot => simp [table]
  | final => simp [table]

theorem boot_correct [Fintype L] (P : Program k L) (i o : Fin k) (n : ℕ) :
    TuringMachines.Step (compiled P i o)
      (TuringMachines.input (alphabet i) (compiled P i o) n)
      (boundary i (input P i n)) := by
  classical
  have tape_ext (t u : TuringMachines.Tape (Symbol k) (alphabet i).blank)
      (h : ∀ z, t z = u z) : t = u := by
    cases t; cases u; congr; funext z; exact h z
  have ht :
      (TuringMachines.unaryTape (alphabet i) n).write 0
          (setOrigin (TuringMachines.unaryTape (alphabet i) n 0)) =
        boundaryTape i (inputFile i n) := by
    apply tape_ext
    intro z
    change Function.update (TuringMachines.unaryTape (alphabet i) n).cells 0
      (setOrigin (TuringMachines.unaryTape (alphabet i) n 0)) z = boundaryCell (inputFile i n) z
    rw [Function.update_apply]
    by_cases hz : z = 0
    · subst z
      by_cases hn : 0 < n
      all_goals apply Prod.ext
      all_goals simp [TuringMachines.unaryTape, setOrigin, alphabet, mark, blank,
        boundaryCell, hn]
      all_goals funext r; by_cases hr : r = i <;> simp [inputFile, hr, hn]
    · by_cases hc : 0 ≤ z ∧ z < (n : ℤ)
      all_goals apply Prod.ext
      all_goals simp [hz, hc, TuringMachines.unaryTape, alphabet, mark, blank,
        boundaryCell]
      all_goals funext r; by_cases hr : r = i <;> simp [inputFile, hr]
      all_goals simp_all

  simp [TuringMachines.Step, TuringMachines.step, TuringMachines.input, compiled,
    table, TuringMachines.Move.displacement, boundary, input, ht]

end Lemmatheca.ComputabilityTheory.CounterPrograms
