import Lemmatheca.TuringMachines.Unary
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic

namespace Lemmatheca.ComputabilityTheory.CounterPrograms

abbrev Registers (k : ℕ) := Fin k → ℕ

def updateRegister {k : ℕ} (R : Registers k) (r : Fin k) (n : ℕ) : Registers k :=
  Function.update R r n

inductive Instr (k : ℕ) (L : Type*)
  | inc (register : Fin k) (next : L)
  | dec (register : Fin k) (positive zero : L)
  | halt
  deriving DecidableEq, Fintype

structure Program (k : ℕ) (L : Type*) where
  initial : L
  code : L → Instr k L

@[ext] structure Config (k : ℕ) (L : Type*) where
  pc : L
  regs : Registers k

variable {k : ℕ} {L : Type*}

def step (P : Program k L) (S : Config k L) : Option (Config k L) :=
  match P.code S.pc with
  | .inc r q => some ⟨q, updateRegister S.regs r (S.regs r + 1)⟩
  | .dec r qp qz => if S.regs r = 0 then some ⟨qz, S.regs⟩
      else some ⟨qp, updateRegister S.regs r (S.regs r - 1)⟩
  | .halt => none

def Step (P : Program k L) (S U : Config k L) : Prop := step P S = some U

def Halted (P : Program k L) (S : Config k L) : Prop := P.code S.pc = .halt

def haltTest (P : Program k L) (S : Config k L) : Bool :=
  match P.code S.pc with | .halt => true | _ => false

def advance (P : Program k L) (S : Config k L) : Config k L := (step P S).getD S

def run (P : Program k L) (S : Config k L) : ℕ → Config k L
  | 0 => S
  | j + 1 => advance P (run P S j)

def OutputFrom (P : Program k L) (S : Config k L) (o : Fin k) (m : ℕ) : Prop :=
  ∃ j, Halted P (run P S j) ∧ (run P S j).regs o = m

noncomputable def computedFrom (P : Program k L) (S : Config k L) (o : Fin k) : Option ℕ := by
  classical
  exact if h : ∃ m, OutputFrom P S o m then some (Classical.choose h) else none

noncomputable def evalFrom (P : Program k L) (S : Config k L) (o : Fin k) : Part ℕ :=
  Part.ofOption (computedFrom P S o)

def inputFile (i : Fin k) (n : ℕ) : Registers k := fun r => if r = i then n else 0

def input (P : Program k L) (i : Fin k) (n : ℕ) : Config k L := ⟨P.initial, inputFile i n⟩

def Output (P : Program k L) (i o : Fin k) (n m : ℕ) : Prop :=
  OutputFrom P (input P i n) o m

noncomputable def computed (P : Program k L) (i o : Fin k) (n : ℕ) : Option ℕ :=
  computedFrom P (input P i n) o

noncomputable def eval (P : Program k L) (i o : Fin k) (n : ℕ) : Part ℕ :=
  evalFrom P (input P i n) o

theorem step_deterministic (P : Program k L) (S U V : Config k L)
    (hU : Step P S U) (hV : Step P S V) : U = V := by
  exact Option.some.inj (hU.symm.trans hV)

theorem halted_iff_step_none (P : Program k L) (S : Config k L) :
    Halted P S ↔ step P S = none := by
  cases h : P.code S.pc with
  | inc r q => simp [Halted, step, h]
  | dec r qp qz =>
      by_cases hz : S.regs r = 0 <;> simp [Halted, step, h, hz]
  | halt => simp [Halted, step, h]

theorem haltTest_spec (P : Program k L) (S : Config k L) :
    haltTest P S = true ↔ Halted P S := by
  cases h : P.code S.pc <;> simp [haltTest, Halted, h]

theorem run_add (P : Program k L) (S : Config k L) (a b : ℕ) :
    run P S (a + b) = run P (run P S a) b := by
  induction b with
  | zero => simp [run]
  | succ b ih => simp [run, ih]

theorem run_halted_add (P : Program k L) (S : Config k L) (j d : ℕ)
    (hj : Halted P (run P S j)) : run P S (j + d) = run P S j := by
  induction d with
  | zero => simp
  | succ d ih =>
      simp [run, ih, advance, (halted_iff_step_none P _).mp hj]

theorem outputFrom_unique (P : Program k L) (S : Config k L) (o : Fin k) (a b : ℕ)
    (ha : OutputFrom P S o a) (hb : OutputFrom P S o b) : a = b := by
  obtain ⟨j, hj, ha⟩ := ha
  obtain ⟨t, ht, hb⟩ := hb
  rcases le_total j t with h | h
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [run_halted_add P S j d hj] at hb
    exact ha.symm.trans hb
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [run_halted_add P S t d ht] at ha
    exact ha.symm.trans hb

theorem computedFrom_spec (P : Program k L) (S : Config k L) (o : Fin k) (m : ℕ) :
    computedFrom P S o = some m ↔ OutputFrom P S o m := by
  classical
  by_cases h : ∃ z, OutputFrom P S o z
  · simp only [computedFrom, dite_eq_left h, Option.some.injEq]
    constructor
    · rintro rfl
      exact Classical.choose_spec h
    · intro hm
      exact outputFrom_unique P S o _ _ (Classical.choose_spec h) hm
  · have hm : ¬ OutputFrom P S o m := fun hm => h ⟨m, hm⟩
    simp [computedFrom, h, hm]

theorem evalFrom_spec (P : Program k L) (S : Config k L) (o : Fin k) (m : ℕ) :
    m ∈ evalFrom P S o ↔ OutputFrom P S o m := by
  rw [evalFrom, Part.mem_ofOption]
  exact computedFrom_spec P S o m

theorem computed_spec (P : Program k L) (i o : Fin k) (n m : ℕ) :
    computed P i o n = some m ↔ Output P i o n m := by
  exact computedFrom_spec P (input P i n) o m

theorem eval_spec (P : Program k L) (i o : Fin k) (n m : ℕ) :
    m ∈ eval P i o n ↔ Output P i o n m := by
  exact evalFrom_spec P (input P i n) o m

end Lemmatheca.ComputabilityTheory.CounterPrograms
