import Lemmatheca.MathematicalLogic.MachinesAndComputationHistories
namespace Lemmatheca.Entry.MachinesAndComputationHistories
open Lemmatheca.MathematicalLogic.MachinesAndComputationHistories

def doublingMachine : Machine where
  initial x := Nat.pair x 0
  transition c := Nat.pair ((Nat.unpair c).1 - 1) ((Nat.unpair c).2 + 2)
  halt c := decide ((Nat.unpair c).1 = 0)
  output c := (Nat.unpair c).2

theorem doubling_primitive : Primitive doublingMachine := by
  have hl : Primrec (fun q : ℕ => (Nat.unpair q).1) := Primrec.fst.comp Primrec.unpair
  have hr : Primrec (fun q : ℕ => (Nat.unpair q).2) := Primrec.snd.comp Primrec.unpair
  refine ⟨Primrec₂.natPair.comp Primrec.id (Primrec.const 0), ?_, ?_, hr⟩
  · exact Primrec₂.natPair.comp (Primrec.nat_sub.comp hl (Primrec.const 1))
      (Primrec.nat_add.comp hr (Primrec.const 2))
  · exact (Primrec.eq.comp hl (Primrec.const 0)).decide

theorem doubling_run (x i : ℕ) (hi : i ≤ x) :
    run doublingMachine x i = Nat.pair (x - i) (2 * i) := by
  induction i with
  | zero => simp [run, doublingMachine]
  | succ i ih =>
    have hi' : i ≤ x := by omega
    have hxi : x - i ≠ 0 := by omega
    rw [run, next, ih hi']
    simp only [doublingMachine, Nat.unpair_pair, hxi, decide_false,
      Bool.false_eq_true, ↓reduceIte]
    congr 1

theorem doubling_compute (x : ℕ) : compute doublingMachine x = Part.some (2 * x) := by
  apply Part.eq_some_iff.mpr
  apply (compute_output doublingMachine x (2 * x)).mpr
  refine ⟨x, ?_, ?_⟩
  · rw [doubling_run x x (le_refl x)]
    simp [doublingMachine]
  · rw [doubling_run x x (le_refl x)]
    simp [doublingMachine]

theorem doubling_trace_three :
    (List.range 4).map (run doublingMachine 3) =
      [Nat.pair 3 0, Nat.pair 2 2, Nat.pair 1 4, Nat.pair 0 6] := by
  change [run doublingMachine 3 0, run doublingMachine 3 1,
    run doublingMachine 3 2, run doublingMachine 3 3] = _
  rw [doubling_run 3 0 (by omega), doubling_run 3 1 (by omega),
    doubling_run 3 2 (by omega), doubling_run 3 3 (by omega)]

theorem zero_program_bound :
    bounded .zero 100 100 = none ∧ bounded .zero 101 100 = some 0 := by
  norm_num [bounded, Nat.Partrec.Code.evaln]

theorem successor_program_bound (k : ℕ) :
    bounded .succ (k + 1) k = some (k + 1) := by
  simp [bounded, Nat.Partrec.Code.evaln]

end Lemmatheca.Entry.MachinesAndComputationHistories
