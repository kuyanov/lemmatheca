import Lemmatheca.OracleProgramNumberings.Enumerable

/-! Worked questions about uniformity, specialization and oracle-dependent certificates. -/
namespace Lemmatheca.Entry.OracleProgramNumberings

open Lemmatheca.ComputabilityTheory
open OracleComputation OracleProgramNumberings

def queryLeftIndex : ℕ := encodeCode (.comp .query .left)

theorem successor_at_allowance (q : ℕ → ℕ) (k : ℕ) :
    boundedQ q (k + 1) .succ k = some (k + 1) := by simp [boundedQ]

theorem allowance_not_output_bound (q : ℕ → ℕ) :
    boundedQ q 1 (.pair .succ .succ) 0 = some 3 := by simp [boundedQ, Nat.pair]

theorem universal_query (A : Set ℕ) (x : ℕ) :
    eval A universalCode (Nat.pair 4 x) =
      Part.some (UniversalComputation.indicator (fun n => n ∈ A) x) := by
  rw [universal_code_eval]
  simp [phi, decodeCode, eval]

theorem specialized_query (A : Set ℕ) (a x : ℕ) :
    phi A (specialize queryLeftIndex a) x =
      Part.some (UniversalComputation.indicator (fun n => n ∈ A) a) := by
  rw [specialize_eval]
  simp [phi, queryLeftIndex, decode_encode, eval]

theorem query_certificate (A : Set ℕ) (x : ℕ) :
    boundedValue A (x + 1) 4 x = 2 ↔ x ∈ A := by
  classical
  simp [boundedValue, bounded, decodeCode, boundedQ, optionNumber,
    UniversalComputation.indicator]

theorem query_certificate_decides_oracle (A : Set ℕ)
    (h : ComputablePred (fun p : ℕ × ℕ => boundedValue A p.1 4 p.2 = 2)) :
    ComputablePred (fun x => x ∈ A) := by
  have hc : Computable (fun x : ℕ => (x + 1, x)) :=
    (Primrec.succ.pair Primrec.id).to_comp
  exact (Computable.comp h.decide hc).computablePred |>.of_eq fun x => query_certificate A x

theorem halting_query_certificate_not_computable :
    ¬ ComputablePred (fun p : ℕ × ℕ =>
      boundedValue UniversalComputation.haltingDiagonal p.1 4 p.2 = 2) := by
  intro h
  exact UniversalComputation.haltingDiagonal_undecidable
    (query_certificate_decides_oracle _ h)

end Lemmatheca.Entry.OracleProgramNumberings
