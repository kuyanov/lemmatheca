import Lemmatheca.OraclePadding.Basic

/-! The query program keeps its oracle-dependent behavior under padding. -/
namespace Lemmatheca.Entry.OraclePadding

open Lemmatheca.ComputabilityTheory
open OracleComputation OracleProgramNumberings OraclePadding

theorem padded_query (A : Set ℕ) (t x : ℕ) :
    phi A (pad 4 t) x =
      Part.some (UniversalComputation.indicator (fun n => n ∈ A) x) := by
  rw [pad_eval]
  simp only [phi, decodeCode, eval]

end Lemmatheca.Entry.OraclePadding
