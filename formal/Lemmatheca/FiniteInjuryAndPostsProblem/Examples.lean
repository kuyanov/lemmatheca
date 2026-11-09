import Lemmatheca.FiniteInjuryAndPostsProblem.Degrees

/-! A queried-bit change can destroy an earlier diagonal disagreement. -/
namespace Lemmatheca.Entry.FiniteInjury

open Lemmatheca.ComputabilityTheory
open OracleComputation OracleProgramNumberings

def queryAt (q : ℕ) : Code := .comp .query (constantCode q)

theorem queried_bit_injury (q x : ℕ) :
    eval ∅ (queryAt q) x = Part.some 0 ∧
      eval {q} (queryAt q) x = Part.some 1 := by
  classical
  simp [queryAt, eval, constant_eval, UniversalComputation.indicator]

end Lemmatheca.Entry.FiniteInjury
