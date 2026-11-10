import Lemmatheca.HighDegreesAndDomination.Consequences
import Lemmatheca.LowSimpleSets.Verification
import Lemmatheca.DominationAndHyperimmuneDegrees.Approximation
import Lemmatheca.FriedbergJumpInversion.Degrees

/-! The specified low-simple counterexample and the actual inversion witness. -/
namespace Lemmatheca.Entry.HighDegreesAndDomination

open Lemmatheca.ComputabilityTheory
open HighDegreesAndDomination UniversalComputation OracleComputation TuringDegrees
open HyperimmuneDegrees

noncomputable section

theorem low_simple_counterexample :
    REPred LowSimpleSets.constructedSet ∧
      ¬ ComputablePred (fun x => x ∈ LowSimpleSets.constructedSet) ∧
      LowSimpleSets.Low LowSimpleSets.constructedSet ∧
      HasHyperimmuneDegree LowSimpleSets.constructedSet ∧ ¬ High LowSimpleSets.constructedSet := by
  have hn := SimpleSets.simple_undecidable LowSimpleSets.constructed_simple
  have hl := LowSimpleSets.constructed_low
  exact ⟨LowSimpleSets.constructed_enumerable, hn, hl,
    noncomputable_low_hyperimmune LowSimpleSets.constructedSet hl hn,
    low_not_high LowSimpleSets.constructedSet hl⟩

theorem inversion_high_example :
    let A := FriedbergJumpInversion.codedSet (TuringJump.jump haltingDiagonal) 0
    High A ∧ OneGenericSets.IsOneGeneric A ∧
      ¬ ComputablePred (fun x => x ∈ A) ∧
      Reducible A (TuringJump.jump haltingDiagonal) ∧
      ¬ Reducible (TuringJump.jump haltingDiagonal) A := by
  let A := FriedbergJumpInversion.codedSet (TuringJump.jump haltingDiagonal) 0
  have hi := FriedbergJumpInversion.jump_inversion (TuringJump.jump haltingDiagonal)
    (TuringJump.jump_strict haltingDiagonal).1 0
  have hh : High A := hi.1.2
  refine ⟨hh, FriedbergJumpInversion.coded_generic _ _, ?_, hi.2⟩
  intro hc
  have hj : Reducible (TuringJump.jump A) haltingDiagonal :=
    manyOne_imp_reducible (TuringJump.computable_jump_equiv_halting A hc).1
  exact (TuringJump.jump_strict haltingDiagonal).2 (reducible_trans hh hj)

end
end Lemmatheca.Entry.HighDegreesAndDomination
