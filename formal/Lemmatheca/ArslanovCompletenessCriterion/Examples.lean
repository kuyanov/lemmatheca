import Lemmatheca.ArslanovCompletenessCriterion.DNC
import Lemmatheca.ComparingEnumerableSets.Classification
import Lemmatheca.LowBasisTheorem.Basis

namespace Lemmatheca.ComputabilityTheory.ArslanovCompletenessCriterion

open UniversalComputation OracleComputation

noncomputable section

theorem low_fpf_non_ce :
    ∃ D : Set ℕ, D ∈ EffectivelyClosedClassesAndDnc.binaryDNCClass ∧
      LowSimpleSets.Low D ∧ ¬ TuringDegrees.Reducible haltingDiagonal D ∧
      ComputesFPF D ∧ ¬ REPred (fun n => n ∈ D) := by
  obtain ⟨D, hD, hlow, _, _, hinc⟩ := LowBasisTheorem.low_dnc
  have hp : ComputesFPF D := computes_fpf_of_dnc D (indicator (fun n => n ∈ D)) hD
    ⟨.query, rfl⟩
  refine ⟨D, hD, hlow, hinc, hp, ?_⟩
  intro hce
  exact hinc ((arslanov_criterion D hce).mpr hp)

theorem candidate_failure (a e n : ℕ) (hn : n ∉ haltingDiagonal) :
    EffectiveEnumerations.indexSet (copySelector a e n) = ∅ ∧
      EffectiveEnumerations.indexSet ComparingEnumerableSets.wholeIndex = Set.univ ∧
      EffectiveEnumerations.indexSet (copySelector a e n) ≠
        EffectiveEnumerations.indexSet ComparingEnumerableSets.wholeIndex := by
  refine ⟨copy_index_empty a e n hn, ComparingEnumerableSets.whole_index_domain, ?_⟩
  rw [copy_index_empty a e n hn, ComparingEnumerableSets.whole_index_domain]
  exact Set.empty_ne_univ

end
end Lemmatheca.ComputabilityTheory.ArslanovCompletenessCriterion
