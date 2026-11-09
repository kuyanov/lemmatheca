import Lemmatheca.PaDegrees.Comparison
import Lemmatheca.PaDegrees.Completion
import Lemmatheca.PaDegrees.Paths
import Lemmatheca.LowBasisTheorem.Basis

set_option autoImplicit false

namespace Lemmatheca.ComputabilityTheory.PaDegrees

open UniversalComputation TuringDegrees OracleComputation EffectivelyClosedClassesAndDnc
open LowBasisTheorem LowSimpleSets TuringJump

noncomputable section

theorem pa_iff_computes_dnc (A : Set ℕ) : IsPAOracle A ↔ ComputesDNC A := by
  constructor
  · rintro ⟨T, hT, hTA⟩
    have hD := consistent_Q_extension_dnc T
      (fun _ h => hT.1 (Or.inl h)) hT.2.1 hT.2.2.2
    exact ⟨completionDNC T, hD,
      reducible_trans ⟨completionDNCCode, completion_dnc_code_eval T⟩ hTA⟩
  · rintro ⟨D, hD, hDA⟩
    exact ⟨completedTheory D, greedy_completion D hD,
      reducible_trans ⟨completionProgram, completion_program_reduces D hD⟩ hDA⟩

theorem computes_dnc_iff_paths (A : Set ℕ) : ComputesDNC A ↔ PathProperty A := by
  constructor
  · rintro ⟨D, hD, hDA⟩ T hT hc hne
    obtain ⟨X, hX, hXD⟩ := dnc_path_property D hD T hT hc hne
    exact ⟨X, hX, reducible_trans hXD hDA⟩
  · exact path_property_computes_dnc A

theorem pa_upward {A B : Set ℕ} (hA : IsPAOracle A) (hAB : Reducible A B) :
    IsPAOracle B := by
  obtain ⟨T, hT, hTA⟩ := hA
  exact ⟨T, hT, reducible_trans hTA hAB⟩

theorem pa_degree_invariant {A B : Set ℕ} (hAB : Equivalent A B) :
    IsPAOracle A ↔ IsPAOracle B := by
  exact ⟨fun h => pa_upward h hAB.1, fun h => pa_upward h hAB.2⟩

theorem pa_degree_iff_oracle (A : Set ℕ) : PADegree (degree A) ↔ IsPAOracle A := by
  constructor
  · rintro ⟨B, heq, hB⟩
    have hBA : Equivalent B A := by
      change B ∈ literalClass A
      rw [← classOf_degree A]
      exact heq
    exact (pa_degree_invariant hBA).mp hB
  · intro hA
    exact ⟨A, rfl, hA⟩

theorem halting_above_pa (A : Set ℕ) (hA : Reducible haltingDiagonal A) :
    IsPAOracle A := by
  apply (pa_iff_computes_dnc A).mpr
  exact ⟨binaryDNCPath, binary_dnc_example.1,
    reducible_trans ⟨binaryDNCCode, binary_dnc_example.2.1⟩ hA⟩

theorem pa_not_computable (A : Set ℕ) (hA : IsPAOracle A) :
    ¬ ComputablePred (fun n => n ∈ A) := by
  intro hc
  obtain ⟨D, hD, hDA⟩ := (pa_iff_computes_dnc A).mp hA
  exact binary_dnc_not_computable D hD (computable_of_reducible hDA hc)

theorem low_pa_degree : ∃ D : Set ℕ, D ∈ binaryDNCClass ∧ IsPAOracle D ∧ Low D ∧
    zeroDegree < degree D ∧ degree D < degree haltingDiagonal := by
  obtain ⟨D, hD, hlow, hnc, hDK, hnKD⟩ := low_dnc
  refine ⟨D, hD, (pa_iff_computes_dnc D).mpr ⟨D, hD, reducible_refl D⟩,
    hlow, ?_, ?_⟩
  · exact lt_of_le_of_ne (zeroDegree_le _) (fun h =>
      hnc ((degree_eq_zero_iff D).mp h.symm))
  · apply lt_of_le_not_ge
    · exact hDK
    · exact hnKD

end
end Lemmatheca.ComputabilityTheory.PaDegrees
