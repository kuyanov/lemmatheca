import Lemmatheca.HyperimmuneFreeBasisTheorem.Basis
import Lemmatheca.DominationAndHyperimmuneDegrees.Approximation

set_option autoImplicit false
namespace Lemmatheca.ComputabilityTheory.HyperimmuneFreeBasisTheorem
open ComputableTreesAndPaths UniversalComputation HyperimmuneDegrees
open TuringDegrees LowSimpleSets PaDegrees EffectivelyClosedClassesAndDnc
noncomputable section
local instance hfbExamplesPropDecidable (p : Prop) : Decidable p := Classical.propDecidable p

theorem noncomputable_free_not_low (A : Set ℕ) (hA : HyperimmuneFree A)
    (hn : ¬ ComputablePred (fun n => n ∈ A)) : ¬ Low A := by
  intro hlow
  exact (hyperimmune_or_free A).mp (noncomputable_low_hyperimmune A hlow hn) hA

theorem hyperimmune_free_pa_outside_halting : ∃ A : Set ℕ,
    Path kleeneTree A ∧ A ∈ binaryDNCClass ∧ HyperimmuneFree A ∧ IsPAOracle A ∧
      ¬ ComputablePred (fun n => n ∈ A) ∧ ¬ Reducible A haltingDiagonal ∧ ¬ Low A := by
  obtain ⟨A, hpA, hdnc, hfree, hpa, hn⟩ := hyperimmune_free_pa
  refine ⟨A, hpA, hdnc, hfree, hpa, hn, ?_, noncomputable_free_not_low A hfree hn⟩
  intro hAK
  exact hn (hyperimmune_free_below_halting_computable A hfree hAK)

theorem halting_selected_dnc_not_free : ¬ HyperimmuneFree binaryDNCPath := by
  intro hfree
  exact binary_dnc_example.2.2.2
    (hyperimmune_free_below_halting_computable binaryDNCPath hfree
      ⟨binaryDNCCode, binary_dnc_example.2.1⟩)

end
end Lemmatheca.ComputabilityTheory.HyperimmuneFreeBasisTheorem
