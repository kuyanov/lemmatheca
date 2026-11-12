import Lemmatheca.HyperimmuneFreeBasisTheorem.Examples
import Lemmatheca.LowBasisTheorem.Basis

/-! Single-cone avoidance from the low and hyperimmune-free basis theorems. -/
namespace Lemmatheca.ComputabilityTheory.HyperimmuneFreeBasisTheorem

open ComputableTreesAndPaths TuringDegrees UniversalComputation
open LowBasisTheorem LowSimpleSets HyperimmuneDegrees EffectivelyClosedClassesAndDnc

/-- The oracle sets from which the given target can be computed. -/
def turingCone (C : Set ℕ) : Set (Set ℕ) := {A | Reducible C A}

theorem cone_avoidance_basis (T : Set ℕ) (hT : IsBinaryTree T)
    (hc : ComputablePred (fun u => u ∈ T)) (hi : ∀ n, HasLevel T n)
    (C : Set ℕ) (hC : ¬ ComputablePred (fun n => n ∈ C)) :
    ∃ A, Path T A ∧ A ∉ turingCone C := by
  classical
  by_cases hCK : Reducible C haltingDiagonal
  · obtain ⟨A, hA, hfree⟩ := hyperimmune_free_basis T hT hc hi
    refine ⟨A, hA, ?_⟩
    intro hCA
    exact hC (hyperimmune_free_below_halting_computable C
      (hyperimmune_free_downward hCA hfree) hCK)
  · obtain ⟨A, hA, hlow⟩ := low_basis T hT hc hi
    refine ⟨A, hA, ?_⟩
    intro hCA
    exact hCK (reducible_trans hCA (low_below_halting A hlow).1)

theorem closed_cone_avoidance (P : Set (Set ℕ)) (hP : EffectivelyClosed P)
    (hne : P.Nonempty) (C : Set ℕ) (hC : ¬ ComputablePred (fun n => n ∈ C)) :
    ∃ A ∈ P, A ∉ turingCone C := by
  obtain ⟨T, hT, hc, he⟩ := (effectively_closed_iff_tree P).mp hP
  obtain ⟨Y, hY⟩ := hne
  have hpY : Path T Y := (Set.ext_iff.mp he Y).mpr hY
  have hi := (all_levels_path T hT).mpr ⟨Y, hpY⟩
  obtain ⟨A, hpA, hcone⟩ := cone_avoidance_basis T hT hc hi C hC
  exact ⟨A, (Set.ext_iff.mp he A).mp hpA, hcone⟩

theorem co_ce_cone_avoidance (T : Set ℕ) (hT : CoCETree T)
    (hne : ∃ A, Path T A) (C : Set ℕ)
    (hC : ¬ ComputablePred (fun n => n ∈ C)) :
    ∃ A, Path T A ∧ A ∉ turingCone C := by
  obtain ⟨r, hr⟩ := (enumerable_iff_index
    (fun u => u ∈ missingWords T)).mp hT.2
  have hindex : EffectiveEnumerations.indexSet r = missingWords T := by
    ext u
    exact (hr u).symm
  obtain ⟨htree, hc, he⟩ := co_ce_conversion T r hindex
  obtain ⟨Y, hY⟩ := hne
  have hi := (all_levels_path (commonStageTree r) htree).mpr ⟨Y, (he Y).mpr hY⟩
  obtain ⟨A, hpA, hcone⟩ := cone_avoidance_basis (commonStageTree r) htree hc hi C hC
  exact ⟨A, (he A).mp hpA, hcone⟩

end Lemmatheca.ComputabilityTheory.HyperimmuneFreeBasisTheorem
