import Lemmatheca.LowBasisTheorem.Construction
import Lemmatheca.LowSimpleSets.Lowness
import Lemmatheca.EffectivelyClosedClassesAndDnc.HaltingMembers

/-! Low paths and the closed-class and binary diagonal-avoidance applications. -/
namespace Lemmatheca.ComputabilityTheory.LowBasisTheorem

open ComputableTreesAndPaths LowSimpleSets EffectivelyClosedClassesAndDnc
open UniversalComputation TuringDegrees

noncomputable section

def LowPath (T : Set ℕ) (X : Set ℕ) : Prop := Path T X ∧ Low X

theorem low_basis (T : Set ℕ) (hT : IsBinaryTree T)
    (hc : ComputablePred (fun u => u ∈ T)) (hi : ∀ n, HasLevel T n) :
    ∃ X, LowPath T X := by
  let S : ℕ → Set ℕ := fun e => restricted T (history (failureQuery T hc) e)
  have hs := history_survival T hT hc hi
  obtain ⟨_, _, X, hX⟩ := nested_levels S
    (fun e => restricted_tree T hT _) hs.2 hs.1
  have hp : Path T X := by
    have hzero := hX 0
    simpa only [S, history, restricted_zero] using hzero
  refine ⟨X, hp, (low_iff_jump_below_halting X).mpr ?_⟩
  exact ⟨jumpCode (failureQuery T hc) (failure_query_primitive T hc),
    jump_code_reduces T hc X hX⟩

theorem closed_low_basis (P : Set (Set ℕ)) (hP : EffectivelyClosed P)
    (hne : P.Nonempty) : ∃ X ∈ P, Low X := by
  obtain ⟨T, hT, hc, he⟩ := (effectively_closed_iff_tree P).mp hP
  obtain ⟨Y, hY⟩ := hne
  have hpY : Path T Y := (Set.ext_iff.mp he Y).mpr hY
  have hi := (all_levels_path T hT).mpr ⟨Y, hpY⟩
  obtain ⟨X, hpX, hlow⟩ := low_basis T hT hc hi
  exact ⟨X, (Set.ext_iff.mp he X).mp hpX, hlow⟩

theorem co_ce_low_basis (T : Set ℕ) (hT : CoCETree T)
    (hne : ∃ X, Path T X) : ∃ X, LowPath T X := by
  obtain ⟨r, hr⟩ := (enumerable_iff_index (fun u => u ∈ missingWords T)).mp hT.2
  have hindex : EffectiveEnumerations.indexSet r = missingWords T := by
    ext u
    exact (hr u).symm
  obtain ⟨htree, hc, he⟩ := co_ce_conversion T r hindex
  obtain ⟨Y, hY⟩ := hne
  have hi := (all_levels_path (commonStageTree r) htree).mpr ⟨Y, (he Y).mpr hY⟩
  obtain ⟨X, hX, hlow⟩ := low_basis (commonStageTree r) htree hc hi
  exact ⟨X, (he X).mp hX, hlow⟩

theorem low_dnc :
    ∃ X : Set ℕ, X ∈ binaryDNCClass ∧ Low X ∧
      ¬ ComputablePred (fun e => e ∈ X) ∧
      Reducible X haltingDiagonal ∧ ¬ Reducible haltingDiagonal X := by
  obtain ⟨X, hX, hlow⟩ := closed_low_basis binaryDNCClass binary_dnc_closed.2
    binary_dnc_example.2.2.1
  exact ⟨X, hX, hlow, binary_dnc_not_computable X hX, low_below_halting X hlow⟩

end
end Lemmatheca.ComputabilityTheory.LowBasisTheorem
