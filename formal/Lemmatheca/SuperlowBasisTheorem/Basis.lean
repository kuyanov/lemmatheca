import Lemmatheca.SuperlowBasisTheorem.Tables
import Lemmatheca.TruthTableAndWeakTruthTableReductions.Characterization

/-! The original common paths, with the specified finite history table. -/
namespace Lemmatheca.ComputabilityTheory.SuperlowBasisTheorem

open UniversalComputation OracleComputation OracleProgramNumberings TuringDegrees
open LowBasisTheorem ComputableTreesAndPaths StrongReductions EffectivelyClosedClassesAndDnc

noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem common_path_table (T : Set ℕ) (hc : ComputablePred (fun u => u ∈ T))
    (X : Set ℕ) (hX : ∀ e, Path (restricted T (history (failureQuery T hc) e)) X) :
    Presents (historyData (failureQuery T hc)) (TuringJump.jump X) haltingDiagonal := by
  refine ⟨history_scheme _ (failure_query_primitive T hc), ?_⟩
  intro e
  exact (history_table_recorded_bit (failureQuery T hc) e).trans
    (exact_jump T hc X hX e).symm

theorem same_common_path (T : Set ℕ) (hc : ComputablePred (fun u => u ∈ T))
    (X : Set ℕ) (hX : ∀ e, Path (restricted T (history (failureQuery T hc) e)) X) :
    Superlow X ∧ AllOracleTotal (jumpCode (failureQuery T hc) (failure_query_primitive T hc)) ∧
      Reduces (jumpCode (failureQuery T hc) (failure_query_primitive T hc))
        (TuringJump.jump X) haltingDiagonal := by
  exact ⟨⟨historyData (failureQuery T hc), common_path_table T hc X hX⟩,
    jump_code_total _ (failure_query_primitive T hc), jump_code_reduces T hc X hX⟩

theorem superlow_basis (T : Set ℕ) (hT : IsBinaryTree T)
    (hc : ComputablePred (fun u => u ∈ T)) (hi : ∀ n, HasLevel T n) :
    ∃ X, Path T X ∧ Superlow X := by
  let S : ℕ → Set ℕ := fun e => restricted T (history (failureQuery T hc) e)
  have hs := history_survival T hT hc hi
  obtain ⟨_, _, X, hX⟩ := nested_levels S
    (fun e => restricted_tree T hT _) hs.2 hs.1
  have hp : Path T X := by
    have hzero := hX 0
    simpa only [S, history, restricted_zero] using hzero
  exact ⟨X, hp, (same_common_path T hc X hX).1⟩

theorem closed_superlow_basis (P : Set (Set ℕ)) (hP : EffectivelyClosed P)
    (hne : P.Nonempty) : ∃ X ∈ P, Superlow X := by
  obtain ⟨T, hT, hc, he⟩ := (effectively_closed_iff_tree P).mp hP
  obtain ⟨Y, hY⟩ := hne
  have hpY : Path T Y := (Set.ext_iff.mp he Y).mpr hY
  have hi := (all_levels_path T hT).mpr ⟨Y, hpY⟩
  obtain ⟨X, hpX, hlow⟩ := superlow_basis T hT hc hi
  exact ⟨X, (Set.ext_iff.mp he X).mp hpX, hlow⟩

theorem co_ce_superlow_basis (T : Set ℕ) (hT : CoCETree T) (hne : ∃ X, Path T X) :
    ∃ X, Path T X ∧ Superlow X := by
  obtain ⟨r, hr⟩ := (enumerable_iff_index (fun u => u ∈ missingWords T)).mp hT.2
  have hindex : EffectiveEnumerations.indexSet r = missingWords T := by
    ext u
    exact (hr u).symm
  obtain ⟨htree, hc, he⟩ := co_ce_conversion T r hindex
  obtain ⟨Y, hY⟩ := hne
  have hi := (all_levels_path (commonStageTree r) htree).mpr ⟨Y, (he Y).mpr hY⟩
  obtain ⟨X, hX, hlow⟩ := superlow_basis (commonStageTree r) htree hc hi
  exact ⟨X, (he X).mp hX, hlow⟩

theorem superlow_dnc :
    ∃ X : Set ℕ, X ∈ binaryDNCClass ∧ Superlow X ∧
      ¬ ComputablePred (fun e => e ∈ X) ∧
      Reducible X haltingDiagonal ∧ ¬ Reducible haltingDiagonal X := by
  obtain ⟨X, hX, hsuper⟩ := closed_superlow_basis binaryDNCClass binary_dnc_closed.2
    binary_dnc_example.2.2.1
  exact ⟨X, hX, hsuper, binary_dnc_not_computable X hX,
    LowSimpleSets.low_below_halting X (superlow_low X hsuper)⟩

end
end Lemmatheca.ComputabilityTheory.SuperlowBasisTheorem
