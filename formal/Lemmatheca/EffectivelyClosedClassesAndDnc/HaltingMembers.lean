import Lemmatheca.EffectivelyClosedClassesAndDnc.Diagonal

/-! The specified earlier halting-selected paths and their actual oracle programs. -/
namespace Lemmatheca.ComputabilityTheory.EffectivelyClosedClassesAndDnc

open ComputableTreesAndPaths UniversalComputation EffectiveEnumerations

noncomputable section

def closedSelectedPath (r : ℕ) : Set ℕ :=
  selectedPath (deadQuery (commonStageTree r) (common_stage_computable r))

def closedPathCode (r : ℕ) : OracleComputation.Code :=
  pathCode (deadQuery (commonStageTree r) (common_stage_computable r))
    (dead_query_primitive (commonStageTree r) (common_stage_computable r))

theorem closed_class_halting_member (F : Set ℕ) (r : ℕ)
    (hindex : indexSet r = F) (hne : (avoidance F).Nonempty) :
    (∀ n, HasLevel (commonStageTree r) n) ∧
      closedSelectedPath r ∈ avoidance F ∧
      TuringDegrees.Reduces (closedPathCode r) (closedSelectedPath r) haltingDiagonal := by
  have he : {X | Path (commonStageTree r) X} = avoidance F := by
    rw [common_stage_paths, hindex]
  obtain ⟨X, hX⟩ := hne
  have hp : Path (commonStageTree r) X := (Set.ext_iff.mp he X).mpr hX
  have hi := (all_levels_path _ (common_stage_is_tree r)).mpr ⟨X, hp⟩
  have hs := halting_oracle_path (commonStageTree r) (common_stage_is_tree r)
    (common_stage_computable r) hi
  exact ⟨hi, (Set.ext_iff.mp he (closedSelectedPath r)).mp hs.1, hs.2⟩

private theorem kleeneComputable : ComputablePred (fun u => u ∈ kleeneTree) :=
  kleene_tree.2.1

def binaryDNCPath : Set ℕ := selectedPath (deadQuery kleeneTree kleeneComputable)

def binaryDNCCode : OracleComputation.Code :=
  pathCode (deadQuery kleeneTree kleeneComputable)
    (dead_query_primitive kleeneTree kleeneComputable)

theorem binary_dnc_example :
    binaryDNCPath ∈ binaryDNCClass ∧
      TuringDegrees.Reduces binaryDNCCode binaryDNCPath haltingDiagonal ∧
      binaryDNCClass.Nonempty ∧
      ¬ ComputablePred (fun e => e ∈ binaryDNCPath) := by
  have hp := halting_oracle_path kleeneTree kleene_tree.1 kleeneComputable
    kleene_tree.2.2.1
  have hd : binaryDNCPath ∈ binaryDNCClass := by
    rw [dnc_separator_tree]
    exact hp.1
  exact ⟨hd, hp.2, ⟨binaryDNCPath, hd⟩, binary_dnc_not_computable _ hd⟩

end
end Lemmatheca.ComputabilityTheory.EffectivelyClosedClassesAndDnc
