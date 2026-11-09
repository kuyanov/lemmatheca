import Lemmatheca.PostsTheorem.Hierarchy

/-! Exact witnesses for the relative-halting and nonoptimal-prefix questions. -/
namespace Lemmatheca.Entry.PostsTheorem

open Lemmatheca.ComputabilityTheory
open Lemmatheca.ComputabilityTheory.PostsTheorem
open ArithmeticalHierarchy TuringJump

theorem halting_jump_equiv :
    ManyOneEquiv (jump UniversalComputation.haltingDiagonal) (iterate ∅ 2) := by
  exact ⟨jump_monotone (TuringDegrees.manyOne_imp_reducible empty_jump_equiv_halting.2),
    jump_monotone (TuringDegrees.manyOne_imp_reducible empty_jump_equiv_halting.1)⟩

theorem halting_jump_levels :
    SigmaComplete ∅ 2 (jump UniversalComputation.haltingDiagonal) ∧
      ¬ Pi ∅ 2 (jump UniversalComputation.haltingDiagonal) ∧
      ¬ Delta ∅ 2 (jump UniversalComputation.haltingDiagonal) := by
  have hc := (complete_iff_iterate ∅ 2 (by omega) _).mpr halting_jump_equiv
  have hb := complete_boundaries ∅ 2 (by omega) _ hc
  exact ⟨hc, hb.1, hb.2.1⟩

theorem jump_padded_levels (B : Set ℕ) :
    Sigma B 2 (jump B) ∧ Delta B 2 (jump B) ∧ ¬ Delta B 1 (jump B) ∧
      Sigma B 1 (jump B) ∧ ¬ Sigma B 0 (jump B) := by
  have hs : Sigma B 1 (jump B) := (sigma_iff_ce B 0 _).mpr (jump_ce B)
  refine ⟨level_padding B 1 true true _ hs,
    (delta_iff_reducible B 1 _).mpr (TuringDegrees.reducible_refl _), ?_, hs, ?_⟩
  · intro h
    exact (jump_strict B).2 ((delta_iff_reducible B 0 _).mp h)
  · intro h
    exact jump_not_decidable B ((level_zero_iff B true _).mp h)

end Lemmatheca.Entry.PostsTheorem
