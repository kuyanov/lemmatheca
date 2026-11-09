import Lemmatheca.FriedbergJumpInversion.Recovery
import Lemmatheca.TuringJump.Degrees

/-! The exact join yields inversion, its degree range, and distinct inverse degrees. -/
namespace Lemmatheca.ComputabilityTheory.FriedbergJumpInversion

open OracleComputation OracleProgramNumberings IncomparableTuringDegrees
  ComputableTreesAndPaths PostsTheorem UniversalComputation OneGenericSets TuringDegrees TuringJump

noncomputable section
set_option autoImplicit false

theorem exact_join (B : Set ℕ) (hB : Reducible haltingDiagonal B) (rho : ℕ) :
    Equivalent B (join (codedSet B rho) haltingDiagonal) := by
  refine ⟨⟨fixedDecoderProgram rho, decoder_reduces B rho⟩, ?_⟩
  obtain ⟨d, hd⟩ := hB
  exact (join_reducible_iff (codedSet B rho) haltingDiagonal B).mpr
    ⟨⟨fixedCharacteristicProgram d rho, fixed_characteristic_reduces B d hd rho⟩, ⟨d, hd⟩⟩

theorem jump_inversion (B : Set ℕ) (hB : Reducible haltingDiagonal B) (rho : ℕ) :
    Equivalent (jump (codedSet B rho)) B ∧
      Reducible (codedSet B rho) B ∧ ¬ Reducible B (codedSet B rho) := by
  have hg := generalized_low _ (coded_generic B rho)
  have hj := exact_join B hB rho
  have he : Equivalent (jump (codedSet B rho)) B :=
    ⟨reducible_trans hg.1 hj.2, reducible_trans hj.1 hg.2⟩
  have hb : Reducible (codedSet B rho) B := by
    obtain ⟨d, hd⟩ := hB
    exact ⟨fixedCharacteristicProgram d rho, fixed_characteristic_reduces B d hd rho⟩
  exact ⟨he, hb, fun h => (jump_strict (codedSet B rho)).2 (reducible_trans he.1 h)⟩

theorem degree_jump_range (b : Degree) :
    (∃ a : Degree, degreeJump a = b) ↔ degree haltingDiagonal ≤ b := by
  constructor
  · rintro ⟨a, rfl⟩
    obtain ⟨A, rfl⟩ := degree_surjective a
    rw [degree_jump_degree]
    exact LowSimpleSets.halting_below_jump A
  · intro hb
    obtain ⟨B, rfl⟩ := degree_surjective b
    refine ⟨degree (codedSet B 0), ?_⟩
    rw [degree_jump_degree]
    exact Quotient.sound (jump_inversion B hb 0).1

theorem degree_jump_collision :
    degreeJump zeroDegree = degreeJump (degree (constructedSet 0)) ∧
      zeroDegree ≠ degree (constructedSet 0) := by
  constructor
  · rw [zero_jump_halting, degree_jump_degree]
    exact Quotient.sound ⟨(constructed_low 0).2, (constructed_low 0).1⟩
  · intro h
    exact generic_noncomputable _ (constructed_generic 0)
      ((degree_eq_zero_iff _).mp h.symm)

end
end Lemmatheca.ComputabilityTheory.FriedbergJumpInversion
