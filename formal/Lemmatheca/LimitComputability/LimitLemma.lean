import Lemmatheca.LimitComputability.StableStage
import Lemmatheca.LimitComputability.BoundedGuesses
import Lemmatheca.PostsTheorem.Correspondence

/-! Shoenfield's set limit lemma and the genuine second-level characterization. -/
namespace Lemmatheca.ComputabilityTheory.LimitComputability

noncomputable section

theorem limit_lemma (A : Set ℕ) :
    LimitComputable A ↔ TuringDegrees.Reducible A UniversalComputation.haltingDiagonal := by
  exact ⟨limit_reducible A, reducible_limit A⟩

theorem limit_delta_two (A : Set ℕ) :
    LimitComputable A ↔ ArithmeticalHierarchy.Delta ∅ 2 A := by
  rw [limit_lemma]
  have hd := PostsTheorem.delta_iff_reducible ∅ 1 A
  have hi : TuringJump.iterate ∅ 1 = TuringJump.jump ∅ := rfl
  rw [hi] at hd
  rw [hd]
  obtain ⟨hJK, hKJ⟩ := TuringJump.empty_jump_equiv_halting
  exact ⟨fun h => TuringDegrees.reducible_trans h (TuringDegrees.manyOne_imp_reducible hKJ),
    fun h => TuringDegrees.reducible_trans h (TuringDegrees.manyOne_imp_reducible hJK)⟩

end
end Lemmatheca.ComputabilityTheory.LimitComputability
