import Lemmatheca.BoundedChangesAndStrongReductions.Snapshots
import Lemmatheca.BeyondComputableChangeBounds.Diagonal
import Lemmatheca.LimitComputability.LimitLemma

/-! The halting-cone characterization and the specified strictness witness. -/
namespace Lemmatheca.ComputabilityTheory.BoundedChangesStrongReductions

open UniversalComputation ComputablyBoundedChanges StrongReductions

noncomputable section

set_option backward.isDefEq.respectTransparency false

theorem wtt_imp_omega (A : Set ℕ) (h : WeakTruthTableReducible A haltingDiagonal) :
    OmegaCE A := by
  obtain ⟨c, u, hcu⟩ := h
  obtain ⟨hc, hb, hz, hl, hn⟩ := bounded_reduction_presentation c u A hcu
  exact ⟨snapshotGuess (OracleProgramNumberings.encodeCode c) u, revisionBudget u,
    hc, hb, hl, hz, hn⟩

theorem halting_cone_characterization (A : Set ℕ) :
    (OmegaCE A ↔ TruthTableReducible A haltingDiagonal) ∧
      (TruthTableReducible A haltingDiagonal ↔ WeakTruthTableReducible A haltingDiagonal) := by
  constructor
  · exact ⟨omega_imp_tt A, fun h => wtt_imp_omega A (tt_imp_wtt h)⟩
  · exact ⟨tt_imp_wtt, fun h => omega_imp_tt A (wtt_imp_omega A h)⟩

theorem diagonal_separates :
    TuringDegrees.Reducible BeyondComputableChangeBounds.diagonalSet haltingDiagonal ∧
      ¬ WeakTruthTableReducible BeyondComputableChangeBounds.diagonalSet haltingDiagonal := by
  have hd := BeyondComputableChangeBounds.diagonal_data
  refine ⟨LimitComputability.limit_reducible _
    ⟨BeyondComputableChangeBounds.diagonalGuess, hd.1, hd.2.1, hd.2.2.2⟩, ?_⟩
  intro h
  exact BeyondComputableChangeBounds.diagonal_not_omega (wtt_imp_omega _ h)

end
end Lemmatheca.ComputabilityTheory.BoundedChangesStrongReductions
