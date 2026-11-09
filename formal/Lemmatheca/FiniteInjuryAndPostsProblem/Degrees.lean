import Lemmatheca.FiniteInjuryAndPostsProblem.Verification
import Lemmatheca.IncomparableTuringDegrees.DegreeBounds
import Lemmatheca.ProductiveAndCreativeSets.Productivity
import Lemmatheca.TuringJump.Recoding

/-! The actual enumerated sets solve Post's problem. -/
namespace Lemmatheca.ComputabilityTheory.FiniteInjury

open TuringDegrees TuringJump UniversalComputation

theorem constructed_bounds : Reducible leftSet (jump ∅) ∧ Reducible rightSet (jump ∅) := by
  have hKJ : Reducible haltingDiagonal (jump ∅) :=
    manyOne_imp_reducible empty_jump_equiv_halting.2
  exact ⟨reducible_trans
      (manyOne_imp_reducible (ProductiveAndCreativeSets.diagonal_complete
        constructed_enumerable.1)) hKJ,
    reducible_trans
      (manyOne_imp_reducible (ProductiveAndCreativeSets.diagonal_complete
        constructed_enumerable.2)) hKJ⟩

theorem posts_solution :
    (zeroDegree < degree leftSet ∧ degree leftSet < degree (jump ∅)) ∧
      (zeroDegree < degree rightSet ∧ degree rightSet < degree (jump ∅)) := by
  exact IncomparableTuringDegrees.incomparable_between leftSet rightSet (jump ∅)
    friedberg_muchnik.2.2.1 friedberg_muchnik.2.2.2
    constructed_bounds.1 constructed_bounds.2

theorem constructed_undecidable :
    ¬ ComputablePred leftSet ∧ ¬ ComputablePred rightSet := by
  exact IncomparableTuringDegrees.incomparable_noncomputable leftSet rightSet
    friedberg_muchnik.2.2.1 friedberg_muchnik.2.2.2

theorem halting_not_reducible :
    ¬ Reducible (jump ∅) leftSet ∧ ¬ Reducible (jump ∅) rightSet := by
  constructor
  · intro h
    exact friedberg_muchnik.2.2.2 (reducible_trans constructed_bounds.2 h)
  · intro h
    exact friedberg_muchnik.2.2.1 (reducible_trans constructed_bounds.1 h)

theorem many_one_incomparable : ¬ leftSet ≤₀ rightSet ∧ ¬ rightSet ≤₀ leftSet := by
  exact ⟨fun h => friedberg_muchnik.2.2.1 (manyOne_imp_reducible h),
    fun h => friedberg_muchnik.2.2.2 (manyOne_imp_reducible h)⟩

theorem no_halting_many_one_reduction :
    ¬ haltingDiagonal ≤₀ leftSet ∧ ¬ haltingDiagonal ≤₀ rightSet := by
  have hJK : Reducible (jump ∅) haltingDiagonal :=
    manyOne_imp_reducible empty_jump_equiv_halting.1
  exact ⟨fun h => halting_not_reducible.1
      (reducible_trans hJK (manyOne_imp_reducible h)),
    fun h => halting_not_reducible.2
      (reducible_trans hJK (manyOne_imp_reducible h))⟩

theorem not_ce_complete :
    ¬ (∀ S : Set ℕ, REPred S → S ≤₀ leftSet) ∧
      ¬ (∀ S : Set ℕ, REPred S → S ≤₀ rightSet) := by
  exact ⟨fun h => no_halting_many_one_reduction.1
      (h haltingDiagonal haltingDiagonal_enumerable),
    fun h => no_halting_many_one_reduction.2
      (h haltingDiagonal haltingDiagonal_enumerable)⟩

end Lemmatheca.ComputabilityTheory.FiniteInjury
