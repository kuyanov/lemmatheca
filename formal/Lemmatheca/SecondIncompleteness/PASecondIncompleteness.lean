import Lemmatheca.SecondIncompleteness.Lob
import Lemmatheca.ArithmeticProofPredicates.ArithmeticProofPredicates

open Lemmatheca.MathematicalLogic Lemmatheca.ModelTheory Lemmatheca.ComputabilityTheory

/-! Second incompleteness for the same PA program graph, unary predicate and
consistency sentence as the arithmetic proof construction. -/
namespace Lemmatheca.ProofTheory.PASecondIncompleteness
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic ArithmeticTheories FirstOrderProofs
noncomputable section

/-- The existing construction discharges the exact general conditions. -/
theorem pa_derivabilityConditions :
    Lob.DerivabilityConditions PA ArithmeticProofPredicates.proofPredicate := by
  refine ⟨?_, ?_, ?_⟩
  · intro A hA
    exact ArithmeticProofPredicates.derivability_one A hA
  · intro A B
    exact ArithmeticProofPredicates.derivability_two A B
  · intro A
    exact ArithmeticProofPredicates.derivability_three A

theorem pa_second_incompleteness (hPA : Consistent PA) :
    ¬ Derives PA ArithmeticProofPredicates.consistency := by
  exact Lob.second_incompleteness pa_derivabilityConditions
    (fun _ h => Or.inl h) hPA

theorem negated_consistency_extension (hPA : Consistent PA) :
    Consistent (insert ArithmeticProofPredicates.consistency.not PA) := by
  by_contra h
  exact pa_second_incompleteness hPA (derives_iff_not_consistent_neg.mpr h)

theorem extension_not_standard (hPA : Consistent PA) :
    ¬ ℕ ⊨ (insert ArithmeticProofPredicates.consistency.not PA) := by
  intro h
  have hn := h.realize_of_mem ArithmeticProofPredicates.consistency.not
    (Set.mem_insert _ _)
  rw [Sentence.realize_not] at hn
  exact hn (ArithmeticProofPredicates.consistency_standard.mpr hPA)

end
end Lemmatheca.ProofTheory.PASecondIncompleteness
