import Lemmatheca.FirstOrderResolution.FirstOrderResolution
import Lemmatheca.EqualityAxioms.EqualityAxioms

namespace Lemmatheca.MathematicalLogic.FirstOrderResolution

open FirstOrder FirstOrder.Language
open HerbrandModels

universe u v
variable {L : Language.{u, v}}

/-- Completeness for the actual original signed equality clauses, using their
specified translation and all five concrete equality axiom clause families. -/
theorem equality_refutational_completeness
    [Nonempty (GroundTerm (EqualityAxioms.Extended L))]
    (Δ : Set (EqualityAxioms.OriginalClause L ℕ)) :
    ¬ EqualityAxioms.OriginalClauseSatisfiable Δ ↔
      Derives (EqualityAxioms.translatedClauses Δ ∪ EqualityAxioms.axiomClauses L) ∅  := by
  rw [EqualityAxioms.originalClauses_equisatisfiable]
  exact refutational_completeness _

end Lemmatheca.MathematicalLogic.FirstOrderResolution
