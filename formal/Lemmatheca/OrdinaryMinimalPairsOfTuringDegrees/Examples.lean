import Lemmatheca.OrdinaryMinimalPairsOfTuringDegrees.Core

namespace Lemmatheca.Entry.OrdinaryMinimalPairsOfTuringDegrees

open Lemmatheca.ComputabilityTheory

theorem joins_not_minimal (a b d : TuringDegrees.Degree) (hd : d ≠ TuringDegrees.zeroDegree) :
    ¬ OrdinaryMinimalPairs.MinimalPair (a ⊔ d) (b ⊔ d) := by
  intro h
  exact hd (h.2.2 d le_sup_right le_sup_right)

theorem joins_collapse (a b : TuringDegrees.Degree) :
    a ⊔ (a ⊔ b) = a ⊔ b ∧ b ⊔ (a ⊔ b) = a ⊔ b := by
  exact ⟨sup_left_idem a b, by rw [sup_left_comm, sup_idem]⟩

end Lemmatheca.Entry.OrdinaryMinimalPairsOfTuringDegrees
