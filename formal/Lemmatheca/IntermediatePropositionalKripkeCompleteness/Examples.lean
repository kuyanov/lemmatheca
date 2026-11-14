import Lemmatheca.IntermediatePropositionalKripkeCompleteness.Completeness
import Lemmatheca.IntuitionisticPropositionalTreeCountermodels.Examples
import Lemmatheca.PropositionalWeakExcludedMiddle.Frames

namespace Lemmatheca.Entry.IntermediatePropositionalKripkeCompleteness

open Lemmatheca.ProofTheory.Intuitionistic
open Kripke StrictPaths
open Lemmatheca.Entry.IntuitionisticPropositionalTreeCountermodels

/-- These are the same six-path diamond, the same root, and the two displayed terminal paths. -/
theorem diamond_tree_nonjoining :
    root diamondRoot ≤ diamondPath 4 ∧
      root diamondRoot ≤ diamondPath 5 ∧
      ¬ ∃ z : Path diamondRoot, diamondPath 4 ≤ z ∧ diamondPath 5 ≤ z := by
  refine ⟨root_le _, root_le _, ?_⟩
  rintro ⟨z, h₄, h₅⟩
  rcases predecessors_compare (diamondPath 4) (diamondPath 5) z h₄ h₅ with h | h
  · exact diamond_incomparable.1 h
  · exact diamond_incomparable.2 h

theorem diamond_tree_not_directed :
    ¬ WeakExcludedMiddle.DirectedFutureCones (Path diamondRoot) := by
  intro h
  have hn := diamond_tree_nonjoining
  exact hn.2.2 (h (root diamondRoot) (diamondPath 4) (diamondPath 5) hn.1 hn.2.1)

/-- Atom zero is verified precisely on the upward cone of the actual first terminal path. -/
theorem diamond_tree_countervaluation :
    ¬ Forces (WeakExcludedMiddle.upsetModel (diamondPath 4))
      (root diamondRoot) (WeakExcludedMiddle.wem (.atom 0)) := by
  have hn := diamond_tree_nonjoining
  exact (WeakExcludedMiddle.nonjoining_countervaluation (root diamondRoot)
    (diamondPath 4) (diamondPath 5) hn.1 hn.2.1 hn.2.2).2.2.2.2

end Lemmatheca.Entry.IntermediatePropositionalKripkeCompleteness
