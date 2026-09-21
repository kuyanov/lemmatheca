import Mathlib.Data.Set.Card
import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Tactic.NormNum

/-!
# Sets-and-maps entry: sets and their elements

The concrete three-element set and the even-natural-number set used in the entry.
Lean's natural numbers include zero.
-/

namespace Lemmatheca.Entry.SetsAndMaps

/-- The concrete set {2, 5, 8} in the human text has three elements. -/
theorem three_element_example_card : ({2, 5, 8} : Set ℕ).ncard = 3 := by
  norm_num

/-- The set E of even natural numbers; Lean's natural numbers include zero. -/
def evenNaturals : Set ℕ := {n | Even n}

end Lemmatheca.Entry.SetsAndMaps
