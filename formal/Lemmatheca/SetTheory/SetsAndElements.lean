import Mathlib.Data.Set.Card
import Mathlib.Algebra.Group.Nat.Even

/-!
# Sets and their elements

Proposed declarations for Definition 1 of the sets-and-maps entry.
The foundational definitions are linked directly to Mathlib.Data.Set.Defs:
`Set`, `Set.Mem`, `Set.ofPred`, and `Set.insert`.

Sets here have a specified ambient type. The human text's discussion of
foundations and its notation for number systems are conventions, not additional
theorem claims. In particular, this file makes no claim about a universal set
containing objects of every type.

The theorem statements below await human review and a separate proof-writing
pass. Their `sorry` terms check the statements' types but do not prove them.
-/

namespace Lemmatheca.SetsAndMaps

universe u

variable {α : Type u}

/-- Exchanging two successive insertions does not change a set. -/
theorem insert_order (a b : α) (s : Set α) :
    insert a (insert b s) = insert b (insert a s) := by
  sorry

/-- Repeating an element in an enumeration does not change a set. -/
theorem insert_repetition (a : α) (s : Set α) :
    insert a (insert a s) = insert a s := by
  sorry

/-- The concrete set {2, 5, 8} in the human text has three elements. -/
theorem three_element_example_card : ({2, 5, 8} : Set ℕ).ncard = 3 := by
  sorry

/-- The set E of even natural numbers; Lean's natural numbers include zero. -/
def evenNaturals : Set ℕ := {n | Even n}

/-- Zero belongs to the even-number set used in Definition 1. -/
theorem zero_mem_evenNaturals : 0 ∈ evenNaturals := by
  sorry

end Lemmatheca.SetsAndMaps
