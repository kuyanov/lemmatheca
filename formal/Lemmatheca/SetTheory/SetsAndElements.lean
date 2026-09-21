import Mathlib.Data.Set.Card
import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Tactic.NormNum

/-!
# Sets and their elements

Reviewed declarations for Definition 1 of the sets-and-maps entry.
The foundational definitions are linked directly to Mathlib.Data.Set.Defs:
`Set`, `Set.Mem`, `Set.ofPred`, and `Set.insert`.

Sets here have a specified ambient type. The human text's discussion of
foundations and its notation for number systems are conventions, not additional
theorem claims. In particular, this file makes no claim about a universal set
containing objects of every type.

The proofs below preserve the accepted statements and their review hashes.
-/

namespace Lemmatheca.SetsAndMaps

universe u

variable {α : Type u}

/-- Exchanging two successive insertions does not change a set. -/
theorem insert_order (a b : α) (s : Set α) :
    insert a (insert b s) = insert b (insert a s) := by
  ext x
  simp only [Set.mem_insert_iff, or_left_comm]

/-- Repeating an element in an enumeration does not change a set. -/
theorem insert_repetition (a : α) (s : Set α) :
    insert a (insert a s) = insert a s := by
  ext x
  simp only [Set.mem_insert_iff, or_self_left]

/-- The concrete set {2, 5, 8} in the human text has three elements. -/
theorem three_element_example_card : ({2, 5, 8} : Set ℕ).ncard = 3 := by
  norm_num

/-- The set E of even natural numbers; Lean's natural numbers include zero. -/
def evenNaturals : Set ℕ := {n | Even n}

/-- Zero belongs to the even-number set used in Definition 1. -/
theorem zero_mem_evenNaturals : 0 ∈ evenNaturals := by
  exact ⟨0, rfl⟩

end Lemmatheca.SetsAndMaps
