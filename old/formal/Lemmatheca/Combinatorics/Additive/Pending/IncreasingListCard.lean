import Mathlib.Data.Finset.Card

namespace Lemmatheca.Pending

/-- An increasing list contained in a finite set cannot exceed its cardinality. -/
theorem increasing_list_length_le_card (S : Finset ℤ) (chain : List ℤ)
    (hincreasing : chain.Pairwise (· < ·))
    (hmem : ∀ z ∈ chain, z ∈ S) :
    chain.length ≤ S.card := by
  sorry

end Lemmatheca.Pending
