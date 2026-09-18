import Mathlib.Algebra.Group.Pointwise.Finset.Basic

namespace Lemmatheca.Pending

open scoped Pointwise

/-- A sumset contains an increasing chain of the required length. -/
theorem integer_sumset_increasing_chain (X Y : Finset ℤ)
    (hX : X.Nonempty) (hY : Y.Nonempty) :
    ∃ chain : List ℤ,
      chain.Pairwise (· < ·) ∧
      chain.length = X.card + Y.card - 1 ∧
      ∀ z ∈ chain, z ∈ X + Y := by
  sorry

end Lemmatheca.Pending
