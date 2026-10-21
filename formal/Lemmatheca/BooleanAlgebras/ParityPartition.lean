import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic

/-! The elementary infinite partition used by the finite/cofinite algebra example. -/
namespace Lemmatheca.SetTheory.FiniteErrors
open Set

/-- The two residue classes modulo two form an infinite partition. -/
theorem parity_partition :
    ({n : ℕ | n % 2 = 0} : Set ℕ).Infinite ∧
    ({n : ℕ | n % 2 = 1} : Set ℕ).Infinite ∧
    ({n : ℕ | n % 2 = 0} ∩ {n : ℕ | n % 2 = 1} : Set ℕ) = ∅ ∧
    ({n : ℕ | n % 2 = 0} ∪ {n : ℕ | n % 2 = 1} : Set ℕ) = univ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply infinite_of_injective_forall_mem (f := fun n : ℕ => 2 * n)
    · intro m n h; dsimp at h; omega
    · intro n; simp
  · apply infinite_of_injective_forall_mem (f := fun n : ℕ => 2 * n + 1)
    · intro m n h; dsimp at h; omega
    · intro n; simp
  · ext n; simp
  · ext n; simp; omega

end Lemmatheca.SetTheory.FiniteErrors
