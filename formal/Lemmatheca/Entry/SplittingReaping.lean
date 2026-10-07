import Lemmatheca.SetTheory.SplittingReaping

namespace Lemmatheca.Entry.SplittingReaping
open Set Lemmatheca.SetTheory.SplittingReaping

theorem parity_example :
    Splits {n : ℕ | Even n} univ ∧ ¬ Splits {n : ℕ | Even n} {n : ℕ | Even n} := by
  have he : ({n : ℕ | Even n} : Set ℕ).Infinite := by
    apply infinite_of_injective_forall_mem (f := fun n : ℕ => 2 * n)
    · intro m n h; dsimp at h; omega
    · intro n; exact ⟨n, by omega⟩
  have ho : (univ \ {n : ℕ | Even n} : Set ℕ).Infinite := by
    apply infinite_of_injective_forall_mem (f := fun n : ℕ => 2 * n + 1)
    · intro m n h; dsimp at h; omega
    · intro n
      refine ⟨mem_univ _, ?_⟩
      rintro ⟨k, hk⟩
      omega
  constructor
  · exact ⟨by simpa using he, ho⟩
  · intro h
    exact h.2 (by simp)

end Lemmatheca.Entry.SplittingReaping
