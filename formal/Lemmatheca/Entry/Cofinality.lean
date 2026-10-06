import Lemmatheca.SetTheory.Cofinality

/-! Particular examples and counterexamples for the human entry. -/

namespace Lemmatheca.Entry.Cofinality
open Lemmatheca.SetTheory.Cofinality
open Ordinal Order Set Function
open scoped Ordinal
universe u v w

/-- A cofinal range alone does not justify restricting to a cofinal domain subset.
Take f(2n)=n and f(2n+1)=0, and restrict to the odd numbers. -/
theorem cofinal_restriction_counterexample :
    ∃ (f : ℕ → ℕ) (s : Set ℕ),
      IsCofinal (range f) ∧ IsCofinal s ∧ ¬ IsCofinal (f '' s) := by
  let f : ℕ → ℕ := fun n => if n % 2 = 0 then n / 2 else 0
  refine ⟨f, {n | n % 2 = 1}, ?_, ?_, ?_⟩
  · intro n
    refine ⟨f (2 * n), Set.mem_range_self _, ?_⟩
    simp [f]
  · intro n
    refine ⟨2 * n + 1, ?_, by omega⟩
    simp
  · intro h
    obtain ⟨x, ⟨n, hn, rfl⟩, hx⟩ := h 1
    dsimp [f] at hx
    have hn' : n % 2 ≠ 0 := by change n % 2 = 1 at hn; omega
    simp [hn'] at hx

end Lemmatheca.Entry.Cofinality
