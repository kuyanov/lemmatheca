import Lemmatheca.ComputablyBoundedChanges.Basic
import Lemmatheca.LimitComputability.Examples

/-! A deliberately loose input bound on a constant approximation. -/
namespace Lemmatheca.Entry.ComputablyBoundedChanges

open Lemmatheca.ComputabilityTheory
open UniversalComputation LimitComputability DifferenceEnumerable FiniteMindChanges
open ComputablyBoundedChanges

set_option backward.isDefEq.respectTransparency false

theorem loose_bound_example :
    Computable₂ (fun (_s _x : ℕ) => 0) ∧ Binary (fun (_s _x : ℕ) => 0) ∧
      StartsZero (fun (_s _x : ℕ) => 0) ∧
      Converges (fun (_s _x : ℕ) => 0) (∅ : Set ℕ) ∧
      ComputableBound (fun (_s _x : ℕ) => 0) (fun x => x) ∧
      (∀ k : ℕ, ∃ x, k < x) ∧ NCE 0 (∅ : Set ℕ) := by
  classical
  have hcount : ∀ s x, changeCount (fun (_s _x : ℕ) => 0) s x = 0 := by
    intro s x
    induction s with
    | zero => rfl
    | succ s ih =>
        change changeCount (fun (_s _x : ℕ) => 0) s x + (if (0 : ℕ) = 0 then 0 else 1) = 0
        rw [ih]
        rfl
  refine ⟨Computable.const 0, fun _ _ => Or.inl rfl, fun _ => rfl, ?_,
    ⟨Computable.id, ?_⟩, ?_, (nce_zero_iff (∅ : Set ℕ)).mpr rfl⟩
  · intro x
    exact ⟨0, fun _ _ => by simp [indicator, EmptyCollection.emptyCollection]⟩
  · intro s x
    rw [hcount]
    exact Nat.zero_le x
  · intro k
    exact ⟨k + 1, Nat.lt_succ_self k⟩

end Lemmatheca.Entry.ComputablyBoundedChanges
