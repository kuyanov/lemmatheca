import Mathlib.Data.Set.Basic

/-! The family-choice principle stated with the ZFC axioms. -/
namespace Lemmatheca.SetTheory
universe u

def ChoicePrinciple : Prop :=
  ∀ (ι α : Type u) (A : ι → Set α),
    (∀ i, (A i).Nonempty) → ∃ c : ι → α, ∀ i, c i ∈ A i

end Lemmatheca.SetTheory
