import Mathlib.Order.InitialSeg
import Mathlib.Order.UpperLower.Basic
import Mathlib.Order.SuccPred.Limit
import Mathlib.Order.WellFoundedSet
import Mathlib.Tactic

/-!
# Well-orders: histories and partial recursive solutions

Non-strict orders use `LinearOrder`; well-foundedness concerns their strict `<`.
Initial segments are `IsLowerSet` subsets (including empty and full subsets).
The history at a point is a function on the subtype `Set.Iio a`.
-/

namespace Lemmatheca.SetTheory

universe u v
variable {α : Type u} {S : Type v}

theorem wellFounded_iff_induction (r : α → α → Prop) :
    WellFounded r ↔ ∀ P : α → Prop,
      (∀ a, (∀ b, r b a → P b) → P a) → ∀ a, P a := by
  sorry

section Ordered
variable [LinearOrder α]

/-- A rule for every point and every possible earlier history, with fixed value type. -/
def RecursionRule (α : Type u) [Preorder α] (S : Type v) :=
  (a : α) → (Set.Iio a → S) → S

/-- A function on a downward-closed domain obeying the given recursion rule. -/
structure PartialRecursiveSolution (Φ : RecursionRule α S) where
  domain : Set α
  lower : IsLowerSet domain
  value : domain → S
  equation : ∀ a : domain, value a =
    Φ a.val (fun b => value ⟨b.val, lower b.property.le a.property⟩)

theorem partial_recursive_solutions_agree [WellFoundedLT α] (Φ : RecursionRule α S)
    (h k : PartialRecursiveSolution Φ) :
    ∀ a (ha : a ∈ h.domain) (hk : a ∈ k.domain), h.value ⟨a, ha⟩ = k.value ⟨a, hk⟩ := by
  sorry

noncomputable def recursiveValue [WellFoundedLT α] (Φ : RecursionRule α S) : α → S :=
  wellFounded_lt.fix (fun a earlier => Φ a (fun b => earlier b.val b.property))

theorem recursion_exists_unique [WellFoundedLT α] (Φ : RecursionRule α S) :
    ∃! F : α → S, ∀ a, F a = Φ a (fun b => F b.val) := by
  sorry

theorem three_case_induction [WellFoundedLT α] (P : α → Prop)
    (base : ∀ a, IsMin a → P a)
    (step : ∀ a b, a ⋖ b → P a → P b)
    (limit : ∀ b, Order.IsSuccLimit b → (∀ a, a < b → P a) → P b) :
    ∀ a, P a := by
  sorry

theorem finite_predecessor [Finite α] {b : α} (hb : ¬ IsMin b) :
    ∃ a, a ⋖ b := by
  sorry

theorem recursion_empty_values_impossible [WellFoundedLT α] [Nonempty α] :
    IsEmpty (RecursionRule α Empty) := by
  sorry

end Ordered

end Lemmatheca.SetTheory
