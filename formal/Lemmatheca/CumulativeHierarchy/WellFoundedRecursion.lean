import Mathlib.Tactic
import Mathlib.SetTheory.ZFC.VonNeumann

/-! Set-valued well-founded recursion, used to construct the cumulative hierarchy. -/
set_option autoImplicit false
universe u v
namespace Lemmatheca.SetTheory.WellFoundedRecursion
open scoped ZFSet Ordinal

/-- The rule takes the indexed values at immediate predecessors. -/
abbrev RecursionRule {α : Type v} (R : α → α → Prop) :=
  (a : α) → ({b // R b a} → ZFSet.{u}) → ZFSet.{u}

/-- Well-founded recursion with set values. -/
noncomputable def recursiveValue {α : Type v} {R : α → α → Prop}
    (h : WellFounded R) (H : RecursionRule.{u} R) : α → ZFSet.{u} :=
  h.fix (fun a rec => H a (fun b => rec b.val b.property))

/-- Every well-founded set-valued recursion has a unique solution. -/
theorem recursion_exists_unique {α : Type v} {R : α → α → Prop}
    (h : WellFounded R) (H : RecursionRule.{u} R) :
    ∃! F : α → ZFSet.{u}, ∀ a, F a = H a (fun b => F b.val) := by
  refine ⟨recursiveValue h H, ?_, ?_⟩
  · intro a
    exact h.fix_eq _ a
  · intro F hF
    funext a
    induction a using h.induction with
    | h a ih =>
      rw [hF a, recursiveValue, h.fix_eq]
      congr 1
      funext b
      exact ih b.val b.property

end Lemmatheca.SetTheory.WellFoundedRecursion
