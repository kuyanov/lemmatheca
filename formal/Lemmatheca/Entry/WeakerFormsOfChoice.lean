import Lemmatheca.SetTheory.WeakerChoice
import Lemmatheca.SetTheory.Choice

/-! Particular examples and counterexamples for the human entry. -/

set_option autoImplicit false
universe u
namespace Lemmatheca.Entry.WeakerFormsOfChoice
open Lemmatheca.SetTheory.WeakerChoice
open Order
open scoped Ordinal Cardinal

/-- The empty carrier is serial but has no infinite sequence. -/
theorem empty_serial : Serial (fun _ _ : ULift.{u} Empty => False) ∧
    ¬ Nonempty (ℕ → ULift.{u} Empty) := by
  constructor
  · intro x
    exact x.down.elim
  · rintro ⟨f⟩
    exact (f 0).down.elim

end Lemmatheca.Entry.WeakerFormsOfChoice
