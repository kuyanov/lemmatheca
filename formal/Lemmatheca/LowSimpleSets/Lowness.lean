import Lemmatheca.TuringJump.Recoding
import Lemmatheca.LimitComputability.Approximation

/-! Lowness in the existing oracle numbering, with ordinary diagonal halting. -/
namespace Lemmatheca.ComputabilityTheory.LowSimpleSets

open TuringDegrees UniversalComputation TuringJump

noncomputable section
set_option backward.isDefEq.respectTransparency false

def Low (A : Set ℕ) : Prop := Equivalent (jump A) haltingDiagonal

def PositiveRequirement (A : Set ℕ) (e : ℕ) : Prop :=
  (EffectiveEnumerations.indexSet e).Infinite → (EffectiveEnumerations.indexSet e ∩ A).Nonempty

def JumpRequirement (A : Set ℕ) (g : LimitComputability.Approximation) (e : ℕ) : Prop :=
  ∃ t, ∀ s ≥ t, g s e = indicator (jump A) e

theorem low_iff_jump_below_halting (A : Set ℕ) :
    Low A ↔ Reducible (jump A) haltingDiagonal := by
  exact ⟨fun h => h.1, fun h => ⟨h, halting_below_jump A⟩⟩

theorem low_below_halting (A : Set ℕ) (hA : Low A) :
    Reducible A haltingDiagonal ∧ ¬ Reducible haltingDiagonal A := by
  exact ⟨reducible_trans (jump_strict A).1 hA.1,
    fun h => (jump_strict A).2 (reducible_trans hA.1 h)⟩

end
end Lemmatheca.ComputabilityTheory.LowSimpleSets
