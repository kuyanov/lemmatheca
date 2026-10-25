import Lemmatheca.TuringMachines.Unary
import Mathlib.Data.Fintype.EquivFin

/-! Labelings are chosen once for an arbitrary native finite tape machine. -/
namespace Lemmatheca.ComputabilityTheory.TapeCoding

open TuringMachines (Alphabet Config Move)

variable {Γ Q : Type*} {A : Alphabet Γ} [Fintype Γ] [Fintype Q]

structure Labeling (T : TuringMachines.Machine A Q) where
  symbol : Γ ≃ Fin (Fintype.card Γ)
  state : Q ≃ Fin (Fintype.card Q)
  blank_zero : (symbol A.blank).val = 0
  mark_one : (symbol A.mark).val = 1
  initial_zero : (state T.initial).val = 0

theorem labeling_exists (T : TuringMachines.Machine A Q) : Nonempty (Labeling T) := by
  classical
  have hg : 1 < Fintype.card Γ :=
    Fintype.one_lt_card_iff.mpr ⟨A.mark, A.blank, A.mark_ne_blank⟩
  have hq : 0 < Fintype.card Q := Fintype.card_pos_iff.mpr ⟨T.initial⟩
  let zeroSymbol : Fin (Fintype.card Γ) := ⟨0, by omega⟩
  let oneSymbol : Fin (Fintype.card Γ) := ⟨1, hg⟩
  let first := (Fintype.equivFin Γ).trans
    (Equiv.swap ((Fintype.equivFin Γ) A.blank) zeroSymbol)
  have hblank : first A.blank = zeroSymbol := by simp [first]
  have hmark : first A.mark ≠ zeroSymbol := by
    intro h
    exact A.mark_ne_blank (first.injective (h.trans hblank.symm))
  have hzeroone : zeroSymbol ≠ oneSymbol := by
    intro h
    have := congrArg Fin.val h
    simp [zeroSymbol, oneSymbol] at this
  let symbols := first.trans (Equiv.swap (first A.mark) oneSymbol)
  let zeroState : Fin (Fintype.card Q) := ⟨0, hq⟩
  let states := (Fintype.equivFin Q).trans
    (Equiv.swap ((Fintype.equivFin Q) T.initial) zeroState)
  refine ⟨⟨symbols, states, ?_, ?_, ?_⟩⟩
  · change (Equiv.swap (first A.mark) oneSymbol (first A.blank)).val = 0
    rw [hblank, Equiv.swap_apply_of_ne_of_ne hmark.symm hzeroone]
  · simp [symbols, oneSymbol]
  · simp [states, zeroState]

noncomputable def chooseLabeling (T : TuringMachines.Machine A Q) : Labeling T :=
  Classical.choice (labeling_exists T)

theorem cardinal_bounds (T : TuringMachines.Machine A Q) :
    2 ≤ Fintype.card Γ ∧ 1 ≤ Fintype.card Q := by
  have hg := Fintype.one_lt_card_iff.mpr ⟨A.mark, A.blank, A.mark_ne_blank⟩
  have hq : 0 < Fintype.card Q := Fintype.card_pos_iff.mpr ⟨T.initial⟩
  exact ⟨hg, hq⟩

def moveCode : Move → ℕ
  | .left => 0
  | .stay => 1
  | .right => 2

end Lemmatheca.ComputabilityTheory.TapeCoding
