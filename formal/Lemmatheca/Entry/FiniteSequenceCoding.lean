import Lemmatheca.MathematicalLogic.FiniteSequenceCoding

namespace Lemmatheca.Entry.FiniteSequenceCoding
open Lemmatheca.MathematicalLogic.FiniteSequenceCoding

theorem coding_examples :
    code [0] = 1 ∧ code [2] = 7 ∧ code [2, 0] = 8 ∧ code [2, 0, 0] = 9 ∧
    decode 8 = [2, 0] ∧ length 8 = 2 ∧ entry 8 1 = 0 ∧ entry 8 2 = 0 := by
  have hc : code [2, 0] = 8 := by decide
  have hd : decode 8 = [2, 0] := hc ▸ decode_code [2, 0]
  exact ⟨by decide, by decide, hc, by decide, hd,
    by simp [length, hd], by simp [entry, hd], by simp [entry, hd]⟩

def unmarkedCode : List ℕ → ℕ
  | [] => 0
  | a :: s => Nat.pair a (unmarkedCode s)

theorem unmarked_collision : unmarkedCode [] = unmarkedCode [0] := by decide

theorem pairing_examples :
    Nat.pair 0 1 = 1 ∧ Nat.pair 1 0 = 2 ∧ Nat.pair 1 1 = 3 ∧
    Nat.pair 0 2 = 4 ∧ Nat.pair 2 1 = 7 := by decide

theorem tail_examples : tails 8 0 = 8 ∧ tails 8 1 = 1 ∧ tails 8 2 = 0 := by
  change tails (code [2, 0]) 0 = 8 ∧ tails (code [2, 0]) 1 = 1 ∧ tails (code [2, 0]) 2 = 0
  rw [tails_code, tails_code, tails_code]
  decide

end Lemmatheca.Entry.FiniteSequenceCoding
