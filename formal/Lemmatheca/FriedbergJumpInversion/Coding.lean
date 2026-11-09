import Lemmatheca.FriedbergJumpInversion.Basic
import Lemmatheca.OracleComputation.Substitution

/-! Actual finite programs compute the very same coding history from a supplied K reduction. -/
namespace Lemmatheca.ComputabilityTheory.FriedbergJumpInversion

open OracleComputation OracleProgramNumberings IncomparableTuringDegrees
  ComputableTreesAndPaths PostsTheorem UniversalComputation OneGenericSets TuringDegrees

noncomputable section
set_option autoImplicit false

def transportedSelector (d : Code) : Code := subst d OneGenericSets.selectorCode

theorem transported_selector_eval (B : Set ℕ) (d : Code)
    (hd : Reduces d haltingDiagonal B) (e u : ℕ) :
    eval B (transportedSelector d) (Nat.pair e u) = Part.some (H e u) := by
  rw [transportedSelector, subst_eval haltingDiagonal B d hd]
  exact selector_code_eval e u

def codingFinish (z : ℕ) : ℕ :=
  Nat.pair (z.unpair.1 + 1) (appendBit z.unpair.2.unpair.1 z.unpair.2.unpair.2)

theorem coding_finish_primitive : Primrec codingFinish := by
  have hl : Primrec (fun z : ℕ => z.unpair.1) := Primrec.fst.comp Primrec.unpair
  have hr : Primrec (fun z : ℕ => z.unpair.2) := Primrec.snd.comp Primrec.unpair
  exact Primrec₂.natPair.comp (Primrec.succ.comp hl)
    (appendBit_primitive.comp (hl.comp hr) (hr.comp hr))

def codingFinishCode : Nat.Partrec.Code :=
  ordinaryCode codingFinish (Primrec.nat_iff.mp coding_finish_primitive)

def stateProjection : Code := .comp .right .right

def counterProjection : Code := .comp .left .right

def codingStep (d : Code) : Code :=
  .comp (embed codingFinishCode)
    (.pair counterProjection
      (.pair (.comp (transportedSelector d) stateProjection)
        (.comp .query counterProjection)))

def codingProgram (d : Code) : Code := .prec historyBaseCode (codingStep d)

def characteristicProgram (d : Code) : Code :=
  .comp (embed historyBitOutputCode)
    (.pair identityCode (.comp (codingProgram d) (embed bitStageInputCode)))

theorem coding_program_eval (B : Set ℕ) (d : Code) (hd : Reduces d haltingDiagonal B)
    (rho n : ℕ) :
    eval B (codingProgram d) (Nat.pair rho n) = Part.some (codingState B rho n) := by
  induction n with
  | zero =>
    rw [codingProgram, eval_prec_zero]
    simp [historyBaseCode, eval, eval_embed, normalizeCode, ordinaryCode_eval, codingState]
  | succ n ih =>
    have hs : codingState B rho n = Nat.pair n (codingWord B rho n) := by
      conv_lhs => rw [← Nat.pair_unpair (codingState B rho n)]
      rw [(coding_invariant B rho n).1]
      rfl
    have hh : eval B (transportedSelector d) (codingState B rho n) =
        Part.some (H n (codingWord B rho n)) := by
      rw [hs]
      exact transported_selector_eval B d hd n _
    rw [codingProgram, eval_prec_succ]
    change (eval B (codingProgram d) (Nat.pair rho n)).bind _ = _
    rw [ih, Part.bind_some]
    simp [codingStep, stateProjection, counterProjection, eval, hh, eval_embed,
      codingFinishCode, ordinaryCode_eval, codingFinish, codingState, codingWord]

theorem characteristic_program_eval (B : Set ℕ) (d : Code)
    (hd : Reduces d haltingDiagonal B) (rho x : ℕ) :
    eval B (characteristicProgram d) (Nat.pair rho x) =
      Part.some (indicator (fun q => q ∈ codedSet B rho) x) := by
  simp [characteristicProgram, eval, identity_eval, eval_embed, bitStageInputCode,
    historyBitOutputCode, ordinaryCode_eval, bitStageInput, coding_program_eval B d hd,
    historyBitOutput, coded_characteristic, codingWord]

def fixedCharacteristicProgram (d : Code) (rho : ℕ) : Code :=
  .comp (characteristicProgram d) (.pair (constantCode rho) identityCode)

theorem fixed_characteristic_reduces (B : Set ℕ) (d : Code)
    (hd : Reduces d haltingDiagonal B) (rho : ℕ) :
    Reduces (fixedCharacteristicProgram d rho) (codedSet B rho) B := by
  intro x
  simp [fixedCharacteristicProgram, eval, constant_eval, identity_eval,
    characteristic_program_eval B d hd]

end
end Lemmatheca.ComputabilityTheory.FriedbergJumpInversion
