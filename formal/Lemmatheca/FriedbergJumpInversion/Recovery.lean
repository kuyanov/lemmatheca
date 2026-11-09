import Lemmatheca.FriedbergJumpInversion.Coding
import Lemmatheca.OneGenericSets.Jump

/-! One fixed decoder reconstructs the exact selected words and coding positions. -/
namespace Lemmatheca.ComputabilityTheory.FriedbergJumpInversion

open OracleComputation OracleProgramNumberings IncomparableTuringDegrees
  ComputableTreesAndPaths PostsTheorem UniversalComputation OneGenericSets TuringDegrees

noncomputable section
set_option autoImplicit false

def recoveryState (X : Set ℕ) (rho : ℕ) : ℕ → ℕ
  | 0 => Nat.pair 0 (OneGenericSets.normalize rho)
  | n + 1 =>
      let v := H n (recoveryState X rho n).unpair.2
      Nat.pair (n + 1) (appendBit v (indicator (fun q => q ∈ X) (wordLength v)))

def recoveryWord (X : Set ℕ) (rho n : ℕ) : ℕ := (recoveryState X rho n).unpair.2

def recoveryExtension (X : Set ℕ) (rho n : ℕ) : ℕ := H n (recoveryWord X rho n)

def recoveryBit (X : Set ℕ) (rho n : ℕ) : ℕ :=
  indicator (fun q => q ∈ X) (wordLength (recoveryExtension X rho n))

theorem recovery_invariant (X : Set ℕ) (rho n : ℕ) :
    (recoveryState X rho n).unpair.1 = n ∧ ValidCode (recoveryWord X rho n) ∧
      ValidCode (recoveryExtension X rho n) ∧
      recoveryWord X rho (n + 1) = appendBit (recoveryExtension X rho n) (recoveryBit X rho n) := by
  have hv : ∀ j, ValidCode (recoveryWord X rho j) := by
    intro j
    cases j with
    | zero => simpa only [recoveryWord, recoveryState, Nat.unpair_pair] using (normalize_spec rho).1
    | succ j =>
      simpa only [recoveryWord, recoveryState, Nat.unpair_pair] using
        append_valid _ (indicator (fun q => q ∈ X)
          (wordLength (H j (recoveryWord X rho j)))) (H_spec j (recoveryWord X rho j)).1
  refine ⟨?_, hv n, (H_spec n (recoveryWord X rho n)).1, ?_⟩
  · cases n <;> simp [recoveryState]
  · simp [recoveryWord, recoveryState, recoveryExtension, recoveryBit]

theorem recovery_exact (B : Set ℕ) (rho n : ℕ) :
    recoveryState (codedSet B rho) rho n = codingState B rho n ∧
      recoveryExtension (codedSet B rho) rho n = codingExtension B rho n ∧
      recoveryBit (codedSet B rho) rho n = indicator (fun q => q ∈ B) n := by
  have hs : ∀ j, recoveryState (codedSet B rho) rho j = codingState B rho j := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih =>
      change Nat.pair (j + 1)
        (appendBit (H j (recoveryState (codedSet B rho) rho j).unpair.2)
          (indicator (fun q => q ∈ codedSet B rho)
            (wordLength (H j (recoveryState (codedSet B rho) rho j).unpair.2)))) = _
      rw [ih]
      change Nat.pair (j + 1) (appendBit (codingExtension B rho j)
        (indicator (fun q => q ∈ codedSet B rho) (wordLength (codingExtension B rho j)))) = _
      rw [coding_bit]
      rfl
  have he : recoveryExtension (codedSet B rho) rho n = codingExtension B rho n := by
    simp [recoveryExtension, recoveryWord, codingExtension, codingWord, hs]
  exact ⟨hs n, he, by simpa only [recoveryBit, he] using coding_bit B rho n⟩

def oddInput (x : ℕ) : ℕ := 2 * x + 1

private theorem odd_input_primitive : Primrec oddInput := by
  exact Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id)
    (Primrec.const 1)

private def oddInputCode : Nat.Partrec.Code := ordinaryCode oddInput (Primrec.nat_iff.mp odd_input_primitive)

def oddQueryCode : Code := .comp .query (embed oddInputCode)

theorem join_queries_eval (X : Set ℕ) (x : ℕ) :
    eval (join X haltingDiagonal) evenQueryCode x = Part.some (indicator (fun q => q ∈ X) x) ∧
      eval (join X haltingDiagonal) oddQueryCode x = Part.some (indicator (fun q => q ∈ haltingDiagonal) x) := by
  constructor
  · simp [evenQueryCode, eval, eval_embed, doubleInputCode, ordinaryCode_eval,
      doubleInput, join_indicator]
  · have hm : (2 * x + 1) % 2 = 1 := by omega
    have hd : (2 * x + 1) / 2 = x := by omega
    simp [oddQueryCode, eval, eval_embed, oddInputCode, ordinaryCode_eval,
      oddInput, join_indicator, hm, hd]

private theorem word_length_primitive : Primrec wordLength := by
  exact FiniteSequenceCoding.primrec_length

private def lengthCode : Nat.Partrec.Code := ordinaryCode wordLength (Primrec.nat_iff.mp word_length_primitive)

def recoverySelector : Code := subst oddQueryCode OneGenericSets.selectorCode

def recoveryRead : Code := .comp evenQueryCode (.comp (embed lengthCode) recoverySelector)

private theorem recovery_selector_eval (X : Set ℕ) (e u : ℕ) :
    eval (join X haltingDiagonal) recoverySelector (Nat.pair e u) = Part.some (H e u) := by
  rw [recoverySelector, subst_eval haltingDiagonal (join X haltingDiagonal) oddQueryCode
    (fun q => (join_queries_eval X q).2)]
  exact selector_code_eval e u

private theorem recovery_read_eval (X : Set ℕ) (e u : ℕ) :
    eval (join X haltingDiagonal) recoveryRead (Nat.pair e u) =
      Part.some (indicator (fun q => q ∈ X) (wordLength (H e u))) := by
  rw [recoveryRead]
  simp only [eval, recovery_selector_eval X e u, Part.bind_some, eval_embed,
    lengthCode, ordinaryCode_eval]
  exact (join_queries_eval X (wordLength (H e u))).1

def recoveryStep : Code :=
  .comp (embed codingFinishCode)
    (.pair counterProjection
      (.pair (.comp recoverySelector stateProjection) (.comp recoveryRead stateProjection)))

def recoveryProgram : Code := .prec historyBaseCode recoveryStep

def decoderProgram : Code := .comp recoveryRead recoveryProgram

theorem recovery_program_eval (X : Set ℕ) (rho n : ℕ) :
    eval (join X haltingDiagonal) recoveryProgram (Nat.pair rho n) =
      Part.some (recoveryState X rho n) := by
  induction n with
  | zero =>
    rw [recoveryProgram, eval_prec_zero]
    simp [historyBaseCode, eval, eval_embed, normalizeCode, ordinaryCode_eval, recoveryState]
  | succ n ih =>
    have hs : recoveryState X rho n = Nat.pair n (recoveryWord X rho n) := by
      conv_lhs => rw [← Nat.pair_unpair (recoveryState X rho n)]
      rw [(recovery_invariant X rho n).1]
      rfl
    have hh : eval (join X haltingDiagonal) recoverySelector (recoveryState X rho n) =
        Part.some (H n (recoveryWord X rho n)) := by
      rw [hs]
      exact recovery_selector_eval X n _
    have hb : eval (join X haltingDiagonal) recoveryRead (recoveryState X rho n) =
        Part.some (recoveryBit X rho n) := by
      rw [hs]
      exact recovery_read_eval X n _
    rw [recoveryProgram, eval_prec_succ]
    change (eval (join X haltingDiagonal) recoveryProgram (Nat.pair rho n)).bind _ = _
    rw [ih, Part.bind_some]
    simp [recoveryStep, stateProjection, counterProjection, eval, hh, hb, eval_embed,
      codingFinishCode, ordinaryCode_eval, codingFinish, recoveryState, recoveryWord,
      recoveryBit, recoveryExtension]

theorem decoder_program_eval (X : Set ℕ) (rho n : ℕ) :
    eval (join X haltingDiagonal) decoderProgram (Nat.pair rho n) =
      Part.some (recoveryBit X rho n) := by
  rw [decoderProgram]
  simp only [eval, recovery_program_eval, Part.bind_some]
  have hs : recoveryState X rho n = Nat.pair n (recoveryWord X rho n) := by
    conv_lhs => rw [← Nat.pair_unpair (recoveryState X rho n)]
    rw [(recovery_invariant X rho n).1]
    rfl
  rw [hs]
  exact recovery_read_eval X n _

def fixedDecoderProgram (rho : ℕ) : Code :=
  .comp decoderProgram (.pair (constantCode rho) identityCode)

theorem decoder_reduces (B : Set ℕ) (rho : ℕ) :
    Reduces (fixedDecoderProgram rho) B (join (codedSet B rho) haltingDiagonal) := by
  intro x
  simp [fixedDecoderProgram, eval, constant_eval, identity_eval, decoder_program_eval,
    (recovery_exact B rho x).2.2]

end
end Lemmatheca.ComputabilityTheory.FriedbergJumpInversion
