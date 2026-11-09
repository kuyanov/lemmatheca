import Lemmatheca.OneGenericSets.Selector
import Lemmatheca.EffectiveEnumerations.Increasing

/-! The exact zero-appending history and its actual halting-oracle characteristic program. -/
namespace Lemmatheca.ComputabilityTheory.OneGenericSets

open OracleComputation OracleProgramNumberings IncomparableTuringDegrees
  ComputableTreesAndPaths PostsTheorem UniversalComputation

set_option backward.isDefEq.respectTransparency false

noncomputable section

/-- The state stores both the stage counter and the current valid word. -/
def historyState (rho : ℕ) : ℕ → ℕ
  | 0 => Nat.pair 0 (normalize rho)
  | n + 1 => Nat.pair (n + 1) (appendBit (H n (historyState rho n).unpair.2) 0)

def historyWord (rho n : ℕ) : ℕ := (historyState rho n).unpair.2

def constructedSet (rho : ℕ) : Set ℕ := unionSet (historyWord rho)

theorem history_recurrence (rho n : ℕ) :
    historyWord rho 0 = normalize rho ∧
      historyWord rho (n + 1) = appendBit (H n (historyWord rho n)) 0 := by
  constructor <;> simp only [historyWord, historyState, Nat.unpair_pair]

theorem history_invariants (rho n : ℕ) :
    (historyState rho n).unpair.1 = n ∧ ValidCode (historyWord rho n) ∧
      Prefix (historyWord rho n) (historyWord rho (n + 1)) ∧
      wordLength rho + n ≤ wordLength (historyWord rho n) := by
  have hv : ∀ j, ValidCode (historyWord rho j) := by
    intro j
    cases j with
    | zero => rw [(history_recurrence rho 0).1]; exact (normalize_spec rho).1
    | succ j =>
      rw [(history_recurrence rho j).2]
      exact append_valid _ _ (H_spec j (historyWord rho j)).1
  have hp (j : ℕ) : Prefix (historyWord rho j) (historyWord rho (j + 1)) := by
    rw [(history_recurrence rho j).2]
    have hh := (H_spec j (historyWord rho j)).2.1
    rw [normalize_valid _ (hv j)] at hh
    exact prefix_trans hh (appendBit_spec _ _).2.1
  have hl (j : ℕ) : wordLength rho + j ≤ wordLength (historyWord rho j) := by
    induction j with
    | zero => rw [(history_recurrence rho 0).1, (normalize_spec rho).2.2]; omega
    | succ j ih =>
      have hh := (H_spec j (historyWord rho j)).2.1.1
      rw [(normalize_spec _).2.2] at hh
      rw [(history_recurrence rho j).2, (appendBit_spec _ _).1]
      omega
  refine ⟨?_, hv n, hp n, hl n⟩
  cases n <;> simp [historyState]

theorem constructed_prefixes (rho : ℕ) :
    (∀ n, Realizes (historyWord rho n) (constructedSet rho)) ∧
      ∀ G : Set ℕ, (∀ n, Realizes (historyWord rho n) G) → G = constructedSet rho := by
  exact coherent_union (historyWord rho) (fun n => (history_invariants rho n).2.2.1)
    (fun n => by have h := (history_invariants rho n).2.2.2; omega)

theorem constructed_bit (rho x : ℕ) :
    indicator (fun q => q ∈ constructedSet rho) x = wordBit (historyWord rho (x + 1)) x := by
  exact union_bit (historyWord rho) x

/-- Reusable meeting argument, independent of which bits are appended after each H step. -/
theorem generic_of_H_history (G : Set ℕ) (sigma : ℕ → ℕ)
    (hrealizes : ∀ n, Realizes (sigma n) G)
    (hstep : ∀ n, Prefix (H n (sigma n)) (sigma (n + 1))) : IsOneGeneric G := by
  apply (generic_iff_dense_completions G).mpr
  intro n
  have h := H_spec n (sigma n)
  exact ⟨H n (sigma n), h.1, realizes_prefix (hstep n) (hrealizes (n + 1)), h.2.2⟩

theorem constructed_generic (rho : ℕ) : IsOneGeneric (constructedSet rho) := by
  apply generic_of_H_history _ (historyWord rho) (constructed_prefixes rho).1
  intro n
  rw [(history_recurrence rho n).2]
  exact (appendBit_spec _ _).2.1

def historyFinish (z : ℕ) : ℕ := Nat.pair (z.unpair.1 + 1) (appendBit z.unpair.2 0)

def bitStageInput (z : ℕ) : ℕ := Nat.pair z.unpair.1 (z.unpair.2 + 1)

def historyBitOutput (z : ℕ) : ℕ := wordBit z.unpair.2.unpair.2 z.unpair.1.unpair.2

theorem history_finish_primitive : Primrec historyFinish := by
  exact Primrec₂.natPair.comp
    (Primrec.succ.comp (Primrec.fst.comp Primrec.unpair))
    (appendBit_primitive.comp (Primrec.snd.comp Primrec.unpair) (Primrec.const 0))

theorem bit_stage_input_primitive : Primrec bitStageInput := by
  exact Primrec₂.natPair.comp (Primrec.fst.comp Primrec.unpair)
    (Primrec.succ.comp (Primrec.snd.comp Primrec.unpair))

theorem history_bit_output_primitive : Primrec historyBitOutput := by
  have hl : Primrec (fun z : ℕ => z.unpair.1) := Primrec.fst.comp Primrec.unpair
  have hr : Primrec (fun z : ℕ => z.unpair.2) := Primrec.snd.comp Primrec.unpair
  exact beta_primitive.comp (hr.comp hr) (hr.comp hl)

def normalizeCode : Nat.Partrec.Code := ordinaryCode normalize (Primrec.nat_iff.mp normalize_primitive)
def historyFinishCode : Nat.Partrec.Code :=
  ordinaryCode historyFinish (Primrec.nat_iff.mp history_finish_primitive)
def bitStageInputCode : Nat.Partrec.Code :=
  ordinaryCode bitStageInput (Primrec.nat_iff.mp bit_stage_input_primitive)
def historyBitOutputCode : Nat.Partrec.Code :=
  ordinaryCode historyBitOutput (Primrec.nat_iff.mp history_bit_output_primitive)

def historyBaseCode : Code := .pair .zero (embed normalizeCode)

def historyStepCode : Code :=
  .comp (embed historyFinishCode)
    (.pair (.comp .left .right) (.comp selectorCode (.comp .right .right)))

def historyCode : Code := .prec historyBaseCode historyStepCode

def characteristicCode : Code :=
  .comp (embed historyBitOutputCode)
    (.pair identityCode (.comp historyCode (embed bitStageInputCode)))

theorem history_code_eval (rho n : ℕ) :
    eval haltingDiagonal historyCode (Nat.pair rho n) = Part.some (historyState rho n) := by
  induction n with
  | zero =>
    rw [historyCode, eval_prec_zero]
    simp [historyBaseCode, eval, eval_embed, normalizeCode, ordinaryCode_eval, historyState]
  | succ n ih =>
    have hs : historyState rho n = Nat.pair n (historyWord rho n) := by
      conv_lhs => rw [← Nat.pair_unpair (historyState rho n)]
      rw [(history_invariants rho n).1]
      rfl
    have hh : eval haltingDiagonal selectorCode (historyState rho n) =
        Part.some (H n (historyWord rho n)) := by
      rw [hs]
      exact selector_code_eval n _
    rw [historyCode, eval_prec_succ]
    change (eval haltingDiagonal historyCode (Nat.pair rho n)).bind _ = _
    rw [ih, Part.bind_some]
    simp [historyStepCode, eval, hh, eval_embed, historyFinishCode, ordinaryCode_eval,
      historyFinish, historyState, historyWord]

theorem characteristic_code_eval (rho x : ℕ) :
    eval haltingDiagonal characteristicCode (Nat.pair rho x) =
      Part.some (indicator (fun q => q ∈ constructedSet rho) x) := by
  simp [characteristicCode, eval, identity_eval, eval_embed, bitStageInputCode,
    historyBitOutputCode, ordinaryCode_eval, bitStageInput, history_code_eval,
    historyBitOutput, constructed_bit, historyWord]

theorem constructed_bound (rho : ℕ) :
    TuringDegrees.Reducible (constructedSet rho) haltingDiagonal := by
  refine ⟨.comp characteristicCode (.pair (constantCode rho) identityCode), fun x => ?_⟩
  simp [eval, constant_eval, identity_eval, characteristic_code_eval]

theorem constructed_extends (rho : ℕ) (hrho : ValidCode rho) :
    Realizes rho (constructedSet rho) := by
  have h := (constructed_prefixes rho).1 0
  rw [(history_recurrence rho 0).1, normalize_valid rho hrho] at h
  exact h

theorem generic_noncomputable (G : Set ℕ) (hG : IsOneGeneric G) :
    ¬ ComputablePred (fun q => q ∈ G) := by
  classical
  intro hc
  obtain ⟨f, hf, hfeq⟩ := (decidable_iff_characteristic (fun q => q ∈ G)).mp hc
  have hchi : Computable (indicator (fun q => q ∈ G)) := hf.of_eq hfeq
  have hR : ComputablePred (fun p : ℕ × ℕ => wordBit p.1 p.2 = indicator (fun q => q ∈ G) p.2) :=
    (Primrec.eq.decide.to_comp.comp
      beta_primitive.to_comp (hchi.comp Computable.snd)).computablePred
  have hb : ComputablePred (fun p : ℕ × ℕ =>
      ∀ i < p.2, wordBit p.1 i = indicator (fun q => q ∈ G) i) :=
    EffectiveEnumerations.computable_bounded_forall
      (R := fun u i => wordBit u i = indicator (fun q => q ∈ G) i) hR
  have hreal : ComputablePred (fun u => Realizes u G) :=
    (hb.decide.comp (Computable.id.pair FiniteSequenceCoding.primrec_length.to_comp)).computablePred
  let S : Set ℕ := {u | ValidCode u ∧ ¬ Realizes u G}
  have hS : REPred (fun u => u ∈ S) :=
    enumerable_inter valid_code_primitive.computablePred.to_re hreal.not.to_re
  rcases (generic_iff_enumerable_collections G).mp hG S hS (fun _ hu => hu.1) with
    ⟨u, _, hr, hbad⟩ | ⟨u, hu, hr, ha⟩
  · exact hbad.2 hr
  · let b := if wordLength u ∈ G then 0 else 1
    apply ha (appendBit u b) (append_valid _ _ hu) (appendBit_spec _ _).2.1
    refine ⟨append_valid _ _ hu, ?_⟩
    intro hv
    have hb := hv (wordLength u) (by rw [(appendBit_spec _ _).1]; omega)
    rw [(appendBit_spec _ _).2.2] at hb
    by_cases hg : wordLength u ∈ G <;> simp [b, indicator, hg] at hb

end
end Lemmatheca.ComputabilityTheory.OneGenericSets
