import Lemmatheca.RelativizedLimitComputability.Theorems

namespace Lemmatheca.ComputabilityTheory.RelativizedLimitComputability

open OracleComputation OracleProgramNumberings UniversalComputation
open BusyBeaverFunctions (ordinaryProgram)

noncomputable section

set_option backward.isDefEq.respectTransparency false

def successBit (B : Set ℕ) (e : ℕ) (s x : ℕ) : ℕ :=
  if 0 < virtualValue B s e x then 1 else 0

theorem constant_two_eventually_three (B : Set ℕ) (x : ℕ) :
    ∃ S, ∀ s, S ≤ s → virtualValue B s (constantIndex 2) x = 3 := by
  have he : OracleProgramNumberings.phi (TuringJump.jump B) (constantIndex 2) x =
      Part.some 2 := by
    simp only [OracleProgramNumberings.phi, constantIndex, decode_encode, constant_eval]
  obtain ⟨k,hk⟩ := (phi_output_certificate (TuringJump.jump B) (constantIndex 2) x 2).mp
    (Part.eq_some_iff.mp he)
  obtain ⟨S,hS⟩ := fixed_prefix_replay B k (constantIndex 2) x 2 hk
  exact ⟨S, fun s hs => (hS s hs).2⟩

theorem success_bit_loses_two (B : Set ℕ) :
    ConvergesTo (successBit B (constantIndex 2)) (fun _ => 1) ∧
      ¬ ConvergesTo (successBit B (constantIndex 2)) (fun _ => 2) ∧
        ConvergesTo (numericalApproximation B (constantIndex 2)) (fun _ => 2) := by
  have hone : ConvergesTo (successBit B (constantIndex 2)) (fun _ => 1) := by
    intro x
    obtain ⟨S,hS⟩ := constant_two_eventually_three B x
    exact ⟨S, fun s hs => by simp [successBit,hS s hs]⟩
  refine ⟨hone, ?_, ?_⟩
  · intro htwo
    obtain ⟨S,hS⟩ := hone 0
    obtain ⟨T,hT⟩ := htwo 0
    have h1 := hS (max S T) (by omega)
    have h2 := hT (max S T) (by omega)
    dsimp only at h1 h2
    omega
  · apply numerical_convergence B (constantIndex 2) (fun _ => 2)
    intro x
    simp only [OracleProgramNumberings.phi, constantIndex, decode_encode, constant_eval]

def queryApproximationCode : Code := .comp .query .right

def queryApproximationIndex : ℕ := encodeCode queryApproximationCode

theorem query_approximation_eval (B : Set ℕ) (s x : ℕ) :
    OracleProgramNumberings.phi B queryApproximationIndex (Nat.pair s x) =
      Part.some (indicator B x) := by
  simp only [OracleProgramNumberings.phi, queryApproximationIndex, decode_encode,
    queryApproximationCode, eval, Nat.unpair_pair, Part.bind_some]
  rfl

theorem query_approximation_converges (B : Set ℕ) :
    ConvergesTo (fun _ x => indicator B x) (indicator B) := by
  exact fun _ => ⟨0, fun _ _ => rfl⟩

theorem transformed_query_eval (B : Set ℕ) (x : ℕ) :
    OracleProgramNumberings.phi (TuringJump.jump B) (stableIndex queryApproximationIndex) x =
      Part.some (indicator B x) := by
  exact stable_index_eval B queryApproximationIndex (fun _ x => indicator B x)
    (query_approximation_eval B) (indicator B) (query_approximation_converges B) x

theorem empty_full_query_values (s x : ℕ) :
    OracleProgramNumberings.phi ∅ queryApproximationIndex (Nat.pair s x) = Part.some 0 ∧
      OracleProgramNumberings.phi Set.univ queryApproximationIndex (Nat.pair s x) = Part.some 1 := by
  rw [query_approximation_eval,query_approximation_eval]
  simp only [indicator]
  constructor
  · rw [ite_eq_right (show ¬ (∅ : Set ℕ) x from id)]
  · rw [ite_eq_left (show (Set.univ : Set ℕ) x from trivial)]

def pulse (B : Set ℕ) (s x : ℕ) : ℕ := by
  classical
  exact if x ∈ jumpStage B (s + 1) ∧ x ∉ jumpStage B s then 3 else 2

def nextStageInput (w : ℕ) : ℕ := Nat.pair (w.unpair.1 + 1) w.unpair.2

theorem next_stage_input_primitive : Primrec nextStageInput := by
  exact Primrec₂.natPair.comp
    (Primrec.succ.comp (Primrec.fst.comp Primrec.unpair))
    (Primrec.snd.comp Primrec.unpair)

-- The first coordinate is the old snapshot bit; the second is the next snapshot bit.
def pulseDecode (w : ℕ) : ℕ :=
  if w.unpair.1 = 0 ∧ w.unpair.2 = 1 then 3 else 2

theorem pulse_decode_primitive : Primrec pulseDecode := by
  have l := Primrec.fst.comp Primrec.unpair
  have r := Primrec.snd.comp Primrec.unpair
  exact Primrec.ite ((Primrec.eq.comp l (Primrec.const 0)).and
    (Primrec.eq.comp r (Primrec.const 1))) (Primrec.const 3) (Primrec.const 2)

def pulseCode : Code :=
  .comp (embed (ordinaryProgram pulseDecode pulse_decode_primitive.to_comp))
    (.pair snapshotCode
      (.comp snapshotCode (embed (ordinaryProgram nextStageInput next_stage_input_primitive.to_comp))))

theorem pulse_code_eval (B : Set ℕ) (s x : ℕ) :
    eval B pulseCode (Nat.pair s x) = Part.some (pulse B s x) := by
  classical
  rw [pulseCode,eval]
  have hp : eval B (.pair snapshotCode
      (.comp snapshotCode (embed (ordinaryProgram nextStageInput next_stage_input_primitive.to_comp))))
      (Nat.pair s x) = Part.some (Nat.pair (stageBit B s x) (stageBit B (s+1) x)) := by
    simp only [snapshot_code_eval,eval,eval_embed,BusyBeaverFunctions.ordinaryProgram_eval,
      nextStageInput,Nat.unpair_pair,Part.bind_some,Part.map_some]
  rw [hp,Part.bind_some,eval_embed,BusyBeaverFunctions.ordinaryProgram_eval]
  congr 1
  simp only [pulseDecode,Nat.unpair_pair,stageBit,indicator,pulse]
  change (if (if x ∈ jumpStage B s then 1 else 0) = 0 ∧
      (if x ∈ jumpStage B (s+1) then 1 else 0) = 1 then 3 else 2) =
    (if x ∈ jumpStage B (s+1) ∧ x ∉ jumpStage B s then 3 else 2)
  by_cases h0 : x ∈ jumpStage B s <;> by_cases h1 : x ∈ jumpStage B (s+1) <;>
    simp [h0,h1]

theorem pulse_joint_computable (B : Set ℕ) : JointComputableIn B (pulse B) := by
  apply (joint_index_iff B (pulse B)).mpr
  refine ⟨encodeCode pulseCode,fun s x => ?_⟩
  simpa only [OracleProgramNumberings.phi,decode_encode] using pulse_code_eval B s x

theorem pulse_converges (B : Set ℕ) : ConvergesTo (pulse B) (fun _ => 2) := by
  classical
  intro x
  have hd := jump_stage_data B
  by_cases hx : x ∈ TuringJump.jump B
  · obtain ⟨S,hS⟩ := (hd.2.2.2 x).mp hx
    refine ⟨S,fun s hs => ?_⟩
    have hmem : x ∈ jumpStage B s := hd.2.1 hs hS
    simp only [pulse, hmem, not_true_eq_false, and_false, ite_false]
  · refine ⟨0,fun s _ => ?_⟩
    have hn : x ∉ jumpStage B (s+1) := fun h => hx ((hd.2.2.2 x).mpr ⟨s+1,h⟩)
    simp only [pulse,hn,false_and,ite_false]

def modulusDecisionCode (c : Code) : Code :=
  .comp snapshotCode (.pair c identityCode)

theorem pulse_modulus_decision (B : Set ℕ) (m : ℕ → ℕ) (c : Code)
    (hc : ∀ x, eval B c x = Part.some (m x)) (hm : ModulusTo (pulse B) (fun _ => 2) m)
    (x : ℕ) :
    eval B (modulusDecisionCode c) x = Part.some (indicator (TuringJump.jump B) x) := by
  classical
  have hd := jump_stage_data B
  have hiff : x ∈ jumpStage B (m x) ↔ x ∈ TuringJump.jump B := by
    constructor
    · intro h
      exact (hd.2.2.2 x).mpr ⟨m x,h⟩
    · intro hx
      by_contra hn
      have hnot : ∀ n, x ∉ jumpStage B (m x+n) := by
        intro n
        induction n with
        | zero => simpa using hn
        | succ n ih =>
            intro hnext
            have hp : pulse B (m x+n) x = 3 := by
              simp only [pulse,show m x+n+1=m x+(n+1) by omega,hnext,ih,
                not_false_eq_true,and_self,ite_true]
            have hv := hm x (m x+n) (by omega)
            change pulse B (m x+n) x = 2 at hv
            rw [hp] at hv
            contradiction
      obtain ⟨S,hS⟩ := (hd.2.2.2 x).mp hx
      let T := max S (m x)
      have hT : x ∈ jumpStage B T := hd.2.1 (by dsimp [T]; omega) hS
      have hnT := hnot (T-m x)
      have he : m x+(T-m x)=T := by dsimp [T]; omega
      rw [he] at hnT
      exact hnT hT
  rw [modulusDecisionCode,eval]
  have hp : eval B (.pair c identityCode) x = Part.some (Nat.pair (m x) x) := by
    simp only [eval,hc,identity_eval,Part.bind_some,Part.map_some]
  rw [hp,Part.bind_some,snapshot_code_eval]
  congr 1
  change (if x ∈ jumpStage B (m x) then 1 else 0) =
    (if x ∈ TuringJump.jump B then 1 else 0)
  rw [hiff]

theorem pulse_no_relative_modulus (B : Set ℕ) :
    ¬ ∃ m, PartialComputable B (fun x => Part.some (m x)) ∧
      ModulusTo (pulse B) (fun _ => 2) m := by
  rintro ⟨m,⟨c,hc⟩,hm⟩
  apply (TuringJump.jump_strict B).2
  refine ⟨modulusDecisionCode c,fun x => ?_⟩
  have hv := pulse_modulus_decision B m c (fun x => congrFun hc x) hm x
  exact hv

end
end Lemmatheca.ComputabilityTheory.RelativizedLimitComputability
