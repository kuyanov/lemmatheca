import Lemmatheca.RelativizedLimitComputability.Forward

namespace Lemmatheca.ComputabilityTheory.RelativizedLimitComputability

open OracleComputation OracleProgramNumberings UniversalComputation
open BusyBeaverFunctions (ordinaryProgram)

noncomputable section

set_option backward.isDefEq.respectTransparency false

private theorem bounded_value_mono (B : Set ℕ) (k l e x y : ℕ) (hkl : k ≤ l)
    (h : boundedValue B k e x = y + 1) : boundedValue B l e x = y + 1 := by
  apply (boundedValue_output B l e x y).mpr
  have hm := bounded_monotone (indicator B) k (l - k) (decodeCode e) x y
    ((boundedValue_output B k e x y).mp h)
  simpa only [bounded, Membership.mem, Set.Mem, Nat.add_sub_of_le hkl] using hm


def jumpStage (B : Set ℕ) (s : ℕ) : Set ℕ :=
  {i | i < s ∧ 0 < OracleProgramNumberings.boundedValue B s i i}

def stageBit (B : Set ℕ) (s i : ℕ) : ℕ := indicator (jumpStage B s) i

theorem jump_stage_data (B : Set ℕ) :
    jumpStage B 0 = ∅ ∧ Monotone (jumpStage B) ∧
      (∀ s, (jumpStage B s).Finite) ∧
      (∀ i, i ∈ TuringJump.jump B ↔ ∃ s, i ∈ jumpStage B s) := by
  have hm : Monotone (jumpStage B) := by
    intro s t hst i hi
    obtain ⟨his, hv⟩ := hi
    refine ⟨lt_of_lt_of_le his hst, ?_⟩
    have he : boundedValue B s i i = (boundedValue B s i i - 1) + 1 := by omega
    have ht := bounded_value_mono B s t i i _ hst he
    omega
  refine ⟨?_, hm, ?_, ?_⟩
  · ext i
    simp [jumpStage]
  · intro s
    exact (Set.finite_Iio s).subset (fun _ h => h.1)
  · intro i
    change (OracleProgramNumberings.phi B i i).Dom ↔ _
    rw [phi_domain_certificate]
    constructor
    · rintro ⟨k, hk⟩
      let s := max k (i + 1)
      refine ⟨s, by dsimp [s]; omega, ?_⟩
      have he : boundedValue B k i i = (boundedValue B k i i - 1) + 1 := by omega
      have ht := bounded_value_mono B k s i i _ (by dsimp [s]; omega) he
      omega
    · rintro ⟨s, hs⟩
      exact ⟨s, hs.2⟩

-- Input (s,i) is transformed to the bounded evaluator input (s,(i,i)).
def snapshotInput (w : ℕ) : ℕ :=
  Nat.pair w.unpair.1 (Nat.pair w.unpair.2 w.unpair.2)

theorem snapshot_input_primitive : Primrec snapshotInput := by
  have l := Primrec.fst.comp Primrec.unpair
  have r := Primrec.snd.comp Primrec.unpair
  exact Primrec₂.natPair.comp l (Primrec₂.natPair.comp r r)

-- This input is ((s,i),v), with v the bounded-output code.
def snapshotDecode (w : ℕ) : ℕ :=
  if w.unpair.1.unpair.2 < w.unpair.1.unpair.1 ∧ 0 < w.unpair.2 then 1 else 0

theorem snapshot_decode_primitive : Primrec snapshotDecode := by
  have l : Primrec (fun n : ℕ => n.unpair.1) := Primrec.fst.comp Primrec.unpair
  have r : Primrec (fun n : ℕ => n.unpair.2) := Primrec.snd.comp Primrec.unpair
  exact Primrec.ite
    ((Primrec.nat_lt.comp (r.comp l) (l.comp l)).and
      (Primrec.nat_lt.comp (Primrec.const 0) r)) (Primrec.const 1) (Primrec.const 0)

def snapshotCode : Code :=
  .comp (embed (ordinaryProgram snapshotDecode snapshot_decode_primitive.to_comp))
    (.pair identityCode
      (.comp boundedCode (embed (ordinaryProgram snapshotInput snapshot_input_primitive.to_comp))))

def snapshotIndex (s : ℕ) : ℕ :=
  OracleProgramNumberings.specialize (encodeCode snapshotCode) s

theorem snapshot_index_primitive : Primrec snapshotIndex := by
  exact OracleProgramNumberings.specialize_primitive.comp (Primrec.const (encodeCode snapshotCode)) Primrec.id

theorem snapshot_code_eval (B : Set ℕ) (s i : ℕ) :
    eval B snapshotCode (Nat.pair s i) = Part.some (stageBit B s i) := by
  rw [snapshotCode, eval]
  have hp : eval B (.pair identityCode
      (.comp boundedCode (embed (ordinaryProgram snapshotInput snapshot_input_primitive.to_comp))))
      (Nat.pair s i) = Part.some (Nat.pair (Nat.pair s i) (boundedValue B s i i)) := by
    simp only [eval, identity_eval, eval_embed, BusyBeaverFunctions.ordinaryProgram_eval,
      snapshotInput, Nat.unpair_pair, Part.bind_some, bounded_code_eval, Part.map_some]
  rw [hp, Part.bind_some, eval_embed, BusyBeaverFunctions.ordinaryProgram_eval]
  congr 1
  simp only [snapshotDecode, Nat.unpair_pair, stageBit, indicator, jumpStage,
    Set.ofPred]
  split_ifs <;> rfl

theorem snapshot_index_eval (B : Set ℕ) (s i : ℕ) :
    OracleProgramNumberings.phi B (snapshotIndex s) i = Part.some (stageBit B s i) := by
  rw [snapshotIndex, OracleProgramNumberings.specialize_eval]
  simpa only [OracleProgramNumberings.phi, decode_encode] using snapshot_code_eval B s i

theorem snapshot_joint_computable (B : Set ℕ) : JointComputableIn B (stageBit B) := by
  apply (joint_index_iff B (stageBit B)).mpr
  refine ⟨encodeCode snapshotCode, fun s i => ?_⟩
  simpa only [OracleProgramNumberings.phi, decode_encode] using snapshot_code_eval B s i

theorem jump_prefix_stability (B : Set ℕ) (k : ℕ) :
    ∃ S, ∀ s, S ≤ s → ∀ q < k, stageBit B s q = indicator (TuringJump.jump B) q := by
  classical
  have hd := jump_stage_data B
  have hc : ConvergesTo (stageBit B) (indicator (TuringJump.jump B)) := by
    intro q
    by_cases hq : q ∈ TuringJump.jump B
    · obtain ⟨S, hS⟩ := (hd.2.2.2 q).mp hq
      refine ⟨S, fun s hs => ?_⟩
      have hsq : q ∈ jumpStage B s := hd.2.1 hs hS
      change (if q ∈ jumpStage B s then 1 else 0) =
        (if q ∈ TuringJump.jump B then 1 else 0)
      rw [ite_eq_left hsq, ite_eq_left hq]
    · refine ⟨0, fun s _ => ?_⟩
      have hn : q ∉ jumpStage B s := fun h => hq ((hd.2.2.2 q).mpr ⟨s,h⟩)
      change (if q ∈ jumpStage B s then 1 else 0) =
        (if q ∈ TuringJump.jump B then 1 else 0)
      rw [ite_eq_right hn, ite_eq_right hq]
  exact finite_prefix_stability (stageBit B) (indicator (TuringJump.jump B)) hc k

-- The input is (e,(s,x)); the compiled index uses the characteristic program h(s).
def virtualInput (w : ℕ) : ℕ :=
  let e := w.unpair.1
  let s := w.unpair.2.unpair.1
  let x := w.unpair.2.unpair.2
  Nat.pair (TuringJump.translate (snapshotIndex s) (encodeCode boundedCode))
    (Nat.pair s (Nat.pair e x))

theorem virtual_input_primitive : Primrec virtualInput := by
  have l : Primrec (fun n : ℕ => n.unpair.1) := Primrec.fst.comp Primrec.unpair
  have r : Primrec (fun n : ℕ => n.unpair.2) := Primrec.snd.comp Primrec.unpair
  exact Primrec₂.natPair.comp
    (TuringJump.translate_primitive.comp (snapshot_index_primitive.comp (l.comp r))
      (Primrec.const (encodeCode boundedCode)))
    (Primrec₂.natPair.comp (l.comp r) (Primrec₂.natPair.comp l (r.comp r)))

def virtualCode : Code :=
  .comp universalCode (embed (ordinaryProgram virtualInput virtual_input_primitive.to_comp))

def virtualValue (B : Set ℕ) (s e x : ℕ) : ℕ :=
  OracleProgramNumberings.boundedValue (jumpStage B s) s e x

theorem virtual_code_eval (B : Set ℕ) (s e x : ℕ) :
    eval B virtualCode (Nat.pair e (Nat.pair s x)) = Part.some (virtualValue B s e x) := by
  rw [virtualCode, eval, eval_embed, BusyBeaverFunctions.ordinaryProgram_eval, Part.bind_some]
  simp only [virtualInput, Nat.unpair_pair]
  rw [universal_code_eval]
  have hd : TuringDegrees.Reduces (decodeCode (snapshotIndex s)) (jumpStage B s) B :=
    fun i => snapshot_index_eval B s i
  rw [TuringJump.translate_eval (jumpStage B s) B (snapshotIndex s) hd]
  simp only [OracleProgramNumberings.phi, decode_encode, bounded_code_eval, virtualValue]

def numericalApproximation (B : Set ℕ) (e : ℕ) (s x : ℕ) : ℕ :=
  virtualValue B s e x - 1

def binaryApproximation (B : Set ℕ) (e : ℕ) (s x : ℕ) : ℕ :=
  if virtualValue B s e x = 2 then 1 else 0

def isTwo (n : ℕ) : ℕ := if n = 2 then 1 else 0

theorem is_two_primitive : Primrec isTwo := by
  exact Primrec.ite (Primrec.eq.comp Primrec.id (Primrec.const 2)) (Primrec.const 1) (Primrec.const 0)

def numericalCode : Code := .comp predecessorCode virtualCode

def binaryCode : Code :=
  .comp (embed (ordinaryProgram isTwo is_two_primitive.to_comp)) virtualCode

def numericalIndex (e : ℕ) : ℕ :=
  OracleProgramNumberings.specialize (encodeCode numericalCode) e

def binaryIndex (e : ℕ) : ℕ :=
  OracleProgramNumberings.specialize (encodeCode binaryCode) e

theorem numerical_index_primitive : Primrec numericalIndex := by
  exact OracleProgramNumberings.specialize_primitive.comp (Primrec.const (encodeCode numericalCode)) Primrec.id

theorem binary_index_primitive : Primrec binaryIndex := by
  exact OracleProgramNumberings.specialize_primitive.comp (Primrec.const (encodeCode binaryCode)) Primrec.id

theorem numerical_index_eval (B : Set ℕ) (e s x : ℕ) :
    OracleProgramNumberings.phi B (numericalIndex e) (Nat.pair s x) =
      Part.some (numericalApproximation B e s x) := by
  rw [numericalIndex, OracleProgramNumberings.specialize_eval]
  simp only [OracleProgramNumberings.phi, decode_encode]
  rw [numericalCode, eval, virtual_code_eval, Part.bind_some, predecessor_eval]
  rfl

theorem binary_index_eval (B : Set ℕ) (e s x : ℕ) :
    OracleProgramNumberings.phi B (binaryIndex e) (Nat.pair s x) =
      Part.some (binaryApproximation B e s x) := by
  rw [binaryIndex, OracleProgramNumberings.specialize_eval]
  simp only [OracleProgramNumberings.phi, decode_encode]
  rw [binaryCode, eval, virtual_code_eval, Part.bind_some, eval_embed,
    BusyBeaverFunctions.ordinaryProgram_eval]
  rfl

theorem numerical_joint_computable (B : Set ℕ) (e : ℕ) :
    JointComputableIn B (numericalApproximation B e) := by
  exact (joint_index_iff B (numericalApproximation B e)).mpr
    ⟨numericalIndex e, numerical_index_eval B e⟩

theorem binary_joint_computable (B : Set ℕ) (e : ℕ) :
    JointComputableIn B (binaryApproximation B e) := by
  exact (joint_index_iff B (binaryApproximation B e)).mpr
    ⟨binaryIndex e, binary_index_eval B e⟩

theorem binary_approximation_bits (B : Set ℕ) (e : ℕ) :
    LimitComputability.Binary (binaryApproximation B e) := by
  intro s x
  unfold binaryApproximation
  split_ifs <;> simp

theorem fixed_prefix_replay (B : Set ℕ) (k e x y : ℕ)
    (h : OracleProgramNumberings.boundedValue (TuringJump.jump B) k e x = y + 1) :
    ∃ S, ∀ s, S ≤ s →
      OracleProgramNumberings.boundedValue (jumpStage B s) k e x = y + 1 ∧
        virtualValue B s e x = y + 1 := by
  obtain ⟨S, hS⟩ := jump_prefix_stability B k
  refine ⟨max S k, fun s hs => ?_⟩
  have hq : ∀ q < k, indicator (TuringJump.jump B) q = indicator (jumpStage B s) q :=
    fun q hq => (hS s (by omega) q hq).symm
  have heq := PostsTheorem.bounded_query_dependence
    (indicator (TuringJump.jump B)) (indicator (jumpStage B s)) k hq (decodeCode e) x
  have hv : boundedValue (jumpStage B s) k e x = y + 1 := by
    unfold OracleProgramNumberings.boundedValue bounded
    simp only [Membership.mem, Set.Mem]
    rw [← heq]
    exact h
  exact ⟨hv, bounded_value_mono (jumpStage B s) k s e x y (by omega) hv⟩

theorem numerical_convergence (B : Set ℕ) (e : ℕ) (f : ℕ → ℕ)
    (he : ∀ x, OracleProgramNumberings.phi (TuringJump.jump B) e x = Part.some (f x)) :
    ConvergesTo (numericalApproximation B e) f := by
  intro x
  obtain ⟨k, hk⟩ := (phi_output_certificate (TuringJump.jump B) e x (f x)).mp
    (Part.eq_some_iff.mp (he x))
  obtain ⟨S, hS⟩ := fixed_prefix_replay B k e x (f x) hk
  refine ⟨S, fun s hs => ?_⟩
  simp only [numericalApproximation, (hS s hs).2, Nat.add_sub_cancel]

theorem binary_convergence (B X : Set ℕ) (e : ℕ)
    (he : ∀ x, OracleProgramNumberings.phi (TuringJump.jump B) e x = Part.some (indicator X x)) :
    ConvergesTo (binaryApproximation B e) (indicator X) := by
  classical
  intro x
  obtain ⟨k, hk⟩ := (phi_output_certificate (TuringJump.jump B) e x (indicator X x)).mp
    (Part.eq_some_iff.mp (he x))
  obtain ⟨S, hS⟩ := fixed_prefix_replay B k e x (indicator X x) hk
  refine ⟨S, fun s hs => ?_⟩
  rw [binaryApproximation, (hS s hs).2]
  change (if (if x ∈ X then 1 else 0) + 1 = 2 then 1 else 0) =
    (if x ∈ X then 1 else 0)
  by_cases hx : x ∈ X <;> simp [hx]

end
end Lemmatheca.ComputabilityTheory.RelativizedLimitComputability
