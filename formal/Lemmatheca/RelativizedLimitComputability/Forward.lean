import Lemmatheca.RelativizedLimitComputability.Basic

namespace Lemmatheca.ComputabilityTheory.RelativizedLimitComputability

open OracleComputation OracleProgramNumberings UniversalComputation
open BusyBeaverFunctions (ordinaryProgram equalityBit equalityBit_computable)
open LimitComputability (Approximation FutureChange)

noncomputable section

set_option backward.isDefEq.respectTransparency false

-- The input of the common recognizer is (e,(x,s)).
def baseInput (p : ℕ) : ℕ :=
  Nat.pair p.unpair.1 (Nat.pair p.unpair.2.unpair.2 p.unpair.2.unpair.1)

theorem base_input_primitive : Primrec baseInput := by
  have l : Primrec (fun n : ℕ => n.unpair.1) := Primrec.fst.comp Primrec.unpair
  have r : Primrec (fun n : ℕ => n.unpair.2) := Primrec.snd.comp Primrec.unpair
  exact Primrec₂.natPair.comp l (Primrec₂.natPair.comp (r.comp r) (l.comp r))

-- The search input is ((p,v),r), with p=(e,(x,s)).
def candidateInput (w : ℕ) : ℕ :=
  let p := w.unpair.1.unpair.1
  Nat.pair p.unpair.1
    (Nat.pair (p.unpair.2.unpair.2 + w.unpair.2 + 1) p.unpair.2.unpair.1)

theorem candidate_input_primitive : Primrec candidateInput := by
  have l : Primrec (fun n : ℕ => n.unpair.1) := Primrec.fst.comp Primrec.unpair
  have r : Primrec (fun n : ℕ => n.unpair.2) := Primrec.snd.comp Primrec.unpair
  have p := l.comp l
  exact Primrec₂.natPair.comp (l.comp p)
    (Primrec₂.natPair.comp
      (Primrec.succ.comp (Primrec.nat_add.comp (r.comp (r.comp p)) r))
      (l.comp (r.comp p)))

def oldValue (w : ℕ) : ℕ := w.unpair.1.unpair.2

theorem old_value_primitive : Primrec oldValue := by
  exact (Primrec.snd.comp Primrec.unpair).comp (Primrec.fst.comp Primrec.unpair)

def changeTestCode : Code :=
  .comp (embed (ordinaryProgram equalityBit equalityBit_computable))
    (.pair
      (.comp universalCode
        (embed (ordinaryProgram candidateInput candidate_input_primitive.to_comp)))
      (embed (ordinaryProgram oldValue old_value_primitive.to_comp)))

def changeRecognizerCode : Code :=
  .comp (.comp .zero (.find' changeTestCode))
    (.pair (.pair identityCode
      (.comp universalCode (embed (ordinaryProgram baseInput base_input_primitive.to_comp)))) .zero)

def changeRecognizerIndex : ℕ := encodeCode changeRecognizerCode

def changeIndex (e x s : ℕ) : ℕ :=
  TuringJump.freeze changeRecognizerIndex (Nat.pair e (Nat.pair x s))

def changeInput (w : ℕ) : ℕ :=
  changeIndex w.unpair.1.unpair.1 w.unpair.1.unpair.2 w.unpair.2

theorem change_index_primitive : Primrec changeInput := by
  have l : Primrec (fun n : ℕ => n.unpair.1) := Primrec.fst.comp Primrec.unpair
  have r : Primrec (fun n : ℕ => n.unpair.2) := Primrec.snd.comp Primrec.unpair
  exact TuringJump.freeze_primitive.comp (Primrec.const changeRecognizerIndex)
    (Primrec₂.natPair.comp (l.comp l) (Primrec₂.natPair.comp (r.comp l) r))

theorem change_recognizer_value (B : Set ℕ) (e : ℕ) (a : Approximation)
    (he : ∀ s x, OracleProgramNumberings.phi B e (Nat.pair s x) = Part.some (a s x))
    (x s : ℕ) :
    eval B changeRecognizerCode (Nat.pair e (Nat.pair x s)) =
      Part.assert (FutureChange a x s) (fun _ => Part.some 0) := by
  classical
  have ht (r : ℕ) : eval B changeTestCode
      (Nat.pair (Nat.pair (Nat.pair e (Nat.pair x s)) (a s x)) r) =
      Part.some (if a (s + r + 1) x = a s x then 1 else 0) := by
    simp only [changeTestCode, eval, eval_embed, BusyBeaverFunctions.ordinaryProgram_eval,
      Part.bind_some, Part.map_some, candidateInput, oldValue, Nat.unpair_pair,
      universal_code_eval, he]
    simp [BusyBeaverFunctions.equalityBit]
  have hv : eval B changeRecognizerCode (Nat.pair e (Nat.pair x s)) =
      (Nat.rfind (fun r => Part.some (decide (a (s + r + 1) x ≠ a s x)))).map
        (fun _ => 0) := by
    simp only [changeRecognizerCode, eval, identity_eval, eval_embed,
      BusyBeaverFunctions.ordinaryProgram_eval, baseInput, Nat.unpair_pair,
      Part.bind_some, Part.map_some, universal_code_eval, he, Nat.add_zero, ht,
      Part.bind_map]
    rw [Part.bind_some_eq_map]
    apply congrArg (Part.map (fun _ : ℕ => 0))
    congr 1
    funext r
    by_cases h : a (s + r + 1) x = a s x <;> simp [h]
  rw [hv]
  have hd : (Nat.rfind (fun r => Part.some (decide (a (s + r + 1) x ≠ a s x)))).Dom ↔
      FutureChange a x s := by
    simp only [Nat.rfind_dom, Part.mem_some_iff, true_eq_decide_iff, Part.some_dom,
      implies_true, and_true]
    constructor
    · rintro ⟨r, hr⟩
      exact ⟨s + r + 1, by omega, hr⟩
    · rintro ⟨t, hst, hne⟩
      refine ⟨t - s - 1, ?_⟩
      have h : s + (t - s - 1) + 1 = t := by omega
      simpa [h] using hne
  apply Part.ext
  intro y
  simp only [Part.mem_map_iff, Part.mem_assert_iff, Part.mem_some_iff]
  constructor
  · rintro ⟨r, hr, rfl⟩
    exact ⟨hd.mp hr.fst, rfl⟩
  · rintro ⟨h, rfl⟩
    obtain ⟨r, hr⟩ := Part.dom_iff_mem.mp (hd.mpr h)
    exact ⟨r, hr, rfl⟩

theorem change_index_correct (B : Set ℕ) (e : ℕ) (a : Approximation)
    (he : ∀ s x, OracleProgramNumberings.phi B e (Nat.pair s x) = Part.some (a s x))
    (x s : ℕ) : changeIndex e x s ∈ TuringJump.jump B ↔ FutureChange a x s := by
  change (OracleProgramNumberings.phi B (changeIndex e x s) (changeIndex e x s)).Dom ↔ _
  rw [changeIndex, TuringJump.freeze_eval]
  change (eval B (decodeCode changeRecognizerIndex) (Nat.pair e (Nat.pair x s))).Dom ↔ _
  rw [changeRecognizerIndex, decode_encode, change_recognizer_value B e a he]
  simp [Part.assert]

-- A fixed program queries the jump at the ordinary membership-map image.
def membershipInput (n : ℕ) : ℕ := TuringJump.queryMap 1 n

def baseQueryCode : Code :=
  .comp .query (embed (ordinaryProgram membershipInput
    (TuringJump.query_map_primitive 1).to_comp))

def baseUniversalCode : Code := subst baseQueryCode universalCode

def futureQueryCode : Code :=
  .comp .query (embed (ordinaryProgram changeInput change_index_primitive.to_comp))

def stableSearchCode : Code :=
  .comp (.find' futureQueryCode) (.pair identityCode .zero)

-- The driver input is (e,x); pair the stable stage with x for the base evaluator.
def stableDriverCode : Code :=
  .comp baseUniversalCode
    (.pair .left (.pair stableSearchCode .right))

def stableIndex (e : ℕ) : ℕ :=
  OracleProgramNumberings.specialize (encodeCode stableDriverCode) e

theorem stable_index_primitive : Primrec stableIndex := by
  exact specialize_primitive.comp (Primrec.const (encodeCode stableDriverCode)) Primrec.id

theorem base_query_eval (B : Set ℕ) (n : ℕ) :
    eval (TuringJump.jump B) baseQueryCode n = Part.some (indicator B n) := by
  classical
  unfold baseQueryCode
  rw [eval, eval_embed, BusyBeaverFunctions.ordinaryProgram_eval, Part.bind_some]
  rw [eval]
  congr 1
  change (if TuringJump.queryMap 1 n ∈ TuringJump.jump B then 1 else 0) =
    (if n ∈ B then 1 else 0)
  rw [← (TuringJump.membership_maps B n).1]

theorem base_universal_eval (B : Set ℕ) (e z : ℕ) :
    eval (TuringJump.jump B) baseUniversalCode (Nat.pair e z) =
      OracleProgramNumberings.phi B e z := by
  rw [baseUniversalCode, subst_eval B (TuringJump.jump B) baseQueryCode
    (base_query_eval B), universal_code_eval]

theorem stable_stage_exists (a : Approximation) (f : ℕ → ℕ)
    (ha : ConvergesTo a f) (x : ℕ) : ∃ s, ¬ FutureChange a x s := by
  obtain ⟨t, ht⟩ := ha x
  refine ⟨t, ?_⟩
  rintro ⟨r, htr, hne⟩
  exact hne ((ht r (by omega)).trans (ht t le_rfl).symm)

def stableStage (a : Approximation) (f : ℕ → ℕ)
    (ha : ConvergesTo a f) (x : ℕ) : ℕ := by
  classical
  exact Nat.find (stable_stage_exists a f ha x)

theorem stable_stage_spec (a : Approximation) (f : ℕ → ℕ)
    (ha : ConvergesTo a f) (x : ℕ) :
    ¬ FutureChange a x (stableStage a f ha x) ∧
      (∀ s < stableStage a f ha x, FutureChange a x s) ∧
      a (stableStage a f ha x) x = f x := by
  classical
  have hs : ¬ FutureChange a x (stableStage a f ha x) :=
    Nat.find_spec (stable_stage_exists a f ha x)
  have hmin : ∀ s < stableStage a f ha x, FutureChange a x s := by
    intro s hlt
    by_contra hn
    have hh : stableStage a f ha x ≤ s := Nat.find_min' _ hn
    omega
  refine ⟨hs, hmin, ?_⟩
  obtain ⟨t, ht⟩ := ha x
  let r := max t (stableStage a f ha x + 1)
  have hsr : stableStage a f ha x < r := by dsimp [r]; omega
  have he : a r x = a (stableStage a f ha x) x := by
    by_contra hn
    exact hs ⟨r, hsr, hn⟩
  exact he.symm.trans (ht r (by dsimp [r]; omega))

theorem stable_search_eval (B : Set ℕ) (e : ℕ) (a : Approximation)
    (he : ∀ s x, OracleProgramNumberings.phi B e (Nat.pair s x) = Part.some (a s x))
    (f : ℕ → ℕ) (ha : ConvergesTo a f) (x : ℕ) :
    eval (TuringJump.jump B) stableSearchCode (Nat.pair e x) =
      Part.some (stableStage a f ha x) := by
  classical
  have hq (s : ℕ) : eval (TuringJump.jump B) futureQueryCode (Nat.pair (Nat.pair e x) s) =
      Part.some (if FutureChange a x s then 1 else 0) := by
    unfold futureQueryCode
    rw [eval, eval_embed, BusyBeaverFunctions.ordinaryProgram_eval, Part.bind_some, eval]
    simp only [changeInput, Nat.unpair_pair]
    congr 1
    change (if changeIndex e x s ∈ TuringJump.jump B then 1 else 0) = _
    rw [change_index_correct B e a he]
  rw [stableSearchCode, eval]
  have hp : eval (TuringJump.jump B) (.pair identityCode .zero) (Nat.pair e x) =
      Part.some (Nat.pair (Nat.pair e x) 0) := by
    simp only [eval, identity_eval, Part.bind_some, Part.map_some]
  rw [hp, Part.bind_some]
  rw [eval]
  simp only [Nat.unpair_pair, Nat.add_zero, hq, Part.map_some]
  rw [Part.map_id' (fun _ => rfl)]
  apply Part.eq_some_iff.mpr
  rw [Nat.mem_rfind]
  refine ⟨?_, ?_⟩
  · simp [(stable_stage_spec a f ha x).1]
  · intro t ht
    simp [(stable_stage_spec a f ha x).2.1 t ht]

theorem stable_index_eval (B : Set ℕ) (e : ℕ) (a : Approximation)
    (he : ∀ s x, OracleProgramNumberings.phi B e (Nat.pair s x) = Part.some (a s x))
    (f : ℕ → ℕ) (ha : ConvergesTo a f) (x : ℕ) :
    OracleProgramNumberings.phi (TuringJump.jump B) (stableIndex e) x = Part.some (f x) := by
  rw [stableIndex, OracleProgramNumberings.specialize_eval]
  simp only [OracleProgramNumberings.phi, decode_encode]
  rw [stableDriverCode, eval]
  have hp : eval (TuringJump.jump B) (.pair .left (.pair stableSearchCode .right))
      (Nat.pair e x) = Part.some (Nat.pair e (Nat.pair (stableStage a f ha x) x)) := by
    simp only [eval, Nat.unpair_pair, stable_search_eval B e a he f ha x,
      Part.bind_some, Part.map_some]
  rw [hp, Part.bind_some, base_universal_eval, he, (stable_stage_spec a f ha x).2.2]

end
end Lemmatheca.ComputabilityTheory.RelativizedLimitComputability
