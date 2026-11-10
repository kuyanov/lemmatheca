import Lemmatheca.HighDegreesAndDomination.Definitions

/-! Success-first races and the actual common oracle-program driver. -/
namespace Lemmatheca.ComputabilityTheory.HighDegreesAndDomination

open UniversalComputation OracleComputation OracleProgramNumberings
open BusyBeaverFunctions (ordinaryProgram ordinaryProgram_eval)
open LimitComputability (Approximation)

noncomputable section
open Classical
set_option backward.isDefEq.respectTransparency false

def raceSearch (a : Approximation) (n e : ℕ) : Part ℕ :=
  (Nat.rfind (fun j => Part.some
    (decide (0 < UniversalComputation.boundedValue (n + j) e n ∨ a (n + j) e = 0)))).map
      (fun j => n + j)

def candidatePart (a : Approximation) (n e : ℕ) : Part ℕ :=
  if n < e ∨ a n e = 0 then Part.some 0
  else (raceSearch a n e).map (fun r => UniversalComputation.boundedValue r e n - 1)

private theorem ordinary_success_later {k l e x : ℕ} (hkl : k ≤ l)
    (hk : 0 < UniversalComputation.boundedValue k e x) :
    0 < UniversalComputation.boundedValue l e x := by
  have hv : UniversalComputation.boundedValue k e x = (UniversalComputation.boundedValue k e x - 1) + 1 := by omega
  have hm := Nat.Partrec.Code.evaln_mono hkl ((UniversalComputation.boundedValue_output k e x _).mp hv)
  have hl := (UniversalComputation.boundedValue_output l e x _).mpr hm
  omega

theorem candidate_terminates (a : Approximation) (ha : IsTotalityApprox a) (n e : ℕ) :
    (candidatePart a n e).Dom := by
  by_cases hun : n < e ∨ a n e = 0
  · simp only [candidatePart, ite_eq_left hun, Part.some_dom]
  · change (if n < e ∨ a n e = 0 then Part.some 0 else
      (raceSearch a n e).map (fun r => UniversalComputation.boundedValue r e n - 1)).Dom
    rw [ite_eq_right hun]
    change (Nat.rfind (fun j => Part.some
      (decide (0 < UniversalComputation.boundedValue (n + j) e n ∨ a (n + j) e = 0)))).Dom
    apply Nat.rfind_dom.mpr
    by_cases he : e ∈ Lemmatheca.Entry.ArithmeticalHierarchy.Totality
    · obtain ⟨k, hk⟩ := (UniversalComputation.phi_domain e n).mp (he n)
      have hs : 0 < UniversalComputation.boundedValue (n + k) e n :=
        ordinary_success_later (by omega) hk
      exact ⟨k, by simp [hs], fun _ => trivial⟩
    · obtain ⟨S, hS⟩ := ha.2 e
      have hz : a (n + S) e = 0 := by
        have h := hS (n + S) (by omega)
        simp only [Membership.mem, Set.Mem] at he
        simpa [indicator, he] using h
      exact ⟨S, by simp [hz], fun _ => trivial⟩

def candidateValue (a : Approximation) (ha : IsTotalityApprox a) (n e : ℕ) : ℕ :=
  (candidatePart a n e).get (candidate_terminates a ha n e)

theorem candidate_value_correct (a : Approximation) (ha : IsTotalityApprox a) (n e : ℕ) :
    candidatePart a n e = Part.some (candidateValue a ha n e) ∧
      ((n < e ∨ a n e = 0) → candidateValue a ha n e = 0) := by
  have hv : candidatePart a n e = Part.some (candidateValue a ha n e) :=
    (Part.some_get (candidate_terminates a ha n e)).symm
  refine ⟨hv, fun hun => ?_⟩
  rw [candidatePart, ite_eq_left hun] at hv
  exact (Part.some_inj.mp hv).symm

theorem race_first_success (a : Approximation) (n e r : ℕ) (hr : r ∈ raceSearch a n e) :
    n ≤ r ∧ (0 < UniversalComputation.boundedValue r e n ∨ a r e = 0) ∧
      ∀ t, n ≤ t → t < r →
        UniversalComputation.boundedValue t e n = 0 ∧ a t e ≠ 0 := by
  obtain ⟨j, hj, rfl⟩ := (Part.mem_map_iff _).mp hr
  have hs : 0 < UniversalComputation.boundedValue (n + j) e n ∨ a (n + j) e = 0 := by
    simpa using Nat.rfind_spec hj
  refine ⟨by omega, hs, ?_⟩
  intro t hnt ht
  have hm : ¬ (0 < UniversalComputation.boundedValue (n + (t - n)) e n ∨ a (n + (t - n)) e = 0) := by
    simpa using Nat.rfind_min hj (show t - n < j by omega)
  have he : n + (t - n) = t := by omega
  rw [he] at hm
  exact ⟨by omega, fun hz => hm (Or.inr hz)⟩

theorem selected_total_value (a : Approximation) (ha : IsTotalityApprox a) (n e y : ℕ)
    (hen : e ≤ n) (ha1 : ∀ r, n ≤ r → a r e = 1)
    (hy : UniversalComputation.phi e n = Part.some y) :
    candidateValue a ha n e = y := by
  have hun : ¬ (n < e ∨ a n e = 0) := by
    have h := ha1 n le_rfl
    omega
  have hv := Part.eq_some_iff.mp (candidate_value_correct a ha n e).1
  rw [candidatePart, ite_eq_right hun] at hv
  obtain ⟨r, hr, hv⟩ := (Part.mem_map_iff _).mp hv
  have hs := race_first_success a n e r hr
  have hguess := ha1 r hs.1
  have hp : 0 < UniversalComputation.boundedValue r e n := by rcases hs.2.1 with h | h; exact h; omega
  have hout : UniversalComputation.boundedValue r e n - 1 ∈ UniversalComputation.phi e n :=
    (UniversalComputation.phi_output e n _).mpr ⟨r, by omega⟩
  rw [hy] at hout
  exact hv.symm.trans (Part.mem_some_iff.mp hout)

-- Search input w=(p,r), with p=(c,(n,e)).
private def boundedAt (w : ℕ) : ℕ :=
  UniversalComputation.boundedValue w.unpair.2 w.unpair.1.unpair.2.unpair.2
    w.unpair.1.unpair.2.unpair.1
private def approxInput (w : ℕ) : ℕ :=
  Nat.pair w.unpair.1.unpair.1 (Nat.pair w.unpair.2 w.unpair.1.unpair.2.unpair.2)
private def initialInput (p : ℕ) : ℕ :=
  Nat.pair p.unpair.1 (Nat.pair p.unpair.2.unpair.1 p.unpair.2.unpair.2)
private def startInput (p : ℕ) : ℕ := Nat.pair p p.unpair.2.unpair.1
private def eligibleBit (p : ℕ) : ℕ :=
  if p.unpair.2.unpair.2 ≤ p.unpair.2.unpair.1 then 1 else 0
private def raceOutput (w : ℕ) : ℕ := boundedAt w - 1

private theorem input_routines_computable :
    Computable boundedAt ∧ Computable approxInput ∧ Computable initialInput ∧
      Computable startInput ∧ Computable eligibleBit ∧ Computable raceOutput := by
  have l : Primrec (fun p : ℕ => p.unpair.1) := Primrec.fst.comp Primrec.unpair
  have r : Primrec (fun p : ℕ => p.unpair.2) := Primrec.snd.comp Primrec.unpair
  have hb : Primrec boundedAt := UniversalComputation.boundedValue_primitive.comp
    ((r.pair (r.comp (r.comp l))).pair (l.comp (r.comp l)))
  have ha : Primrec approxInput := Primrec₂.natPair.comp (l.comp l)
    (Primrec₂.natPair.comp r (r.comp (r.comp l)))
  have hi : Primrec initialInput := Primrec₂.natPair.comp l
    (Primrec₂.natPair.comp (l.comp r) (r.comp r))
  have hs : Primrec startInput := Primrec₂.natPair.comp Primrec.id (l.comp r)
  have he : Primrec eligibleBit := Primrec.ite
    (Primrec.nat_le.comp (r.comp r) (l.comp r)) (Primrec.const 1) (Primrec.const 0)
  have ho : Primrec raceOutput := Primrec.nat_sub.comp hb (Primrec.const 1)
  exact ⟨hb.to_comp, ha.to_comp, hi.to_comp, hs.to_comp, he.to_comp, ho.to_comp⟩

-- The primitive-recursion branch has a harmless zero base. The approximation
-- call is executed only at bit1, when the ordinary bounded checker failed.
def raceTestCode : Code :=
  .comp (.prec .zero (.comp
      (.comp universalCode (embed (ordinaryProgram approxInput input_routines_computable.2.1))) .left))
    (.pair identityCode (.comp (embed zeroTest)
      (embed (ordinaryProgram boundedAt input_routines_computable.1))))

def raceCoreCode : Code :=
  .comp (embed (ordinaryProgram raceOutput input_routines_computable.2.2.2.2.2))
    (.pair .left (.find' raceTestCode))

private def initialApproxCode : Code :=
  .comp universalCode (embed (ordinaryProgram initialInput input_routines_computable.2.2.1))

private def runSelectedCode : Code :=
  .comp (.prec .zero (.comp
      (.comp raceCoreCode (embed (ordinaryProgram startInput input_routines_computable.2.2.2.1))) .left))
    (.pair identityCode (.comp (embed zeroTest) (.comp (embed zeroTest) initialApproxCode)))

def candidateDriverCode : Code :=
  .comp (.prec .zero (.comp runSelectedCode .left))
    (.pair identityCode (embed (ordinaryProgram eligibleBit input_routines_computable.2.2.2.2.1)))

theorem race_test_eval (A : Set ℕ) (c n e r : ℕ) :
    eval A raceTestCode (Nat.pair (Nat.pair c (Nat.pair n e)) r) =
      if 0 < UniversalComputation.boundedValue r e n then Part.some 0
      else OracleProgramNumberings.phi A c (Nat.pair r e) := by
  by_cases hb : UniversalComputation.boundedValue r e n = 0
  · simp [raceTestCode, eval, identity_eval, eval_embed, ordinaryProgram_eval, boundedAt,
      approxInput, Nat.unpair_pair, zeroTest_eval, hb, universal_code_eval]
  · have hp : 0 < UniversalComputation.boundedValue r e n := by omega
    simp [raceTestCode, eval, identity_eval, eval_embed, ordinaryProgram_eval, boundedAt,
      Nat.unpair_pair, zeroTest_eval, hb, hp]

theorem race_core_eval (A : Set ℕ) (c : ℕ) (a : Approximation)
    (hc : ∀ s e, OracleProgramNumberings.phi A c (Nat.pair s e) = Part.some (a s e)) (n e : ℕ) :
    eval A raceCoreCode (Nat.pair (Nat.pair c (Nat.pair n e)) n) =
      (raceSearch a n e).map (fun r => UniversalComputation.boundedValue r e n - 1) := by
  have ht (j : ℕ) :
      (eval A raceTestCode (Nat.pair (Nat.pair c (Nat.pair n e)) (j + n))).map
          (fun v => decide (v = 0)) =
        Part.some (decide (0 < UniversalComputation.boundedValue (n + j) e n ∨ a (n + j) e = 0)) := by
    rw [race_test_eval]
    by_cases hb : 0 < UniversalComputation.boundedValue (n + j) e n
    · simp [hb, Nat.add_comm]
    · simp [hb, hc, Nat.add_comm]
  have hout : eval A (embed (ordinaryProgram raceOutput input_routines_computable.2.2.2.2.2)) =
      (fun w => Part.some (raceOutput w)) := by
    funext w
    simp only [eval_embed, ordinaryProgram_eval]
  simp only [raceCoreCode, eval, Part.bind_some, Part.map_map, Nat.unpair_pair, ht]
  rw [hout, Part.bind_some_eq_map]
  simp only [raceSearch, Part.map_map, Function.comp_def, raceOutput, boundedAt, Nat.unpair_pair,
    Nat.add_comm]

theorem candidate_driver_eval (A : Set ℕ) (c : ℕ) (a : Approximation)
    (hc : ∀ s e, OracleProgramNumberings.phi A c (Nat.pair s e) = Part.some (a s e)) (n e : ℕ) :
    eval A candidateDriverCode (Nat.pair c (Nat.pair n e)) = candidatePart a n e := by
  have hi : eval A initialApproxCode (Nat.pair c (Nat.pair n e)) = Part.some (a n e) := by
    simp only [initialApproxCode, eval, eval_embed, ordinaryProgram_eval, initialInput,
      Nat.unpair_pair, Part.bind_some, universal_code_eval, hc]
  have hs : eval A runSelectedCode (Nat.pair c (Nat.pair n e)) =
      if a n e = 0 then Part.some 0 else
        (raceSearch a n e).map (fun r => UniversalComputation.boundedValue r e n - 1) := by
    by_cases h0 : a n e = 0
    · simp [runSelectedCode, eval, identity_eval, hi, eval_embed, ordinaryProgram_eval,
        startInput, Nat.unpair_pair, zeroTest_eval, h0]
    · simp [runSelectedCode, eval, identity_eval, hi, eval_embed, ordinaryProgram_eval,
        startInput, Nat.unpair_pair, zeroTest_eval, h0, race_core_eval A c a hc n e]
  by_cases hen : e ≤ n
  · have hn : ¬ n < e := by omega
    simpa [candidateDriverCode, eval, identity_eval, eval_embed, ordinaryProgram_eval,
      eligibleBit, Nat.unpair_pair, hen, candidatePart, hn] using hs
  · have hn : n < e := by omega
    simp [candidateDriverCode, eval, identity_eval, eval_embed, ordinaryProgram_eval,
      eligibleBit, Nat.unpair_pair, hen, candidatePart, hn]

end
end Lemmatheca.ComputabilityTheory.HighDegreesAndDomination
