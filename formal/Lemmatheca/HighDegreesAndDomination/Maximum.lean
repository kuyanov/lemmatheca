import Lemmatheca.HighDegreesAndDomination.Races

/-! The literal finite maximum and the numerical common-driver compiler R. -/
namespace Lemmatheca.ComputabilityTheory.HighDegreesAndDomination

open UniversalComputation OracleComputation OracleProgramNumberings TuringDegrees
open BusyBeaverFunctions (ordinaryProgram)
open LimitComputability (Approximation)

noncomputable section
set_option backward.isDefEq.respectTransparency false

def dominatingFunction (a : Approximation) (ha : IsTotalityApprox a) (n : ℕ) : ℕ :=
  1 + ((List.range (n + 1)).map (candidateValue a ha n)).foldl max 0

private def candidateInput (w : ℕ) : ℕ :=
  Nat.pair w.unpair.1.unpair.1 (Nat.pair w.unpair.1.unpair.2 w.unpair.2.unpair.1)
private def previousMaximum (w : ℕ) : ℕ := w.unpair.2.unpair.2
private def ordinaryMaximum (w : ℕ) : ℕ := max w.unpair.1 w.unpair.2
private def recursionInput (w : ℕ) : ℕ := Nat.pair w (w.unpair.2 + 1)

private theorem maximum_routines_computable :
    Computable candidateInput ∧ Computable previousMaximum ∧
      Computable ordinaryMaximum ∧ Computable recursionInput := by
  have hc : Primrec candidateInput :=
    Primrec₂.natPair.comp
      (Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair)))
      (Primrec₂.natPair.comp
        (Primrec.snd.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair)))
        (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))))
  have hp : Primrec previousMaximum :=
    Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))
  have hm : Primrec ordinaryMaximum := Primrec.nat_max.comp
    (Primrec.fst.comp Primrec.unpair) (Primrec.snd.comp Primrec.unpair)
  have hr : Primrec recursionInput := Primrec₂.natPair.comp Primrec.id
    (Primrec.succ.comp (Primrec.snd.comp Primrec.unpair))
  exact ⟨hc.to_comp,hp.to_comp,hm.to_comp,hr.to_comp⟩

private def maximumStepCode : Code :=
  .comp (embed (ordinaryProgram ordinaryMaximum maximum_routines_computable.2.2.1))
    (.pair (embed (ordinaryProgram previousMaximum maximum_routines_computable.2.1))
      (.comp candidateDriverCode (embed (ordinaryProgram candidateInput maximum_routines_computable.1))))

def maximumDriverCode : Code :=
  .comp .succ (.comp (.prec .zero maximumStepCode)
    (embed (ordinaryProgram recursionInput maximum_routines_computable.2.2.2)))

def dominatingCompiler (c : ℕ) : ℕ :=
  OracleProgramNumberings.specialize (encodeCode maximumDriverCode) c

theorem dominating_compiler_primitive : Primrec dominatingCompiler := by
  exact OracleProgramNumberings.specialize_primitive.comp
    (Primrec.const (encodeCode maximumDriverCode)) Primrec.id

theorem maximum_driver_eval (A : Set ℕ) (c : ℕ) (a : Approximation) (ha : IsTotalityApprox a)
    (hc : ∀ s e, OracleProgramNumberings.phi A c (Nat.pair s e) = Part.some (a s e)) (n : ℕ) :
    eval A maximumDriverCode (Nat.pair c n) = Part.some (dominatingFunction a ha n) := by
  have step_eval (e v : ℕ) :
      eval A maximumStepCode (Nat.pair (Nat.pair c n) (Nat.pair e v)) =
        Part.some (max v (candidateValue a ha n e)) := by
    have hcandidate : eval A (.comp candidateDriverCode
        (embed (ordinaryProgram candidateInput maximum_routines_computable.1)))
        (Nat.pair (Nat.pair c n) (Nat.pair e v)) =
        Part.some (candidateValue a ha n e) := by
      change (eval A (embed (ordinaryProgram candidateInput maximum_routines_computable.1))
        (Nat.pair (Nat.pair c n) (Nat.pair e v))).bind _ = _
      rw [eval_embed,BusyBeaverFunctions.ordinaryProgram_eval,Part.bind_some]
      simp only [candidateInput,Nat.unpair_pair]
      rw [candidate_driver_eval A c a hc,(candidate_value_correct a ha n e).1]
    have hprevious : eval A (embed (ordinaryProgram previousMaximum
        maximum_routines_computable.2.1)) (Nat.pair (Nat.pair c n) (Nat.pair e v)) =
        Part.some v := by
      rw [eval_embed,BusyBeaverFunctions.ordinaryProgram_eval]
      simp only [previousMaximum,Nat.unpair_pair]
    have hpair : eval A
        (.pair (embed (ordinaryProgram previousMaximum maximum_routines_computable.2.1))
          (.comp candidateDriverCode (embed (ordinaryProgram candidateInput maximum_routines_computable.1))))
        (Nat.pair (Nat.pair c n) (Nat.pair e v)) =
        Part.some (Nat.pair v (candidateValue a ha n e)) := by
      change (eval A (embed (ordinaryProgram previousMaximum maximum_routines_computable.2.1))
        (Nat.pair (Nat.pair c n) (Nat.pair e v))).bind _ = _
      rw [hprevious,Part.bind_some,hcandidate,Part.map_some]
    change (eval A
      (.pair (embed (ordinaryProgram previousMaximum maximum_routines_computable.2.1))
        (.comp candidateDriverCode (embed (ordinaryProgram candidateInput maximum_routines_computable.1))))
      (Nat.pair (Nat.pair c n) (Nat.pair e v))).bind _ = _
    rw [hpair,Part.bind_some,eval_embed,BusyBeaverFunctions.ordinaryProgram_eval]
    simp only [ordinaryMaximum,Nat.unpair_pair]
  have rec_eval : ∀ k, eval A (.prec .zero maximumStepCode) (Nat.pair (Nat.pair c n) k) =
      Part.some (((List.range k).map (candidateValue a ha n)).foldl max 0) := by
    intro k
    induction k with
    | zero => rw [eval_prec_zero];rfl
    | succ k ih =>
      rw [eval_prec_succ,ih,Part.bind_some,step_eval]
      simp only [List.range_succ,List.map_append,List.map_singleton,List.foldl_append,
        List.foldl_cons,List.foldl_nil]
  have hloop : eval A (.comp (.prec .zero maximumStepCode)
      (embed (ordinaryProgram recursionInput maximum_routines_computable.2.2.2))) (Nat.pair c n) =
      Part.some (((List.range (n+1)).map (candidateValue a ha n)).foldl max 0) := by
    change (eval A (embed (ordinaryProgram recursionInput maximum_routines_computable.2.2.2))
      (Nat.pair c n)).bind _ = _
    rw [eval_embed,BusyBeaverFunctions.ordinaryProgram_eval,Part.bind_some]
    simpa only [recursionInput,Nat.unpair_pair] using rec_eval (n+1)
  change (eval A (.comp (.prec .zero maximumStepCode)
    (embed (ordinaryProgram recursionInput maximum_routines_computable.2.2.2))) (Nat.pair c n)).bind _ = _
  rw [hloop,Part.bind_some]
  change Part.some (_+1) = Part.some (1+_)
  congr 1
  omega

theorem dominating_compiler_eval (A : Set ℕ) (c : ℕ) (a : Approximation) (ha : IsTotalityApprox a)
    (hc : ∀ s e, OracleProgramNumberings.phi A c (Nat.pair s e) = Part.some (a s e)) (n : ℕ) :
    OracleProgramNumberings.phi A (dominatingCompiler c) n =
      Part.some (dominatingFunction a ha n) := by
  rw [dominatingCompiler,OracleProgramNumberings.specialize_eval]
  simpa only [OracleProgramNumberings.phi,decode_encode] using
    maximum_driver_eval A c a ha hc n

theorem maximum_strictly_dominates (a : Approximation) (ha : IsTotalityApprox a)
    (f : ℕ → ℕ) (hf : Computable f) :
    ∃ N, ∀ n, N ≤ n → f n < dominatingFunction a ha n := by
  classical
  obtain ⟨e,he⟩ := UniversalComputation.phi_complete (Partrec.nat_iff.mp hf.partrec)
  have htotal : e ∈ Lemmatheca.Entry.ArithmeticalHierarchy.Totality := by
    intro x
    rw [congrFun he x]
    exact Part.some_dom _
  have hone : indicator Lemmatheca.Entry.ArithmeticalHierarchy.Totality e = 1 := by
    change (if e ∈ Lemmatheca.Entry.ArithmeticalHierarchy.Totality then 1 else 0) = 1
    rw [ite_eq_left htotal]
  obtain ⟨S,hS⟩ := ha.2 e
  have hS1 : ∀ r, S ≤ r → a r e = 1 := fun r hr => (hS r hr).trans hone
  have fold_bounds (xs : List ℕ) (z : ℕ) :
      z ≤ xs.foldl max z ∧ ∀ y ∈ xs, y ≤ xs.foldl max z := by
    induction xs generalizing z with
    | nil => simp
    | cons b bs ih =>
      have hb := ih (max z b)
      refine ⟨(le_max_left z b).trans hb.1,?_⟩
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact (le_max_right z y).trans hb.1
      · exact hb.2 y hy
  refine ⟨max e S,?_⟩
  intro n hn
  have hen : e ≤ n := (le_max_left e S).trans hn
  have hSn : S ≤ n := (le_max_right e S).trans hn
  have hvalue := selected_total_value a ha n e (f n) hen
    (fun r hr => hS1 r (hSn.trans hr)) (congrFun he n)
  have hmem : candidateValue a ha n e ∈ (List.range (n+1)).map (candidateValue a ha n) :=
    List.mem_map.mpr ⟨e,List.mem_range.mpr (by omega),rfl⟩
  have hbound := (fold_bounds ((List.range (n+1)).map (candidateValue a ha n)) 0).2 _ hmem
  rw [hvalue] at hbound
  unfold dominatingFunction
  omega

theorem high_computes_dominating (A : Set ℕ) (hA : High A) :
    ∃ g : ℕ → ℕ, PartialComputable A (fun n => Part.some (g n)) ∧ DominatesComputable g := by
  obtain ⟨a,c,ha,hc⟩ := high_totality_approximation A hA
  refine ⟨dominatingFunction a ha,?_,?_⟩
  · refine ⟨decodeCode (dominatingCompiler c),funext ?_⟩
    intro n
    exact dominating_compiler_eval A c a ha hc n
  · intro f hf
    obtain ⟨N,hN⟩ := maximum_strictly_dominates a ha f hf
    exact Filter.eventually_atTop.mpr ⟨N,fun n hn => (hN n hn).le⟩

end
end Lemmatheca.ComputabilityTheory.HighDegreesAndDomination
