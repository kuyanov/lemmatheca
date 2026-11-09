import Lemmatheca.IndicesOfComputableEnumerableSets.Tagged
import Lemmatheca.OracleProgramNumberings.Parameters
import Lemmatheca.TuringDegrees.Reductions

/-! A fixed finite-query prefix test, its least-stage search, and the specified decoder. -/
namespace Lemmatheca.ComputabilityTheory.ComputableDomainIndices
open UniversalComputation EffectiveEnumerations

set_option backward.isDefEq.respectTransparency false

def Certificate (O : Set ℕ) (g : ℕ → ℕ → ℕ) (hg : Primrec₂ g) (x y s : ℕ) : Prop :=
  ∀ i ≤ y, ThirdLevelIndexSets.marker (taggedStages g hg x s) i ∉ O

/-- Ordinary numerical code choice is made independently of every oracle. -/
private noncomputable def ordinaryCode {f : ℕ → ℕ} (hf : Primrec f) : Nat.Partrec.Code :=
  Classical.choose (Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp hf.to_comp.partrec))

private theorem ordinaryCode_eval {f : ℕ → ℕ} (hf : Primrec f) (w : ℕ) :
    Nat.Partrec.Code.eval (ordinaryCode hf) w = Part.some (f w) := by
  exact congrFun (Classical.choose_spec
    (Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp hf.to_comp.partrec))) w

/-- A primitive-recursion step receives <<x,s>,<i,previous>>. -/
noncomputable def markerQueryInput (g : ℕ → ℕ → ℕ) (hg : Primrec₂ g) (w : ℕ) : ℕ :=
  ThirdLevelIndexSets.marker (taggedStages g hg w.unpair.1.unpair.1 w.unpair.1.unpair.2)
    w.unpair.2.unpair.1

theorem markerQueryInput_primitive (g : ℕ → ℕ → ℕ) (hg : Primrec₂ g) :
    Primrec (markerQueryInput g hg) := by
  have hu : Primrec (fun w : ℕ => w.unpair.1) := Primrec.fst.comp Primrec.unpair
  have hv : Primrec (fun w : ℕ => w.unpair.2) := Primrec.snd.comp Primrec.unpair
  exact ThirdLevelIndexSets.marker_primitive.comp
    ((ThirdLevelIndexSets.stages_primitive (taggedSchedule g hg)).comp
      (hu.comp hu) (hv.comp hu)) (hu.comp hv)

private noncomputable def maximumCode : Nat.Partrec.Code := ordinaryCode
  (Primrec.nat_max.comp (Primrec.fst.comp Primrec.unpair) (Primrec.snd.comp Primrec.unpair))

/-- Preserve any earlier positive answer and query the next current marker. -/
noncomputable def prefixStepCode (g : ℕ → ℕ → ℕ) (hg : Primrec₂ g) : OracleComputation.Code :=
  .comp (OracleComputation.embed maximumCode)
    (.pair (.comp .right .right)
      (.comp .query (OracleComputation.embed (ordinaryCode (markerQueryInput_primitive g hg)))))

noncomputable def prefixLoopCode (g : ℕ → ℕ → ℕ) (hg : Primrec₂ g) : OracleComputation.Code :=
  .prec .zero (prefixStepCode g hg)

noncomputable def prefixFailure (O : Set ℕ) (g : ℕ → ℕ → ℕ) (hg : Primrec₂ g)
    (x s : ℕ) : ℕ → ℕ
  | 0 => 0
  | n+1 => max (prefixFailure O g hg x s n)
      (indicator (fun z => z ∈ O) (ThirdLevelIndexSets.marker (taggedStages g hg x s) n))

private theorem prefix_step_eval (O : Set ℕ) (g : ℕ → ℕ → ℕ) (hg : Primrec₂ g)
    (x s n v : ℕ) :
    OracleComputation.eval O (prefixStepCode g hg)
        (Nat.pair (Nat.pair x s) (Nat.pair n v)) =
      Part.some (max v (indicator (fun z => z ∈ O)
        (ThirdLevelIndexSets.marker (taggedStages g hg x s) n))) := by
  simp [prefixStepCode, OracleComputation.eval, OracleComputation.eval_embed,
    ordinaryCode_eval, maximumCode, markerQueryInput]

theorem prefix_loop_eval (O : Set ℕ) (g : ℕ → ℕ → ℕ) (hg : Primrec₂ g)
    (x s n : ℕ) :
    OracleComputation.eval O (prefixLoopCode g hg) (Nat.pair (Nat.pair x s) n) =
      Part.some (prefixFailure O g hg x s n) := by
  induction n with
  | zero => simp [prefixLoopCode, OracleComputation.eval, prefixFailure]
  | succ n ih =>
    change OracleComputation.eval O (.prec .zero (prefixStepCode g hg))
      (Nat.pair (Nat.pair x s) (n+1)) = _
    rw [OracleComputation.eval_prec_succ]
    change (OracleComputation.eval O (prefixLoopCode g hg)
      (Nat.pair (Nat.pair x s) n)).bind _ = _
    rw [ih, Part.bind_some, prefix_step_eval]
    rfl

/-- Move <<x,y>,s> to the loop input <<x,s>,y+1>. -/
def certificateInput (w : ℕ) : ℕ :=
  Nat.pair (Nat.pair w.unpair.1.unpair.1 w.unpair.2) (w.unpair.1.unpair.2 + 1)

theorem certificateInput_primitive : Primrec certificateInput := by
  have hu : Primrec (fun w : ℕ => w.unpair.1) := Primrec.fst.comp Primrec.unpair
  have hv : Primrec (fun w : ℕ => w.unpair.2) := Primrec.snd.comp Primrec.unpair
  exact Primrec₂.natPair.comp (Primrec₂.natPair.comp (hu.comp hu) hv)
    (Primrec.succ.comp (hv.comp hu))

noncomputable def certificateCode (g : ℕ → ℕ → ℕ) (hg : Primrec₂ g) : OracleComputation.Code :=
  .comp (prefixLoopCode g hg) (OracleComputation.embed (ordinaryCode certificateInput_primitive))

private theorem prefix_failure_bound (O : Set ℕ) (g : ℕ → ℕ → ℕ) (hg : Primrec₂ g)
    (x s n : ℕ) : prefixFailure O g hg x s n ≤ 1 := by
  induction n with
  | zero => simp [prefixFailure]
  | succ n ih =>
    apply max_le ih
    unfold indicator
    split <;> omega

private theorem prefix_failure_zero (O : Set ℕ) (g : ℕ → ℕ → ℕ) (hg : Primrec₂ g)
    (x s n : ℕ) :
    prefixFailure O g hg x s n = 0 ↔
      ∀ i < n, ThirdLevelIndexSets.marker (taggedStages g hg x s) i ∉ O := by
  induction n with
  | zero => simp [prefixFailure]
  | succ n ih =>
    constructor
    · intro h i hi
      change max (prefixFailure O g hg x s n)
        (indicator (fun z => z ∈ O) (ThirdLevelIndexSets.marker (taggedStages g hg x s) n)) = 0 at h
      by_cases hin : i < n
      · have hp : prefixFailure O g hg x s n = 0 := by
          have hb := le_max_left (prefixFailure O g hg x s n)
            (indicator (fun z => z ∈ O) (ThirdLevelIndexSets.marker (taggedStages g hg x s) n))
          omega
        exact ih.mp hp i hin
      · have he : i = n := by omega
        subst i
        intro hm
        have hb := le_max_right (prefixFailure O g hg x s n)
          (indicator (fun z => z ∈ O) (ThirdLevelIndexSets.marker (taggedStages g hg x s) n))
        have hz : indicator (fun z => z ∈ O)
            (ThirdLevelIndexSets.marker (taggedStages g hg x s) n) = 0 := by omega
        simp [indicator, hm] at hz
    · intro h
      have hp := ih.mpr (fun i hi => h i (by omega))
      have hn := h n (by omega)
      simp [prefixFailure, hp, indicator, hn]

theorem certificate_eval (O : Set ℕ) (g : ℕ → ℕ → ℕ) (hg : Primrec₂ g)
    (x y s : ℕ) :
    OracleComputation.eval O (certificateCode g hg) (Nat.pair (Nat.pair x y) s) =
      Part.some (if @decide (Certificate O g hg x y s) (Classical.propDecidable _) then 0 else 1) := by
  classical
  rw [certificateCode, OracleComputation.eval, OracleComputation.eval_embed,
    ordinaryCode_eval, Part.bind_some]
  simp only [certificateInput, Nat.unpair_pair]
  rw [prefix_loop_eval]
  congr 1
  by_cases hc : Certificate O g hg x y s
  · have hz := (prefix_failure_zero O g hg x s (y+1)).mpr (fun i hi => hc i (by omega))
    simp [hc, hz]
  · have hn : prefixFailure O g hg x s (y+1) ≠ 0 := by
      intro hz
      apply hc
      intro i hi
      exact (prefix_failure_zero O g hg x s (y+1)).mp hz i (by omega)
    have hb := prefix_failure_bound O g hg x s (y+1)
    have he : prefixFailure O g hg x s (y+1) = 1 := by omega
    simp [hc, he]

theorem certificate_permanence (g : ℕ → ℕ → ℕ) (hg : Primrec₂ g) (x y s : ℕ)
    (hcert : Certificate (taggedOutput g hg x) g hg x y s) :
    (∀ t ≥ s, ∀ c, ThirdLevelIndexSets.fresh (taggedSchedule g hg) x t c = true → y < taggedLabel c) ∧
      ∀ t ≥ s, ∀ i ≤ y,
        ThirdLevelIndexSets.marker (taggedStages g hg x t) i = ThirdLevelIndexSets.marker (taggedStages g hg x s) i := by
  have hstable := ThirdLevelIndexSets.certified_prefix_stable (taggedSchedule g hg) x y s hcert
  refine ⟨?_,hstable⟩
  intro t ht c hf
  by_contra hn
  have hc : taggedLabel c ≤ y := by omega
  have hm := ThirdLevelIndexSets.fresh_label_strict (taggedSchedule g hg) x t c hf
  have he0 := hstable t ht (taggedLabel c) hc
  have he1 := hstable (t+1) (by omega) (taggedLabel c) hc
  change ThirdLevelIndexSets.marker (taggedStages g hg x t) (taggedLabel c) <
    ThirdLevelIndexSets.marker (taggedStages g hg x (t+1)) (taggedLabel c) at hm
  rw [he0,he1] at hm
  omega

noncomputable def certificateSearchCode (g : ℕ → ℕ → ℕ) (hg : Primrec₂ g) : OracleComputation.Code :=
  .comp (.find' (certificateCode g hg)) (.pair OracleProgramNumberings.identityCode .zero)

private theorem certificate_search_eval (O : Set ℕ) (g : ℕ → ℕ → ℕ) (hg : Primrec₂ g)
    (x y : ℕ) :
    OracleComputation.eval O (certificateSearchCode g hg) (Nat.pair x y) =
      Nat.rfind (fun s => Part.some (@decide (Certificate O g hg x y s)
        (Classical.propDecidable _))) := by
  classical
  simp only [certificateSearchCode, OracleComputation.eval,
    OracleProgramNumberings.identity_eval, Part.map_some, Part.bind_some,
    Nat.unpair_pair, Nat.add_zero, certificate_eval]
  rw [Part.map_id' (fun _ => rfl)]
  congr 1
  funext s
  by_cases h : Certificate O g hg x y s <;> simp [h]

/-- At <<x,y>,s>, read the exact odd event from the processed cumulative record. -/
noncomputable def replay (g : ℕ → ℕ → ℕ) (w : ℕ) : ℕ :=
  if taggedEvent g w.unpair.1.unpair.1 w.unpair.2 (haltingCode w.unpair.1.unpair.2)
    then 1 else 0

theorem replay_primitive (g : ℕ → ℕ → ℕ) (hg : Primrec₂ g) : Primrec (replay g) := by
  have hu : Primrec (fun w : ℕ => w.unpair.1) := Primrec.fst.comp Primrec.unpair
  have hv : Primrec (fun w : ℕ => w.unpair.2) := Primrec.snd.comp Primrec.unpair
  have he : Primrec (fun w : ℕ =>
      taggedEvent g w.unpair.1.unpair.1 w.unpair.2 (haltingCode w.unpair.1.unpair.2)) :=
    (taggedEvent_primitive g hg).comp (((hu.comp hu).pair hv).pair
      (haltingCode_primitive.comp (hv.comp hu)))
  exact (Primrec.ite (Primrec.eq.comp he (Primrec.const true))
    (Primrec.const 1) (Primrec.const 0)).of_eq (fun _ => rfl)

noncomputable def decoderJointCode (g : ℕ → ℕ → ℕ) (hg : Primrec₂ g) : OracleComputation.Code :=
  .comp (OracleComputation.embed (ordinaryCode (replay_primitive g hg)))
    (.pair OracleProgramNumberings.identityCode (certificateSearchCode g hg))

/-- This fixed code inserts x into the joint program before its runtime input y. -/
noncomputable def decoderCode (g : ℕ → ℕ → ℕ) (hg : Primrec₂ g) (x : ℕ) : OracleComputation.Code :=
  .comp (decoderJointCode g hg) (.pair (OracleProgramNumberings.constantCode x) OracleProgramNumberings.identityCode)

noncomputable def decoderPartial (O : Set ℕ) (g : ℕ → ℕ → ℕ) (hg : Primrec₂ g)
    (x y : ℕ) : Part ℕ :=
  (Nat.rfind (fun s => Part.some (@decide (Certificate O g hg x y s)
    (Classical.propDecidable _)))).map
    (fun s => replay g (Nat.pair (Nat.pair x y) s))

theorem decoder_eval (O : Set ℕ) (g : ℕ → ℕ → ℕ) (hg : Primrec₂ g) (x y : ℕ) :
    OracleComputation.eval O (decoderCode g hg x) y = decoderPartial O g hg x y := by
  classical
  have hin : OracleComputation.eval O
      (.pair (OracleProgramNumberings.constantCode x) OracleProgramNumberings.identityCode) y =
      Part.some (Nat.pair x y) := by
    simp [OracleComputation.eval, OracleProgramNumberings.constant_eval,
      OracleProgramNumberings.identity_eval]
  rw [decoderCode, OracleComputation.eval, hin, Part.bind_some,
    decoderJointCode, OracleComputation.eval]
  have hp : OracleComputation.eval O
      (.pair OracleProgramNumberings.identityCode (certificateSearchCode g hg)) (Nat.pair x y) =
      (Nat.rfind (fun s => Part.some (@decide (Certificate O g hg x y s)
        (Classical.propDecidable _)))).map (Nat.pair (Nat.pair x y)) := by
    rw [OracleComputation.eval, OracleProgramNumberings.identity_eval, Part.bind_some,
      certificate_search_eval]
  rw [hp, Part.bind_map]
  simp only [OracleComputation.eval_embed, ordinaryCode_eval, Part.bind_some_eq_map]
  rfl

theorem certificate_exists (g : ℕ → ℕ → ℕ) (hg : Primrec₂ g) (x y : ℕ)
    (hrows : ∀ i, (indexSet (g x i)).Finite) :
    ∃ s, Certificate (taggedOutput g hg x) g hg x y s := by
  obtain ⟨s,_,hs⟩ := tagged_prefix_stabilization g hg x y hrows
  exact ⟨s,hs⟩

theorem decoder_correct (g : ℕ → ℕ → ℕ) (hg : Primrec₂ g) (x : ℕ)
    (hrows : ∀ i, (indexSet (g x i)).Finite) (y : ℕ) :
    OracleComputation.eval (taggedOutput g hg x) (decoderCode g hg x) y =
      Part.some (indicator (fun i => i ∈ haltingDiagonal) y) := by
  classical
  rw [decoder_eval]
  obtain hex : ∃ s, Certificate (taggedOutput g hg x) g hg x y s :=
    certificate_exists g hg x y hrows
  let S := Nat.find hex
  have hS : Certificate (taggedOutput g hg x) g hg x y S := Nat.find_spec hex
  have hfound : S ∈ Nat.rfind (fun s => Part.some
      (@decide (Certificate (taggedOutput g hg x) g hg x y s) (Classical.propDecidable _))) := by
    rw [Nat.mem_rfind]
    constructor
    · simpa using hS
    · intro t ht
      have hn : ¬ Certificate (taggedOutput g hg x) g hg x y t := Nat.find_min hex ht
      simpa using hn
  apply Part.eq_some_iff.mpr
  rw [decoderPartial, Part.mem_map_iff]
  refine ⟨S,hfound,?_⟩
  by_cases hy : y ∈ haltingDiagonal
  · have hevent := (tagged_halting_union g hg x y).mpr hy
    obtain ⟨t,ht,_⟩ := (ThirdLevelIndexSets.event_once (taggedSchedule g hg) x (haltingCode y)).mp hevent
    have htS : t < S := by
      by_contra hn
      have hl := (certificate_permanence g hg x y S hS).1 t (by omega) (haltingCode y) ht
      rw [(tagged_codes y 0).2.1] at hl
      omega
    have hseen := (tagged_processed_through_stage g hg x S (haltingCode y)).mpr ⟨t,htS,ht⟩
    simp [replay, Nat.unpair_pair, hseen, indicator, hy]
  · have hseen : taggedEvent g x S (haltingCode y) ≠ true := by
      intro ht
      exact hy ((tagged_halting_union g hg x y).mp ⟨S,ht⟩)
    simp [replay, Nat.unpair_pair, hseen, indicator, hy]

theorem decoder_reduces (g : ℕ → ℕ → ℕ) (hg : Primrec₂ g) (x : ℕ)
    (hrows : ∀ i, (indexSet (g x i)).Finite) :
    TuringDegrees.Reduces (decoderCode g hg x) haltingDiagonal (taggedOutput g hg x) := by
  exact decoder_correct g hg x hrows

end Lemmatheca.ComputabilityTheory.ComputableDomainIndices
