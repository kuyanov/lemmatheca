import Lemmatheca.BusyBeaverFunctions.Growth
import Lemmatheca.BusyBeaverFunctions.FunctionOracles

/-! Actual ordinary compilers and Boolean-query programs in both directions of
Busy Beaver/halting equivalence. -/
namespace Lemmatheca.ComputabilityTheory.BusyBeaverFunctions

open Encodable Denumerable
open UniversalComputation OracleComputation TuringDegrees
open Classical

set_option backward.isDefEq.respectTransparency false

noncomputable section

/-- Freeze a numerical input using the specified binary constant compiler. -/
def freezeIndex (e x : ℕ) : ℕ :=
  encode (Nat.Partrec.Code.comp (ofNat Nat.Partrec.Code e) (binaryConstant x))

theorem freezeIndex_computable : Computable₂ freezeIndex := by
  exact Primrec.encode.to_comp.comp
    (Nat.Partrec.Code.primrec₂_comp.to_comp.comp
      ((Computable.ofNat Nat.Partrec.Code).comp Computable.fst)
      (binaryConstant_computable.comp Computable.snd))

theorem freezeIndex_eval (e x z : ℕ) : phi (freezeIndex e x) z = phi e x := by
  simp only [phi, freezeIndex, ofNat_encode, Nat.Partrec.Code.eval,
    binaryConstant_eval, Part.bind_eq_bind, Part.bind_some]

theorem freezeIndex_halting (e x : ℕ) :
    freezeIndex e x ∈ haltingDiagonal ↔ (phi e x).Dom := by
  change (phi (freezeIndex e x) (freezeIndex e x)).Dom ↔ _
  rw [freezeIndex_eval]

def candidateLength (n : ℕ) : ℕ := (contestants n).length

def candidateAt (n i : ℕ) : ℕ :=
  encode (((contestants n)[i]?).getD Nat.Partrec.Code.zero)

theorem candidateLength_computable : Computable candidateLength := by
  exact Computable.list_length.comp contestants_computable

theorem candidateAt_computable : Computable₂ candidateAt := by
  exact Primrec.encode.to_comp.comp
    (Primrec.option_getD.to_comp.comp
      (Computable.list_getElem?.comp (contestants_computable.comp Computable.fst) Computable.snd)
      (Computable.const Nat.Partrec.Code.zero))

/-- The primitive-recursion step input is the pair of n with the pair of i and the old state. -/
def maximaQueryInput (z : ℕ) : ℕ := freezeIndex (candidateAt z.unpair.1 z.unpair.2.unpair.1) 0

private theorem left_computable : Computable (fun z : ℕ => z.unpair.1) :=
  Computable.fst.comp Computable.unpair

private theorem right_computable : Computable (fun z : ℕ => z.unpair.2) :=
  Computable.snd.comp Computable.unpair

private theorem candidate_selector_computable :
    Computable (fun z : ℕ => candidateAt z.unpair.1 z.unpair.2.unpair.1) :=
  candidateAt_computable.comp left_computable (left_computable.comp right_computable)

private theorem bounded_computable {α : Type*} [Primcodable α]
    {k e x : α → ℕ} (hk : Computable k) (he : Computable e) (hx : Computable x) :
    Computable (fun a => boundedValue (k a) (e a) (x a)) :=
  boundedValue_primitive.to_comp.comp ((hk.pair he).pair hx)

private theorem positive_bit_computable {α : Type*} [Primcodable α]
    {f : α → ℕ} (hf : Computable f) : Computable (fun a => if 0 < f a then 1 else 0) := by
  have hp := Primrec.nat_lt.decide.to_comp.comp (Computable.const 0) hf
  apply ((Primrec.dom_bool (fun b => if b then 1 else 0)).to_comp.comp hp).of_eq
  intro a
  by_cases h : 0 < f a <;> simp [h]

theorem maximaQueryInput_computable : Computable maximaQueryInput := by
  exact freezeIndex_computable.comp candidate_selector_computable (Computable.const 0)

/-- The positive branch searches the ordinary computation and updates both maxima. -/
def positiveStep (z : ℕ) : Part ℕ :=
  let e := candidateAt z.unpair.1 z.unpair.2.unpair.1
  let acc := z.unpair.2.unpair.2
  (leastResource e 0).map (fun k =>
    Nat.pair (max acc.unpair.1 (boundedValue k e 0 - 1)) (max acc.unpair.2 k))

theorem positiveStep_partrec : Nat.Partrec positiveStep := by
  have he := candidate_selector_computable
  have ha : Computable (fun z : ℕ => z.unpair.2.unpair.2) := right_computable.comp right_computable
  have hbase : Partrec (fun z : ℕ => leastResource z.unpair.1 z.unpair.2) :=
    Partrec.nat_iff.mpr leastResource_partrec
  have hinput : Computable (fun z : ℕ => Nat.pair (candidateAt z.unpair.1 z.unpair.2.unpair.1) 0) :=
    Primrec₂.natPair.to_comp.comp he (Computable.const 0)
  have hl : Partrec (fun z : ℕ => leastResource (candidateAt z.unpair.1 z.unpair.2.unpair.1) 0) :=
    (hbase.comp hinput).of_eq (fun z => by simp)
  have hv : Computable (fun p : ℕ × ℕ =>
      boundedValue p.2 (candidateAt p.1.unpair.1 p.1.unpair.2.unpair.1) 0 - 1) :=
    Primrec.nat_sub.to_comp.comp
      (bounded_computable Computable.snd (he.comp Computable.fst) (Computable.const 0))
      (Computable.const 1)
  have hb := Primrec.nat_max.to_comp.comp (left_computable.comp (ha.comp Computable.fst)) hv
  have hs := Primrec.nat_max.to_comp.comp (right_computable.comp (ha.comp Computable.fst)) Computable.snd
  exact Partrec.nat_iff.mp (hl.map (Primrec₂.natPair.to_comp.comp hb hs).to₂)

def positiveCode : Nat.Partrec.Code :=
  Classical.choose (Nat.Partrec.Code.exists_code.mp positiveStep_partrec)

theorem positiveCode_eval (z : ℕ) : Nat.Partrec.Code.eval positiveCode z = positiveStep z := by
  exact congrFun (Classical.choose_spec (Nat.Partrec.Code.exists_code.mp positiveStep_partrec)) z

/-- Recursion at the queried bit makes the divergent search a lazy positive branch. -/
def maximaBranch : OracleComputation.Code :=
  .comp (.prec (.comp .right .right) (.comp (embed positiveCode) .left))
    (.pair (.pair .left .right)
      (.comp .query (embed (ordinaryProgram maximaQueryInput maximaQueryInput_computable))))

/-- One fixed program scans the finite contestant list and returns the paired maxima. -/
def maximaCode : OracleComputation.Code :=
  .comp (.prec .zero maximaBranch)
    (.pair (.pair .left .right)
      (embed (ordinaryProgram candidateLength candidateLength_computable)))

def maximaFold (A : Set ℕ) (n : ℕ) : ℕ → Part ℕ := by
  classical
  exact Nat.rec (Part.some 0) (fun i previous =>
    previous.bind (fun acc =>
      if freezeIndex (candidateAt n i) 0 ∈ A then
        positiveStep (Nat.pair n (Nat.pair i acc))
      else Part.some acc))

theorem maximaBranch_eval (A : Set ℕ) (n i acc : ℕ) :
    eval A maximaBranch (Nat.pair n (Nat.pair i acc)) =
      if freezeIndex (candidateAt n i) 0 ∈ A then
        positiveStep (Nat.pair n (Nat.pair i acc))
      else Part.some acc := by
  by_cases h : freezeIndex (candidateAt n i) 0 ∈ A
  all_goals
    simp [maximaBranch, eval, eval_embed, ordinaryProgram_eval, maximaQueryInput,
      indicator, h, positiveCode_eval]

theorem maximaCode_eval (A : Set ℕ) (n : ℕ) :
    eval A maximaCode n = maximaFold A n (candidateLength n) := by
  have hr : ∀ t, eval A (.prec .zero maximaBranch) (Nat.pair n t) = maximaFold A n t := by
    intro t
    induction t with
    | zero => rw [eval_prec_zero]; rfl
    | succ t ih =>
      rw [eval_prec_succ, ih]
      change (maximaFold A n t).bind (fun acc =>
        eval A maximaBranch (Nat.pair n (Nat.pair t acc))) =
        (maximaFold A n t).bind (fun acc =>
          if freezeIndex (candidateAt n t) 0 ∈ A then
            positiveStep (Nat.pair n (Nat.pair t acc)) else Part.some acc)
      apply congrArg (Part.bind (maximaFold A n t))
      funext acc
      exact maximaBranch_eval A n t acc
  have hi : eval A (.pair (.pair .left .right)
      (embed (ordinaryProgram candidateLength candidateLength_computable))) n =
      Part.some (Nat.pair n (candidateLength n)) := by
    simp [eval, eval_embed, ordinaryProgram_eval]
  change (eval A (.pair (.pair .left .right)
    (embed (ordinaryProgram candidateLength candidateLength_computable))) n).bind
    (eval A (.prec .zero maximaBranch)) = _
  rw [hi, Part.bind_some, hr]

private theorem halting_step_correct (n i acc : ℕ) (hi : i < (contestants n).length) :
    (if freezeIndex (candidateAt n i) 0 ∈ haltingDiagonal then
      positiveStep (Nat.pair n (Nat.pair i acc)) else Part.some acc) =
      Part.some (Nat.pair
        (max acc.unpair.1 (zeroDefault (Nat.Partrec.Code.eval ((contestants n)[i]) 0)))
        (max acc.unpair.2 (zeroDefault (leastResource (encode ((contestants n)[i])) 0)))) := by
  let c := (contestants n)[i]
  have he : candidateAt n i = encode c := by
    simp [candidateAt, List.getElem?_eq_getElem hi, c]
  have hf : freezeIndex (candidateAt n i) 0 ∈ haltingDiagonal ↔
      (Nat.Partrec.Code.eval c 0).Dom := by
    rw [he, freezeIndex_halting]
    simp [phi]
  by_cases hd : (Nat.Partrec.Code.eval c 0).Dom
  · obtain ⟨y, hy⟩ := Part.dom_iff_mem.mp hd
    have hyphi : y ∈ phi (encode c) 0 := by simpa [phi] using hy
    obtain ⟨k, hk⟩ := Part.dom_iff_mem.mp ((leastResource_domain (encode c) 0).mpr hyphi.1)
    have hv := certificate_value ((leastResource_spec _ _ _).mp hk).1 hyphi
    have hl : leastResource (encode c) 0 = Part.some k := Part.eq_some_iff.mpr hk
    rw [ite_eq_left (hf.mpr hd)]
    simp [positiveStep, he, hl, hv, zeroDefault_value hy, zeroDefault_value (Part.mem_some k), c]
  · have hphi : ¬ (phi (encode c) 0).Dom := by simpa [phi] using hd
    have hl : ¬ (leastResource (encode c) 0).Dom := fun h => hphi ((leastResource_domain _ _).mp h)
    rw [ite_eq_right (fun h => hd (hf.mp h))]
    simp [zeroDefault, hd, hl, c]

private def prefixPair (cs : List Nat.Partrec.Code) : ℕ :=
  Nat.pair ((cs.map (fun c => zeroDefault (Nat.Partrec.Code.eval c 0))).foldl max 0)
    ((cs.map (fun c => zeroDefault (leastResource (encode c) 0))).foldl max 0)

private theorem prefixPair_append (cs : List Nat.Partrec.Code) (c : Nat.Partrec.Code) :
    prefixPair (cs ++ [c]) = Nat.pair
      (max (prefixPair cs).unpair.1 (zeroDefault (Nat.Partrec.Code.eval c 0)))
      (max (prefixPair cs).unpair.2 (zeroDefault (leastResource (encode c) 0))) := by
  simp [prefixPair, List.foldl_append]

private theorem maximaFold_halting_prefix (n : ℕ) : ∀ t, t ≤ candidateLength n →
    maximaFold haltingDiagonal n t = Part.some (prefixPair ((contestants n).take t)) := by
  intro t
  induction t with
  | zero => intro _; rfl
  | succ t ih =>
    intro ht
    have hit : t < (contestants n).length := by change t + 1 ≤ (contestants n).length at ht; omega
    change (maximaFold haltingDiagonal n t).bind (fun acc =>
      if freezeIndex (candidateAt n t) 0 ∈ haltingDiagonal then
        positiveStep (Nat.pair n (Nat.pair t acc)) else Part.some acc) = _
    rw [ih (by change t ≤ (contestants n).length; omega), Part.bind_some,
      halting_step_correct n t _ hit, List.take_succ_eq_append_getElem hit, prefixPair_append]

theorem maximaCode_halting (n : ℕ) :
    eval haltingDiagonal maximaCode n = Part.some (Nat.pair (outputMaximum n) (resourceMaximum n)) := by
  rw [maximaCode_eval]
  simpa [candidateLength, prefixPair, outputMaximum, resourceMaximum] using
    maximaFold_halting_prefix n (candidateLength n) le_rfl

def outputCode : OracleComputation.Code := .comp .left maximaCode

def resourceCode : OracleComputation.Code := .comp .right maximaCode

theorem outputCode_eval (n : ℕ) :
    eval haltingDiagonal outputCode n = Part.some (outputMaximum n) := by
  simp [outputCode, eval, maximaCode_halting]

theorem resourceCode_eval (n : ℕ) :
    eval haltingDiagonal resourceCode n = Part.some (resourceMaximum n) := by
  simp [resourceCode, eval, maximaCode_halting]

/-- These are the ordinary preprocessing and final Boolean test for the resource reduction. -/
def resourceBudget (p : ℕ) : ℕ :=
  nodeSize (ofNat Nat.Partrec.Code (freezeIndex p.unpair.1 p.unpair.2))

def resourceDecision (z : ℕ) : ℕ :=
  if 0 < boundedValue z.unpair.2 (freezeIndex z.unpair.1.unpair.1 z.unpair.1.unpair.2) 0 then 1 else 0

theorem resourceBudget_computable : Computable resourceBudget := by
  exact nodeSize_computable.comp
    ((Computable.ofNat Nat.Partrec.Code).comp
      (freezeIndex_computable.comp left_computable right_computable))

theorem resourceDecision_computable : Computable resourceDecision := by
  exact positive_bit_computable (bounded_computable right_computable
    (freezeIndex_computable.comp (left_computable.comp left_computable)
      (right_computable.comp left_computable)) (Computable.const 0))

def resourceBoundPairCode : OracleComputation.Code :=
  .comp (embed (ordinaryProgram resourceDecision resourceDecision_computable))
    (.pair (.pair .left .right)
      (.comp graphLookup (embed (ordinaryProgram resourceBudget resourceBudget_computable))))

theorem resourceBoundPairCode_eval (h : ℕ → ℕ) (hh : ∀ n, resourceMaximum n ≤ h n) :
    Reduces resourceBoundPairCode haltingPairs (graph h) := by
  intro p
  have hev : eval (graph h) resourceBoundPairCode p =
      Part.some (resourceDecision (Nat.pair p (h (resourceBudget p)))) := by
    simp [resourceBoundPairCode, eval, eval_embed, ordinaryProgram_eval, graphLookup_eval]
  have hiff : 0 < boundedValue (h (resourceBudget p)) (freezeIndex p.unpair.1 p.unpair.2) 0 ↔
      (phi p.unpair.1 p.unpair.2).Dom := by
    constructor
    · intro hc
      have hd := (phi_domain (freezeIndex p.unpair.1 p.unpair.2) 0).mpr
        ⟨h (resourceBudget p), hc⟩
      simpa only [freezeIndex_eval] using hd
    · intro hd
      obtain ⟨y, hy⟩ := Part.dom_iff_mem.mp hd
      let c := ofNat Nat.Partrec.Code (freezeIndex p.unpair.1 p.unpair.2)
      have hcf : y ∈ Nat.Partrec.Code.eval c 0 := by
        change y ∈ phi (freezeIndex p.unpair.1 p.unpair.2) 0
        rw [freezeIndex_eval]
        exact hy
      obtain ⟨_, _, _, _, hb⟩ := contestant_bounds c (resourceBudget p) y le_rfl hcf
      have hv := bounded_value_persists (e := encode c) (x := 0) (hh (resourceBudget p)) hb
      have hv' : boundedValue (h (resourceBudget p)) (freezeIndex p.unpair.1 p.unpair.2) 0 = y + 1 := by
        simpa [c] using hv
      omega
  rw [hev]
  by_cases hd : (phi p.unpair.1 p.unpair.2).Dom
  · have hc := hiff.mpr hd
    simp [resourceDecision, indicator, haltingPairs, hd, hc]
  · have hc : ¬ 0 < boundedValue (h (resourceBudget p)) (freezeIndex p.unpair.1 p.unpair.2) 0 :=
      fun hc => hd (hiff.mp hc)
    simp [resourceDecision, indicator, haltingPairs, hd, hc]

def resourceBoundCode : OracleComputation.Code :=
  .comp resourceBoundPairCode (embed (.pair Nat.Partrec.Code.id Nat.Partrec.Code.id))

theorem resourceBoundCode_eval (h : ℕ → ℕ) (hh : ∀ n, resourceMaximum n ≤ h n) :
    Reduces resourceBoundCode haltingDiagonal (graph h) := by
  intro e
  have hd : Nat.Partrec.Code.eval (.pair Nat.Partrec.Code.id Nat.Partrec.Code.id) e =
      Part.some (Nat.pair e e) := by
    change Nat.pair <$> Nat.Partrec.Code.eval Nat.Partrec.Code.id e <*>
      Nat.Partrec.Code.eval Nat.Partrec.Code.id e = _
    rw [Nat.Partrec.Code.eval_id]
    simp [Seq.seq]
  change (eval (graph h) (embed (.pair Nat.Partrec.Code.id Nat.Partrec.Code.id)) e).bind
    (eval (graph h) resourceBoundPairCode) = _
  rw [eval_embed, hd, Part.bind_some, resourceBoundPairCode_eval h hh (Nat.pair e e)]
  simp [indicator, haltingPairs, haltingDiagonal]

/-- The one ordinary program below searches a resource witness for paired e,x. -/
def witnessCode : Nat.Partrec.Code :=
  Classical.choose (Nat.Partrec.Code.exists_code.mp leastResource_partrec)

def witnessIndex (e x : ℕ) : ℕ :=
  encode (Nat.Partrec.Code.comp witnessCode (binaryConstant (Nat.pair e x)))

theorem witnessIndex_computable : Computable₂ witnessIndex := by
  exact Primrec.encode.to_comp.comp
    (Nat.Partrec.Code.primrec₂_comp.to_comp.comp (Computable.const witnessCode)
      (binaryConstant_computable.comp
        (Primrec₂.natPair.to_comp.comp Computable.fst Computable.snd)))

theorem witnessIndex_eval (e x z : ℕ) : phi (witnessIndex e x) z = leastResource e x := by
  have hr := congrFun (Classical.choose_spec
    (Nat.Partrec.Code.exists_code.mp leastResource_partrec)) (Nat.pair e x)
  simp only [phi, witnessIndex, ofNat_encode, Nat.Partrec.Code.eval,
    binaryConstant_eval, Part.bind_eq_bind, Part.bind_some]
  simpa [witnessCode] using hr

def outputBudget (p : ℕ) : ℕ :=
  nodeSize (ofNat Nat.Partrec.Code (witnessIndex p.unpair.1 p.unpair.2))

def outputDecision (z : ℕ) : ℕ :=
  if 0 < boundedValue z.unpair.2 z.unpair.1.unpair.1 z.unpair.1.unpair.2 then 1 else 0

theorem outputBudget_computable : Computable outputBudget := by
  exact nodeSize_computable.comp
    ((Computable.ofNat Nat.Partrec.Code).comp
      (witnessIndex_computable.comp left_computable right_computable))

theorem outputDecision_computable : Computable outputDecision := by
  exact positive_bit_computable (bounded_computable right_computable
    (left_computable.comp left_computable) (right_computable.comp left_computable))

def outputBoundPairCode : OracleComputation.Code :=
  .comp (embed (ordinaryProgram outputDecision outputDecision_computable))
    (.pair (.pair .left .right)
      (.comp graphLookup (embed (ordinaryProgram outputBudget outputBudget_computable))))

theorem outputBoundPairCode_eval (h : ℕ → ℕ) (hh : ∀ n, outputMaximum n ≤ h n) :
    Reduces outputBoundPairCode haltingPairs (graph h) := by
  intro p
  have hev : eval (graph h) outputBoundPairCode p =
      Part.some (outputDecision (Nat.pair p (h (outputBudget p)))) := by
    simp [outputBoundPairCode, eval, eval_embed, ordinaryProgram_eval, graphLookup_eval]
  have hiff : 0 < boundedValue (h (outputBudget p)) p.unpair.1 p.unpair.2 ↔
      (phi p.unpair.1 p.unpair.2).Dom := by
    constructor
    · intro hc
      exact (phi_domain _ _).mpr ⟨h (outputBudget p), hc⟩
    · intro hd
      obtain ⟨k, hk⟩ := Part.dom_iff_mem.mp ((leastResource_domain _ _).mpr hd)
      let c := ofNat Nat.Partrec.Code (witnessIndex p.unpair.1 p.unpair.2)
      have hkc : k ∈ Nat.Partrec.Code.eval c 0 := by
        change k ∈ phi (witnessIndex p.unpair.1 p.unpair.2) 0
        rw [witnessIndex_eval]
        exact hk
      have hkb := (outputMaximum_le_iff (outputBudget p) (outputMaximum (outputBudget p))).mp
        le_rfl c le_rfl k hkc
      have hkp : 0 < boundedValue k p.unpair.1 p.unpair.2 := ((leastResource_spec _ _ _).mp hk).1
      have hv := bounded_value_persists (e := p.unpair.1) (x := p.unpair.2)
        (y := boundedValue k p.unpair.1 p.unpair.2 - 1)
        (hkb.trans (hh (outputBudget p))) (by omega)
      omega
  rw [hev]
  by_cases hd : (phi p.unpair.1 p.unpair.2).Dom
  · have hc := hiff.mpr hd
    simp [outputDecision, indicator, haltingPairs, hd, hc]
  · have hc : ¬ 0 < boundedValue (h (outputBudget p)) p.unpair.1 p.unpair.2 := fun hc => hd (hiff.mp hc)
    simp [outputDecision, indicator, haltingPairs, hd, hc]

def outputBoundCode : OracleComputation.Code :=
  .comp outputBoundPairCode (embed (.pair Nat.Partrec.Code.id Nat.Partrec.Code.id))

theorem outputBoundCode_eval (h : ℕ → ℕ) (hh : ∀ n, outputMaximum n ≤ h n) :
    Reduces outputBoundCode haltingDiagonal (graph h) := by
  intro e
  have hd : Nat.Partrec.Code.eval (.pair Nat.Partrec.Code.id Nat.Partrec.Code.id) e =
      Part.some (Nat.pair e e) := by
    change Nat.pair <$> Nat.Partrec.Code.eval Nat.Partrec.Code.id e <*>
      Nat.Partrec.Code.eval Nat.Partrec.Code.id e = _
    rw [Nat.Partrec.Code.eval_id]
    simp [Seq.seq]
  change (eval (graph h) (embed (.pair Nat.Partrec.Code.id Nat.Partrec.Code.id)) e).bind
    (eval (graph h) outputBoundPairCode) = _
  rw [eval_embed, hd, Part.bind_some, outputBoundPairCode_eval h hh (Nat.pair e e)]
  simp [indicator, haltingPairs, haltingDiagonal]

theorem halting_equivalence :
    Equivalent (graph outputMaximum) haltingDiagonal ∧
      Equivalent (graph resourceMaximum) haltingDiagonal := by
  have hb : Reducible (graph outputMaximum) haltingDiagonal :=
    (function_computable_iff_graph_reducible haltingDiagonal outputMaximum).mp
      ⟨outputCode, funext outputCode_eval⟩
  have hs : Reducible (graph resourceMaximum) haltingDiagonal :=
    (function_computable_iff_graph_reducible haltingDiagonal resourceMaximum).mp
      ⟨resourceCode, funext resourceCode_eval⟩
  exact ⟨⟨hb, outputBoundCode, outputBoundCode_eval outputMaximum (fun _ => le_rfl)⟩,
    ⟨hs, resourceBoundCode, resourceBoundCode_eval resourceMaximum (fun _ => le_rfl)⟩⟩

theorem no_computable_resource_upper_bound :
    ¬ ∃ g : ℕ → ℕ, Computable g ∧ ∃ N, ∀ n, N ≤ n → resourceMaximum n ≤ g n := by
  rintro ⟨g, hg, N, hN⟩
  have hfinite : ∀ m, ∃ M, ∀ n < m, resourceMaximum n ≤ M := by
    intro m
    induction m with
    | zero => exact ⟨0, fun n hn => by omega⟩
    | succ m ih =>
      obtain ⟨M, hM⟩ := ih
      refine ⟨max M (resourceMaximum m), ?_⟩
      intro n hn
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hn) with hn | rfl
      · exact (hM n hn).trans (le_max_left _ _)
      · exact le_max_right _ _
  obtain ⟨M, hM⟩ := hfinite N
  have hh : ∀ n, resourceMaximum n ≤ max M (g n) := by
    intro n
    by_cases hn : n < N
    · exact (hM n hn).trans (le_max_left _ _)
    · exact (hN n (by omega)).trans (le_max_right _ _)
  have hc : Computable (fun n => max M (g n)) :=
    Primrec.nat_max.to_comp.comp (Computable.const M) hg
  exact haltingDiagonal_undecidable (computable_of_reducible
    ⟨resourceBoundCode, resourceBoundCode_eval _ hh⟩ (computable_graph hc))

end
end Lemmatheca.ComputabilityTheory.BusyBeaverFunctions
