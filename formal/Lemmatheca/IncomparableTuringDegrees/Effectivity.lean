import Lemmatheca.IncomparableTuringDegrees.Construction
import Lemmatheca.IncomparableTuringDegrees.DegreeBounds
import Lemmatheca.TuringJump.Recoding
import Lemmatheca.PostsTheorem.Correspondence

/-! Actual halting queries and relative programs computing the chosen stages. -/
namespace Lemmatheca.ComputabilityTheory.IncomparableTuringDegrees

open OracleComputation OracleProgramNumberings TuringJump UniversalComputation

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

noncomputable section

def searchPartial (p : ℕ) : Part ℕ :=
  Nat.rfind (fun w => Part.some (@decide (Good p w) (Classical.propDecidable _)))

theorem search_recursive : Nat.Partrec searchPartial := by
  classical
  have hc : Computable₂ (fun p w => @decide (Good p w) (Classical.propDecidable _)) :=
    good_primitive.decide.to_comp
  exact Partrec.nat_iff.mp (Partrec.rfind hc.partrec₂)

def searchCode : Nat.Partrec.Code :=
  Classical.choose (Nat.Partrec.Code.exists_code.mp search_recursive)

def searchIndex : ℕ := Encodable.encode searchCode

def testMap (p : ℕ) : ℕ := ordinaryToEmptyJump (ordinaryFreeze searchIndex p)

theorem test_map_primitive : Primrec testMap := by
  exact ordinary_to_empty_primitive.comp
    (ordinary_freeze_primitive.comp (Primrec.const searchIndex) Primrec.id)

def testMapCode : Nat.Partrec.Code :=
  ordinaryCode testMap (Primrec.nat_iff.mp test_map_primitive)

def extensionDecisionCode : Code := .comp .query (embed testMapCode)

def selectorPartial (t : ℕ) : Part ℕ :=
  Nat.rfind (fun w => Part.some (@decide
    ((t.unpair.1 = 0 ∧ w = 0) ∨ Good t.unpair.2 w) (Classical.propDecidable _)))

def extensionPartial (t : ℕ) : Part ℕ :=
  (selectorPartial t).map (fun w => finish t.unpair.1 t.unpair.2 w)

private theorem selector_recursive : Nat.Partrec selectorPartial := by
  classical
  have heq : PrimrecPred (fun z : ℕ × ℕ => z.1.unpair.1 = 0 ∧ z.2 = 0) :=
    (Primrec.eq.comp ((Primrec.fst.comp Primrec.unpair).comp Primrec.fst)
      (Primrec.const 0)).and (Primrec.eq.comp Primrec.snd (Primrec.const 0))
  have hp : Primrec (fun z : ℕ × ℕ => (z.1.unpair.2, z.2)) :=
    ((Primrec.snd.comp Primrec.unpair).comp Primrec.fst).pair Primrec.snd
  have hg := good_primitive.comp hp
  have hc := (heq.or hg).decide.to_comp
  have hh := Partrec.rfind hc.to₂.partrec₂
  apply Partrec.nat_iff.mp
  apply hh.of_eq
  intro t
  unfold selectorPartial
  congr 1
  funext w
  simp

theorem extension_partial_recursive : Nat.Partrec extensionPartial := by
  have hp : Primrec (fun z : ℕ × ℕ => ((z.1.unpair.1, z.1.unpair.2), z.2)) :=
    (((Primrec.fst.comp Primrec.unpair).comp Primrec.fst).pair
      ((Primrec.snd.comp Primrec.unpair).comp Primrec.fst)).pair Primrec.snd
  have hf := finish_primitive.to_comp.comp hp.to_comp
  have hh := (Partrec.nat_iff.mpr selector_recursive).map hf.to₂
  exact Partrec.nat_iff.mp hh

def extensionPartialCode : Nat.Partrec.Code :=
  Classical.choose (Nat.Partrec.Code.exists_code.mp extension_partial_recursive)

def extensionCode : Code :=
  .comp (embed extensionPartialCode) (.pair extensionDecisionCode identityCode)

theorem search_code_eval (p : ℕ) : searchCode.eval p = searchPartial p := by
  exact congrFun (Classical.choose_spec (Nat.Partrec.Code.exists_code.mp search_recursive)) p

theorem search_domain (p : ℕ) : (searchPartial p).Dom ↔ HasExtension p := by
  rw [searchPartial, Nat.rfind_dom]
  simp [HasExtension]

theorem search_least (p : ℕ) (h : HasExtension p) :
    searchPartial p = Part.some (selected p) := by
  apply Part.eq_some_iff.mpr
  apply Nat.mem_rfind.mpr
  refine ⟨?_, ?_⟩
  · simp [(selected_spec p h).1]
  · intro w hw
    simp [(selected_spec p h).2 w hw]

theorem test_map_correct (p : ℕ) : testMap p ∈ jump ∅ ↔ HasExtension p := by
  rw [testMap, ← ordinary_to_empty_membership]
  change (UniversalComputation.phi (ordinaryFreeze searchIndex p)
    (ordinaryFreeze searchIndex p)).Dom ↔ HasExtension p
  rw [ordinary_freeze_eval]
  simp only [UniversalComputation.phi, searchIndex, Denumerable.ofNat_encode]
  rw [search_code_eval, search_domain]

theorem extension_decision_eval (p : ℕ) :
    eval (jump ∅) extensionDecisionCode p = Part.some (indicator HasExtension p) := by
  change (eval (jump ∅) (embed testMapCode) p).bind
    (eval (jump ∅) .query) = _
  rw [eval_embed, testMapCode, ordinaryCode_eval, Part.bind_some]
  classical
  by_cases h : HasExtension p
  · have hm := (test_map_correct p).mpr h
    simp [eval, indicator, h, hm]
  · have hm : testMap p ∉ jump ∅ := fun hm => h ((test_map_correct p).mp hm)
    simp [eval, indicator, h, hm]

theorem extension_partial_eval (p : ℕ) :
    extensionPartial (Nat.pair (indicator HasExtension p) p) =
      Part.some (extendState p) := by
  have hs : selectorPartial (Nat.pair (indicator HasExtension p) p) =
      Part.some (selected p) := by
    classical
    by_cases h : HasExtension p
    · have hb : indicator HasExtension p = 1 := by simp [indicator, h]
      rw [hb]
      have he : selectorPartial (Nat.pair 1 p) = searchPartial p := by
        unfold selectorPartial searchPartial
        congr 1
        funext w
        simp only [Nat.unpair_pair, one_ne_zero, false_and, false_or]
      rw [he, search_least p h]
    · have hb : indicator HasExtension p = 0 := by simp [indicator, h]
      have hw : selected p = 0 := by simp [selected, h]
      rw [hb, hw]
      apply Part.eq_some_iff.mpr
      apply Nat.mem_rfind.mpr
      refine ⟨by simp, ?_⟩
      intro w hw
      omega
  rw [extensionPartial, hs, Part.map_some]
  simp only [Nat.unpair_pair, extendState]

theorem extension_code_eval (p : ℕ) :
    eval (jump ∅) extensionCode p = Part.some (extendState p) := by
  have hp : eval (jump ∅) (.pair extensionDecisionCode identityCode) p =
      Part.some (Nat.pair (indicator HasExtension p) p) := by
    simp only [eval, extension_decision_eval, identity_eval, Part.bind_some, Part.map_some]
  change (eval (jump ∅) (.pair extensionDecisionCode identityCode) p).bind
    (eval (jump ∅) (embed extensionPartialCode)) = _
  rw [hp, Part.bind_some, eval_embed]
  rw [show extensionPartialCode.eval = extensionPartial from
    Classical.choose_spec (Nat.Partrec.Code.exists_code.mp extension_partial_recursive)]
  exact extension_partial_eval p

private abbrev Total (A : Set ℕ) (f : ℕ → ℕ) : Prop :=
  PartialComputable A (fun x => Part.some (f x))

private theorem total_congr {A : Set ℕ} {f g : ℕ → ℕ} (hf : Total A f)
    (h : ∀ x, f x = g x) : Total A g := by
  have he : f = g := funext h
  exact he ▸ hf

private theorem total_ordinary (A : Set ℕ) {f : ℕ → ℕ} (hf : Computable f) :
    Total A f := by
  exact ordinary_inclusion A (Partrec.nat_iff.mp hf.partrec)

private theorem total_comp {A : Set ℕ} {f g : ℕ → ℕ}
    (hf : Total A f) (hg : Total A g) : Total A (fun x => f (g x)) := by
  obtain ⟨c, hc⟩ := hf
  obtain ⟨d, hd⟩ := hg
  refine ⟨.comp c d, funext fun x => ?_⟩
  change (eval A d x).bind (eval A c) = _
  rw [congrFun hd x, Part.bind_some, congrFun hc (g x)]

private theorem total_pair {A : Set ℕ} {f g : ℕ → ℕ}
    (hf : Total A f) (hg : Total A g) : Total A (fun x => Nat.pair (f x) (g x)) := by
  obtain ⟨c, hc⟩ := hf
  obtain ⟨d, hd⟩ := hg
  refine ⟨.pair c d, funext fun x => ?_⟩
  rw [eval, congrFun hc x, Part.bind_some, congrFun hd x, Part.map_some]

private theorem total_iterate (A : Set ℕ) (F : ℕ → ℕ → ℕ) (s₀ : ℕ)
    (hF : Total A (fun z => F z.unpair.1 z.unpair.2)) :
    Total A (fun n => Nat.rec s₀ F n) := by
  obtain ⟨r, hr⟩ := hF
  let base : Code := embed (Nat.Partrec.Code.const s₀)
  let step : Code := .comp r .right
  have he (n : ℕ) : eval A (.prec base step) (Nat.pair 0 n) =
      Part.some (Nat.rec s₀ F n) := by
    induction n with
    | zero =>
      rw [eval_prec_zero]
      simp [base, eval_embed, Nat.Partrec.Code.eval_const]
    | succ n ih =>
      rw [eval_prec_succ, ih, Part.bind_some]
      change (eval A .right (Nat.pair 0 (Nat.pair n (Nat.rec s₀ F n)))).bind (eval A r) = _
      simp only [eval, Nat.unpair_pair, Part.bind_some, congrFun hr,
        ]
  refine ⟨.comp (.prec base step) (.pair .zero identityCode), funext fun n => ?_⟩
  change (eval A (.pair .zero identityCode) n).bind (eval A (.prec base step)) = _
  simp only [eval, identity_eval, Part.bind_some, Part.map_some]
  exact he n

theorem round_computable :
    PartialComputable (jump ∅) (fun z => Part.some (round z.unpair.1 z.unpair.2)) := by
  have he : Total (jump ∅) extendState := ⟨extensionCode, funext extension_code_eval⟩
  let first (z : ℕ) := extendState
    (parameters z.unpair.1 z.unpair.2.unpair.1 z.unpair.2.unpair.2)
  have hp : Primrec (fun z : ℕ => parameters z.unpair.1
      z.unpair.2.unpair.1 z.unpair.2.unpair.2) :=
    parameters_primitive.comp
      (((Primrec.fst.comp Primrec.unpair).pair
        ((Primrec.fst.comp Primrec.unpair).comp (Primrec.snd.comp Primrec.unpair))).pair
        ((Primrec.snd.comp Primrec.unpair).comp (Primrec.snd.comp Primrec.unpair)))
  have hfirst : Total (jump ∅) first := total_comp he (total_ordinary _ hp.to_comp)
  let swappedParameters (w : ℕ) := parameters w.unpair.1
    w.unpair.2.unpair.2 w.unpair.2.unpair.1
  have hsp : Primrec swappedParameters := parameters_primitive.comp
    (((Primrec.fst.comp Primrec.unpair).pair
      ((Primrec.snd.comp Primrec.unpair).comp (Primrec.snd.comp Primrec.unpair))).pair
      ((Primrec.fst.comp Primrec.unpair).comp (Primrec.snd.comp Primrec.unpair)))
  have hpair : Total (jump ∅) (fun z => Nat.pair z.unpair.1 (first z)) :=
    total_pair (total_ordinary _ (Primrec.fst.comp Primrec.unpair).to_comp) hfirst
  have hsecond := total_comp he (total_comp (total_ordinary _ hsp.to_comp) hpair)
  let swap (s : ℕ) := Nat.pair s.unpair.2 s.unpair.1
  have hswap : Primrec swap := Primrec₂.natPair.comp
    (Primrec.snd.comp Primrec.unpair) (Primrec.fst.comp Primrec.unpair)
  apply total_congr (total_comp (total_ordinary _ hswap.to_comp) hsecond)
  intro z
  simp only [swap, swappedParameters, first, Nat.unpair_pair, round, extend]

theorem stage_computable : PartialComputable (jump ∅) (fun n => Part.some (stage n)) := by
  apply total_congr (total_iterate (jump ∅) round (Nat.pair 0 0) round_computable)
  intro n
  induction n with
  | zero => rfl
  | succ n ih => simp only [stage, ih]

theorem characteristic_computable :
    PartialComputable (jump ∅) (fun x => Part.some (wordBit (leftWord (x + 1)) x)) ∧
      PartialComputable (jump ∅) (fun x => Part.some (wordBit (rightWord (x + 1)) x)) := by
  have hs : Total (jump ∅) (fun x => stage (x + 1)) :=
    total_comp stage_computable (total_ordinary _ Primrec.succ.to_comp)
  have hp := total_pair hs (total_ordinary (jump ∅) Computable.id)
  have hl : Primrec (fun z : ℕ => wordBit z.unpair.1.unpair.1 z.unpair.2) :=
    PostsTheorem.beta_primitive.comp
      ((Primrec.fst.comp Primrec.unpair).comp (Primrec.fst.comp Primrec.unpair))
      (Primrec.snd.comp Primrec.unpair)
  have hr : Primrec (fun z : ℕ => wordBit z.unpair.1.unpair.2 z.unpair.2) :=
    PostsTheorem.beta_primitive.comp
      ((Primrec.snd.comp Primrec.unpair).comp (Primrec.fst.comp Primrec.unpair))
      (Primrec.snd.comp Primrec.unpair)
  constructor
  · apply total_congr (total_comp (total_ordinary _ hl.to_comp) hp)
    intro x
    simp only [Nat.unpair_pair, leftWord, id_eq]
  · apply total_congr (total_comp (total_ordinary _ hr.to_comp) hp)
    intro x
    simp only [Nat.unpair_pair, rightWord, id_eq]

theorem constructed_bounds :
    TuringDegrees.Reducible leftSet (jump ∅) ∧
      TuringDegrees.Reducible rightSet (jump ∅) := by
  obtain ⟨ca, ha⟩ := characteristic_computable.1
  obtain ⟨cb, hb⟩ := characteristic_computable.2
  refine ⟨⟨ca, ?_⟩, ⟨cb, ?_⟩⟩
  · intro x
    rw [congrFun ha x]
    exact congrArg Part.some (union_bit leftWord x).symm
  · intro x
    rw [congrFun hb x]
    exact congrArg Part.some (union_bit rightWord x).symm

end
end Lemmatheca.ComputabilityTheory.IncomparableTuringDegrees
