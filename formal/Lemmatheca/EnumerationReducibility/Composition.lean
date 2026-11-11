import Lemmatheca.EnumerationReducibility.Basic

namespace Lemmatheca.ComputabilityTheory.EnumerationReducibility
open UniversalComputation

/-- This finite test uses the existing bounded numerical evaluator, not a classical oracle. -/
def stageCheck (e s x : ℕ) : Bool :=
  decide (x < s) && (List.range s).any (fun k => decide (0 < boundedValue k e x))

def coverCode (w : ℕ) : ℕ :=
  FiniteSequenceCoding.fold FiniteSequenceCoding.append w 0

def CompositeRules (R S : RuleRelation) (n c : ℕ) : Prop :=
  ∃ d w, R n d ∧ FiniteSequenceCoding.length w = FiniteSequenceCoding.length d ∧
    (∀ i < FiniteSequenceCoding.length d,
      S (FiniteSequenceCoding.entry d i) (FiniteSequenceCoding.entry w i)) ∧ c = coverCode w

def compositionOffer (r s z w : ℕ) : Option ℕ :=
  let d := w.unpair.1
  let cs := w.unpair.2.unpair.1
  let t := w.unpair.2.unpair.2
  if stageCheck r t (Nat.pair z.unpair.1 d) &&
      decide (FiniteSequenceCoding.length cs = FiniteSequenceCoding.length d) &&
      decide (z.unpair.2 = coverCode cs) &&
      (List.range (FiniteSequenceCoding.length d)).all (fun i =>
        stageCheck s t (Nat.pair (FiniteSequenceCoding.entry d i) (FiniteSequenceCoding.entry cs i)))
  then some 0 else none

def compositionSearch (r s z : ℕ) : Part ℕ := Nat.rfindOpt (compositionOffer r s z)

private theorem stage_check_spec (e s x : ℕ) :
    stageCheck e s x = true ↔ x ∈ EffectiveEnumerations.stage e s := by
  simp [stageCheck, EffectiveEnumerations.stage, certificate, List.any_eq_true]

theorem stageCheck_primitive :
    Primrec (fun p : (ℕ × ℕ) × ℕ => stageCheck p.1.1 p.1.2 p.2) := by
  classical
  exact EffectiveEnumerations.stage_predicate_primitive.decide.of_eq fun p => by
    exact Bool.eq_iff_iff.mpr (by simp only [decide_eq_true_eq, stage_check_spec])

theorem stageCheck_correct (e s x : ℕ) :
    stageCheck e s x = true ↔ x ∈ EffectiveEnumerations.stage e s := by
  exact stage_check_spec e s x

theorem coverCode_primitive : Primrec coverCode := by
  exact (FiniteSequenceCoding.primrec_fold FiniteSequenceCoding.primrec_append).comp
    Primrec.id (Primrec.const 0)

private theorem decode_append_fold (l : List ℕ) (z : ℕ) :
    FiniteSequenceCoding.decode (l.foldl FiniteSequenceCoding.append z) =
      FiniteSequenceCoding.decode z ++ l.flatMap FiniteSequenceCoding.decode := by
  induction l generalizing z with
  | nil => simp
  | cons a l ih =>
    simp [List.foldl_cons, ih, FiniteSequenceCoding.append, List.append_assoc]

theorem coverCode_set (w : ℕ) :
    (finiteSet (coverCode w) : Set ℕ) =
      {x | ∃ c ∈ FiniteSequenceCoding.decode w, x ∈ finiteSet c} := by
  ext x
  simp [finiteSet, coverCode, FiniteSequenceCoding.fold, decode_append_fold]

theorem coverCode_zero : coverCode 0 = 0 := by
  simp [coverCode, FiniteSequenceCoding.fold]

private theorem mem_finite_iff (x d : ℕ) : x ∈ finiteSet d ↔
    ∃ i, ∃ _hi : i < FiniteSequenceCoding.length d, FiniteSequenceCoding.entry d i = x := by
  simp only [finiteSet, List.mem_toFinset]
  rw [List.mem_iff_getElem]
  exact exists_congr fun i => exists_congr fun hi => by
    simp [FiniteSequenceCoding.entry, List.getElem?_eq_getElem hi]


theorem composite_operator (R S : RuleRelation) (B : Set ℕ) :
    operatorOf (CompositeRules R S) B = operatorOf R (operatorOf S B) := by
  classical
  ext n
  constructor
  · rintro ⟨c, ⟨d, w, hR, hlen, hS, rfl⟩, hcB⟩
    refine ⟨d, hR, ?_⟩
    intro x hx
    obtain ⟨i, hi, rfl⟩ := (mem_finite_iff x d).mp hx
    refine ⟨FiniteSequenceCoding.entry w i, hS i hi, ?_⟩
    intro y hy
    apply hcB
    rw [coverCode_set]
    refine ⟨FiniteSequenceCoding.entry w i, ?_, hy⟩
    have : FiniteSequenceCoding.entry w i ∈ finiteSet w :=
      (mem_finite_iff _ _).mpr ⟨i, by omega, rfl⟩
    simpa only [finiteSet, List.mem_toFinset] using this
  · rintro ⟨d, hR, hd⟩
    have hx (i : Fin (FiniteSequenceCoding.length d)) :
        ∃ c, S (FiniteSequenceCoding.entry d i.val) c ∧ (finiteSet c : Set ℕ) ⊆ B :=
      hd ((mem_finite_iff _ _).mpr ⟨i.val, i.isLt, rfl⟩)
    choose f hf using hx
    let w := FiniteSequenceCoding.code (List.ofFn f)
    have hlen : FiniteSequenceCoding.length w = FiniteSequenceCoding.length d := by
      change (FiniteSequenceCoding.decode (FiniteSequenceCoding.code (List.ofFn f))).length = _
      rw [FiniteSequenceCoding.decode_code]
      exact List.length_ofFn
    have hw (i : ℕ) (hi : i < FiniteSequenceCoding.length d) :
        FiniteSequenceCoding.entry w i = f ⟨i, hi⟩ := by
      simp [w, FiniteSequenceCoding.entry, hi]
    refine ⟨coverCode w, ⟨d, w, hR, hlen, ?_, rfl⟩, ?_⟩
    · intro i hi
      rw [hw i hi]
      exact (hf ⟨i, hi⟩).1
    · intro x hx
      rw [coverCode_set] at hx
      obtain ⟨c, hc, hx⟩ := hx
      have hcmem : c ∈ finiteSet w := by simpa [finiteSet] using hc
      obtain ⟨i, hi, rfl⟩ := (mem_finite_iff c w).mp hcmem
      rw [hw i (by omega)] at hx
      exact (hf ⟨i, by omega⟩).2 hx

theorem composition_offer_primitive :
    Primrec (fun p : (ℕ × (ℕ × ℕ)) × ℕ => compositionOffer p.1.1 p.1.2.1 p.1.2.2 p.2) := by
  let r (p : (ℕ × (ℕ × ℕ)) × ℕ) := p.1.1
  let s (p : (ℕ × (ℕ × ℕ)) × ℕ) := p.1.2.1
  let n (p : (ℕ × (ℕ × ℕ)) × ℕ) := p.1.2.2.unpair.1
  let c (p : (ℕ × (ℕ × ℕ)) × ℕ) := p.1.2.2.unpair.2
  let d (p : (ℕ × (ℕ × ℕ)) × ℕ) := p.2.unpair.1
  let cs (p : (ℕ × (ℕ × ℕ)) × ℕ) := p.2.unpair.2.unpair.1
  let t (p : (ℕ × (ℕ × ℕ)) × ℕ) := p.2.unpair.2.unpair.2
  have hr : Primrec r := Primrec.fst.comp Primrec.fst
  have hs : Primrec s := Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hn : Primrec n := Primrec.fst.comp (Primrec.unpair.comp
    (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
  have hc : Primrec c := Primrec.snd.comp (Primrec.unpair.comp
    (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
  have hd : Primrec d := Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)
  have hcs : Primrec cs := Primrec.fst.comp (Primrec.unpair.comp
    (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)))
  have ht : Primrec t := Primrec.snd.comp (Primrec.unpair.comp
    (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)))
  have hfirst : PrimrecPred (fun p => stageCheck (r p) (t p) (Nat.pair (n p) (d p)) = true) :=
    Primrec.eq.comp (stageCheck_primitive.comp
      ((hr.pair ht).pair (Primrec₂.natPair.comp hn hd))) (Primrec.const true)
  have hlen : PrimrecPred (fun p => FiniteSequenceCoding.length (cs p) = FiniteSequenceCoding.length (d p)) :=
    Primrec.eq.comp (FiniteSequenceCoding.primrec_length.comp hcs)
      (FiniteSequenceCoding.primrec_length.comp hd)
  have hcover : PrimrecPred (fun p => c p = coverCode (cs p)) :=
    Primrec.eq.comp hc (coverCode_primitive.comp hcs)
  have hinner : PrimrecRel (fun p i => stageCheck (s p) (t p)
      (Nat.pair (FiniteSequenceCoding.entry (d p) i) (FiniteSequenceCoding.entry (cs p) i)) = true) :=
    Primrec.eq.comp (stageCheck_primitive.comp
      (((hs.comp Primrec.fst).pair (ht.comp Primrec.fst)).pair
        (Primrec₂.natPair.comp
          (FiniteSequenceCoding.primrec_entry.comp (hd.comp Primrec.fst) Primrec.snd)
          (FiniteSequenceCoding.primrec_entry.comp (hcs.comp Primrec.fst) Primrec.snd))))
      (Primrec.const true)
  have hall := (PrimitiveRecursion.bounded_forall_primrec hinner).comp
    Primrec.id (FiniteSequenceCoding.primrec_length.comp hd)
  exact (Primrec.ite (hfirst.and (hlen.and (hcover.and hall)))
    (Primrec.const (some 0)) (Primrec.const none)).of_eq fun p => by
      simp only [compositionOffer, r, s, n, c, d, cs, t, Bool.and_eq_true,
        decide_eq_true_eq, List.all_eq_true, List.mem_range, and_assoc, id_eq]

theorem composition_search_partial :
    Partrec (fun p : ℕ × (ℕ × ℕ) => compositionSearch p.1 p.2.1 p.2.2) := by
  exact Partrec.rfindOpt composition_offer_primitive.to_comp

theorem composition_has_program :
    ∃ v, ∀ r s z, phi v (Nat.pair r (Nat.pair s z)) = compositionSearch r s z := by
  have hg : Computable (fun x : ℕ => x.unpair.2.unpair) :=
    Computable.unpair.comp (Computable.snd.comp Computable.unpair)
  have hf : Partrec (fun x : ℕ =>
      compositionSearch x.unpair.1 x.unpair.2.unpair.1 x.unpair.2.unpair.2) :=
    Partrec₂.comp (f := fun r (p : ℕ × ℕ) => compositionSearch r p.1 p.2)
      composition_search_partial (Computable.fst.comp Computable.unpair) hg
  obtain ⟨v, hv⟩ := phi_complete (Partrec.nat_iff.mp hf)
  exact ⟨v, fun r s z => by simpa using congrFun hv (Nat.pair r (Nat.pair s z))⟩

noncomputable def compositionMaster : ℕ := Classical.choose composition_has_program

noncomputable def compositionIndex (r s : ℕ) : ℕ := specialize (specialize compositionMaster r) s

theorem compositionMaster_eval (r s z : ℕ) :
    phi compositionMaster (Nat.pair r (Nat.pair s z)) = compositionSearch r s z := by
  exact Classical.choose_spec composition_has_program r s z

theorem compositionIndex_primitive : Primrec₂ compositionIndex := by
  exact (specialize_primitive.comp
    (specialize_primitive.comp (Primrec.const compositionMaster) Primrec.fst) Primrec.snd).to₂

theorem compositionIndex_eval (r s z : ℕ) :
    phi (compositionIndex r s) z = compositionSearch r s z := by
  simp only [compositionIndex, specialize_eval, compositionMaster_eval]

private theorem finite_rules_stage (e : ℕ) (l : List ℕ)
    (hl : ∀ x ∈ l, (phi e x).Dom) :
    ∃ t, ∀ x ∈ l, x ∈ EffectiveEnumerations.stage e t := by
  induction l with
  | nil => exact ⟨0, by simp⟩
  | cons x l ih =>
    obtain ⟨t, ht⟩ := (EffectiveEnumerations.stage_union e x).mp (hl x (by simp))
    obtain ⟨s, hs⟩ := ih (fun y hy => hl y (by simp [hy]))
    refine ⟨max t s, ?_⟩
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact EffectiveEnumerations.stage_monotone e (le_max_left t s) ht
    · exact EffectiveEnumerations.stage_monotone e (le_max_right t s) (hs y hy)

private theorem composition_offer_dom (r s z k : ℕ) :
    (∃ y, y ∈ compositionOffer r s z k) ↔
      Nat.pair z.unpair.1 k.unpair.1 ∈ EffectiveEnumerations.stage r k.unpair.2.unpair.2 ∧
      FiniteSequenceCoding.length k.unpair.2.unpair.1 = FiniteSequenceCoding.length k.unpair.1 ∧
      z.unpair.2 = coverCode k.unpair.2.unpair.1 ∧
      ∀ i < FiniteSequenceCoding.length k.unpair.1,
        Nat.pair (FiniteSequenceCoding.entry k.unpair.1 i)
          (FiniteSequenceCoding.entry k.unpair.2.unpair.1 i) ∈
            EffectiveEnumerations.stage s k.unpair.2.unpair.2 := by
  simp only [compositionOffer]
  split <;> rename_i h
  · simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
      stageCheck_correct, and_assoc] at h
    exact iff_of_true ⟨0, by simp⟩ h
  · simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
      stageCheck_correct, and_assoc] at h
    exact iff_of_false (by simp) h


theorem compositionIndex_rules (r s n d : ℕ) :
    indexedRule (compositionIndex r s) n d ↔ CompositeRules (indexedRule r) (indexedRule s) n d := by
  rw [indexedRule, compositionIndex_eval, compositionSearch, Nat.rfindOpt_dom]
  constructor
  · rintro ⟨k, hk⟩
    obtain ⟨hR, hlen, hc, hS⟩ := (composition_offer_dom r s (Nat.pair n d) k).mp hk
    refine ⟨k.unpair.1, k.unpair.2.unpair.1, ?_, hlen, ?_, by simpa only [Nat.unpair_pair] using hc⟩
    · exact (EffectiveEnumerations.stage_union r _).mpr ⟨_, by simpa using hR⟩
    · intro i hi
      exact (EffectiveEnumerations.stage_union s _).mpr ⟨_, hS i hi⟩
  · rintro ⟨q, w, hR, hlen, hS, rfl⟩
    obtain ⟨t, ht⟩ := (EffectiveEnumerations.stage_union r (Nat.pair n q)).mp hR
    let l := (List.range (FiniteSequenceCoding.length q)).map
      (fun i => Nat.pair (FiniteSequenceCoding.entry q i) (FiniteSequenceCoding.entry w i))
    have hl : ∀ x ∈ l, (phi s x).Dom := by
      intro x hx
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
      exact hS i (List.mem_range.mp hi)
    obtain ⟨u, hu⟩ := finite_rules_stage s l hl
    refine ⟨Nat.pair q (Nat.pair w (max t u)), ?_⟩
    apply (composition_offer_dom _ _ _ _).mpr
    simp only [Nat.unpair_pair]
    refine ⟨EffectiveEnumerations.stage_monotone r (le_max_left t u) ht, hlen, by trivial, ?_⟩
    intro i hi
    exact EffectiveEnumerations.stage_monotone s (le_max_right t u)
      (hu _ (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩))

theorem uniform_composition (r s : ℕ) (B : Set ℕ) :
    operator (compositionIndex r s) B = operator r (operator s B) := by
  have hR : indexedRule (compositionIndex r s) = CompositeRules (indexedRule r) (indexedRule s) :=
    funext (fun n => funext (fun d => propext (compositionIndex_rules r s n d)))
  exact (congrArg (fun R : RuleRelation => operatorOf R B) hR).trans
    (composite_operator (indexedRule r) (indexedRule s) B)

theorem reducible_trans {A B C : Set ℕ} (hAB : Reducible A B) (hBC : Reducible B C) :
    Reducible A C := by
  obtain ⟨r, hr⟩ := hAB
  obtain ⟨s, hs⟩ := hBC
  exact ⟨compositionIndex r s, by rw [uniform_composition, hs, hr]⟩

/-- Recognizer for the constant operator with c.e. output W_a. -/
def constantSearch (a z : ℕ) : Part ℕ :=
  if z.unpair.2 = 0 then (phi a z.unpair.1).map (fun _ => 0) else Part.none

theorem constant_search_partial : Partrec₂ constantSearch := by
  have hp : Computable (fun p : ℕ × ℕ => decide (p.2.unpair.2 = 0)) :=
    (Primrec.eq.comp (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd))
      (Primrec.const 0)).decide.to_comp
  exact (Partrec.cond hp
    ((phi_recursive.comp Computable.fst
      (Computable.fst.comp (Computable.unpair.comp Computable.snd))).map
        (Computable.const 0).to₂) Partrec.none).of_eq fun p => by
      simp [constantSearch]

theorem constant_has_program :
    ∃ v, ∀ a z, phi v (Nat.pair a z) = constantSearch a z := by
  have hf : Partrec (fun x : ℕ => constantSearch x.unpair.1 x.unpair.2) :=
    Partrec₂.comp constant_search_partial
      (Computable.fst.comp Computable.unpair) (Computable.snd.comp Computable.unpair)
  obtain ⟨v, hv⟩ := phi_complete (Partrec.nat_iff.mp hf)
  exact ⟨v, fun a z => by simpa using congrFun hv (Nat.pair a z)⟩

noncomputable def constantMaster : ℕ := Classical.choose constant_has_program

noncomputable def constantIndex (a : ℕ) : ℕ := specialize constantMaster a

theorem constantIndex_primitive : Primrec constantIndex := by
  exact specialize_primitive.comp (Primrec.const constantMaster) Primrec.id

private theorem constant_domain (a n d : ℕ) :
    (constantSearch a (Nat.pair n d)).Dom ↔ d = 0 ∧ (phi a n).Dom := by
  simp only [constantSearch, Nat.unpair_pair]
  by_cases hd : d = 0
  · subst d
    simp only [ite_true, Part.map_Dom, true_and]
  · simp only [hd, ite_false, Part.not_none_dom, false_and]
private theorem constant_value (a z : ℕ) :
    phi (constantIndex a) z = constantSearch a z := by
  rw [constantIndex, specialize_eval]
  exact Classical.choose_spec constant_has_program a z

theorem constantIndex_operator (a : ℕ) (B : Set ℕ) :
    operator (constantIndex a) B = EffectiveEnumerations.indexSet a := by
  ext n
  constructor
  · rintro ⟨d, hd, _⟩
    have he : (phi (constantIndex a) (Nat.pair n d)).Dom =
        (constantSearch a (Nat.pair n d)).Dom := congrArg Part.Dom (constant_value a (Nat.pair n d))
    exact ((constant_domain a n d).mp (he ▸ hd)).2
  · intro hn
    refine ⟨0, ?_, ?_⟩
    · change (phi (constantIndex a) (Nat.pair n 0)).Dom
      rw [constant_value]
      exact (constant_domain a n 0).mpr ⟨rfl, hn⟩
    · simp [finiteSet_empty 0 |>.mpr rfl]

noncomputable def outputIndex (r b : ℕ) : ℕ :=
  Encodable.encode (Nat.Partrec.Code.comp
    (Denumerable.ofNat Nat.Partrec.Code (compositionIndex r (constantIndex b)))
    (.pair (.pair .left .right) .zero))

theorem outputIndex_primitive : Primrec₂ outputIndex := by
  exact (Primrec.encode.comp
    (Nat.Partrec.Code.primrec₂_comp.comp
      ((Primrec.ofNat Nat.Partrec.Code).comp
        (compositionIndex_primitive.comp Primrec.fst (constantIndex_primitive.comp Primrec.snd)))
      (Primrec.const (.pair (.pair .left .right) .zero)))).to₂

private theorem eval_zero_pair (c : Nat.Partrec.Code) (x : ℕ) :
    Nat.Partrec.Code.eval (.comp c (.pair (.pair .left .right) .zero)) x =
      Nat.Partrec.Code.eval c (Nat.pair x 0) := by
  have hin : Nat.Partrec.Code.eval (.pair (.pair .left .right) .zero) x = Part.some (Nat.pair x 0) := by
    have hid : Nat.Partrec.Code.eval (.pair .left .right) x = Part.some x :=
      Nat.Partrec.Code.eval_id x
    have hz : Nat.Partrec.Code.eval .zero x = Part.some 0 :=
      Nat.Partrec.Code.eval_const 0 x
    change Nat.pair <$> Nat.Partrec.Code.eval (.pair .left .right) x <*>
      Nat.Partrec.Code.eval .zero x = _
    rw [hid, hz]
    change ((Part.some x).map Nat.pair).bind (fun f => (Part.some 0).map f) = _
    rw [Part.map_some, Part.bind_some, Part.map_some]
  change (Nat.Partrec.Code.eval (.pair (.pair .left .right) .zero) x).bind
    (fun y => Nat.Partrec.Code.eval c y) = _
  rw [hin]
  exact Part.bind_some (Nat.pair x 0) (fun y => Nat.Partrec.Code.eval c y)

private theorem zero_input_index_eval (e x : ℕ) :
    phi (Encodable.encode (Nat.Partrec.Code.comp (Denumerable.ofNat Nat.Partrec.Code e)
      (.pair (.pair .left .right) .zero))) x = phi e (Nat.pair x 0) := by
  change Nat.Partrec.Code.eval (Denumerable.ofNat Nat.Partrec.Code
    (Encodable.encode (Nat.Partrec.Code.comp (Denumerable.ofNat Nat.Partrec.Code e)
      (.pair (.pair .left .right) .zero)))) x =
    Nat.Partrec.Code.eval (Denumerable.ofNat Nat.Partrec.Code e) (Nat.pair x 0)
  rw [Denumerable.ofNat_encode]
  exact eval_zero_pair (Denumerable.ofNat Nat.Partrec.Code e) x


private theorem zero_input_index_set (e : ℕ) :
    EffectiveEnumerations.indexSet (Encodable.encode (Nat.Partrec.Code.comp
      (Denumerable.ofNat Nat.Partrec.Code e) (.pair (.pair .left .right) .zero))) =
      operator e ∅ := by
  have hbase : EffectiveEnumerations.indexSet (Encodable.encode (Nat.Partrec.Code.comp
      (Denumerable.ofNat Nat.Partrec.Code e) (.pair (.pair .left .right) .zero))) =
      {n | indexedRule e n 0} :=
    Set.ext (fun x => Iff.of_eq (congrArg Part.Dom (zero_input_index_eval e x)))
  exact hbase.trans (operator_empty (indexedRule e)).symm

theorem outputIndex_correct (r b : ℕ) :
    EffectiveEnumerations.indexSet (outputIndex r b) = operator r (EffectiveEnumerations.indexSet b) := by
  exact (zero_input_index_set (compositionIndex r (constantIndex b))).trans
    ((uniform_composition r (constantIndex b) ∅).trans
      (congrArg (operator r) (constantIndex_operator b ∅)))

end Lemmatheca.ComputabilityTheory.EnumerationReducibility
