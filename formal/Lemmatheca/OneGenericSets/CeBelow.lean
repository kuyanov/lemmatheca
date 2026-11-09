import Lemmatheca.OneGenericSets.Decisions
import Lemmatheca.OneGenericSets.Construction

/-! The specified ordinary two-search decider below a 1-generic. -/
namespace Lemmatheca.ComputabilityTheory.OneGenericSets

open OracleComputation OracleProgramNumberings IncomparableTuringDegrees
  ComputableTreesAndPaths PostsTheorem UniversalComputation

set_option backward.isDefEq.respectTransparency false

noncomputable section
attribute [local instance] Classical.propDecidable

def zeroMistakes (i e : ℕ) : Set ℕ :=
  {u | ValidCode u ∧ ∃ x, x ∈ EffectiveEnumerations.indexSet i ∧ certificateValue u e x = 1}

theorem zero_mistakes_enumerable (i e : ℕ) : REPred (fun u => u ∈ zeroMistakes i e) := by
  apply (enumerable_iff_primitive_certificate _).mpr
  let R (u w : ℕ) := ValidCode u ∧
    w.unpair.1 ∈ EffectiveEnumerations.stage i w.unpair.2 ∧ certificateValue u e w.unpair.1 = 1
  have hx : Primrec (fun p : ℕ × ℕ => p.2.unpair.1) :=
    (Primrec.fst.comp Primrec.unpair).comp Primrec.snd
  have hs : Primrec (fun p : ℕ × ℕ => p.2.unpair.2) :=
    (Primrec.snd.comp Primrec.unpair).comp Primrec.snd
  have hR : PrimrecRel R := (valid_code_primitive.comp Primrec.fst).and
    ((EffectiveEnumerations.stage_predicate_primitive.comp (((Primrec.const i).pair hs).pair hx)).and
      (Primrec.eq.comp (certificate_primitive.comp ((Primrec.fst.pair (Primrec.const e)).pair hx))
        (Primrec.const 1)))
  refine ⟨R, hR, ?_⟩
  intro u
  constructor
  · rintro ⟨hu, x, hx, hc⟩
    obtain ⟨k, hk⟩ := (EffectiveEnumerations.stage_union i x).mp hx
    exact ⟨Nat.pair x k, by simpa only [R, Nat.unpair_pair] using And.intro hu (And.intro hk hc)⟩
  · rintro ⟨w, hu, hw, hc⟩
    exact ⟨hu, w.unpair.1, (EffectiveEnumerations.stage_union i _).mpr ⟨_, hw⟩, hc⟩

/-- Pack (enumeration index i, oracle program e, hard-coded word tau, input x). -/
def ceParameters (i e tau x : ℕ) : ℕ := Nat.pair i (Nat.pair e (Nat.pair tau x))

def CeYes (p s : ℕ) : Prop :=
  p.unpair.2.unpair.2.unpair.2 ∈ EffectiveEnumerations.stage p.unpair.1 s

def CeNo (p s : ℕ) : Prop :=
  ∃ v < s, ValidCode v ∧ Prefix p.unpair.2.unpair.2.unpair.1 v ∧
    certificateValue v p.unpair.2.unpair.1 p.unpair.2.unpair.2.unpair.2 = 1

def ceDeciderPartial (p : ℕ) : Part ℕ :=
  (Nat.rfind (fun s => Part.some (decide (CeYes p s ∨ CeNo p s)))).map
    (fun s => if CeYes p s then 1 else 0)

private theorem ce_yes_primitive : PrimrecPred (fun p : ℕ × ℕ => CeYes p.1 p.2) := by
  have hl : Primrec (fun p : ℕ × ℕ => p.1.unpair.1) :=
    (Primrec.fst.comp Primrec.unpair).comp Primrec.fst
  have hr : Primrec (fun p : ℕ × ℕ => p.1.unpair.2) :=
    (Primrec.snd.comp Primrec.unpair).comp Primrec.fst
  have hx := ((Primrec.snd.comp Primrec.unpair).comp
    (Primrec.snd.comp Primrec.unpair)).comp hr
  exact EffectiveEnumerations.stage_predicate_primitive.comp ((hl.pair Primrec.snd).pair hx)

private theorem ce_no_primitive : PrimrecPred (fun p : ℕ × ℕ => CeNo p.1 p.2) := by
  have hl : Primrec (fun z : (ℕ × ℕ) × ℕ => z.1.1) := Primrec.fst.comp Primrec.fst
  have hr := (Primrec.snd.comp Primrec.unpair).comp hl
  have he := (Primrec.fst.comp Primrec.unpair).comp hr
  have hrest := (Primrec.snd.comp Primrec.unpair).comp hr
  have htau := (Primrec.fst.comp Primrec.unpair).comp hrest
  have hx := (Primrec.snd.comp Primrec.unpair).comp hrest
  have hR : PrimrecRel (fun p : ℕ × ℕ => fun v => ValidCode v ∧
      Prefix p.1.unpair.2.unpair.2.unpair.1 v ∧
        certificateValue v p.1.unpair.2.unpair.1 p.1.unpair.2.unpair.2.unpair.2 = 1) :=
    (valid_code_primitive.comp Primrec.snd).and
      ((prefix_primitive.comp (htau.pair Primrec.snd)).and
        (Primrec.eq.comp (certificate_primitive.comp ((Primrec.snd.pair he).pair hx)) (Primrec.const 1)))
  exact (PrimitiveRecursion.bounded_exists_primrec hR).comp Primrec.id Primrec.snd

theorem ce_decider_recursive : Nat.Partrec ceDeciderPartial := by
  have hy : PrimrecPred (fun p : ℕ × ℕ => CeYes p.1 p.2) := ce_yes_primitive
  have hn : PrimrecPred (fun p : ℕ × ℕ => CeNo p.1 p.2) := ce_no_primitive
  have hc : Computable₂ (fun p s => decide (CeYes p s ∨ CeNo p s)) :=
    (hy.or hn).decide.to_comp
  have hout : Computable₂ (fun p s => if CeYes p s then 1 else 0) :=
    (Primrec.ite hy (Primrec.const 1) (Primrec.const 0)).to_comp
  exact Partrec.nat_iff.mp ((Partrec.rfind hc.partrec₂).map hout)

def ceDeciderCode : Nat.Partrec.Code :=
  Classical.choose (Nat.Partrec.Code.exists_code.mp ce_decider_recursive)

theorem ce_decider_code_eval (p : ℕ) : ceDeciderCode.eval p = ceDeciderPartial p := by
  exact congrFun (Classical.choose_spec (Nat.Partrec.Code.exists_code.mp ce_decider_recursive)) p

theorem ce_decider_correct (G : Set ℕ) (i e tau : ℕ)
    (htau : ValidCode tau) (hrealizes : Realizes tau G)
    (havoid : Avoids tau (zeroMistakes i e))
    (hred : TuringDegrees.Reduces (decodeCode e) (EffectiveEnumerations.indexSet i) G)
    (x : ℕ) : ceDeciderCode.eval (ceParameters i e tau x) =
      Part.some (indicator (fun q => q ∈ EffectiveEnumerations.indexSet i) x) := by
  let p := ceParameters i e tau x
  have hn (s : ℕ) (h : CeNo p s) : x ∉ EffectiveEnumerations.indexSet i := by
    intro hx
    simp only [CeNo, p, ceParameters, Nat.unpair_pair] at h
    obtain ⟨v, _, hv, hp, hc⟩ := h
    apply havoid v hv hp
    exact ⟨hv, x, hx, hc⟩
  have hy (s : ℕ) (h : CeYes p s) : x ∈ EffectiveEnumerations.indexSet i :=
    (EffectiveEnumerations.stage_union i x).mpr ⟨s, by simpa only [CeYes, p, ceParameters, Nat.unpair_pair] using h⟩
  have hex : ∃ s, CeYes p s ∨ CeNo p s := by
    by_cases hx : x ∈ EffectiveEnumerations.indexSet i
    · obtain ⟨s, hs⟩ := (EffectiveEnumerations.stage_union i x).mp hx
      exact ⟨s, Or.inl (by simpa only [CeYes, p, ceParameters, Nat.unpair_pair] using hs)⟩
    · have hz : 0 ∈ OracleProgramNumberings.phi G e x := by
        change 0 ∈ eval G (decodeCode e) x
        rw [hred x]
        simp [indicator, hx]
      have hnorm := normalize_valid tau htau
      have hrnorm : Realizes (normalize tau) G := by rwa [hnorm]
      obtain ⟨v, hv, hp, _, hc⟩ := valid_prefix_adequacy G (normalize tau) e x 0 hrnorm hz
      rw [hnorm] at hp
      refine ⟨v + 1, Or.inr ?_⟩
      simpa only [CeNo, p, ceParameters, Nat.unpair_pair] using
        (show ∃ w < v + 1, ValidCode w ∧ Prefix tau w ∧ certificateValue w e x = 1 from
          ⟨v, Nat.lt_succ_self _, hv, hp, hc⟩)
  let result := Nat.rfind (fun s => Part.some (decide (CeYes p s ∨ CeNo p s)))
  have hd : result.Dom := by simpa [result] using hex
  obtain ⟨s, hs⟩ := Part.dom_iff_mem.mp hd
  have hgood : CeYes p s ∨ CeNo p s := by simpa [result] using Nat.rfind_spec hs
  rw [ce_decider_code_eval]
  change result.map (fun s => if CeYes p s then 1 else 0) = _
  rw [Part.eq_some_iff.mpr hs, Part.map_some]
  by_cases hx : x ∈ EffectiveEnumerations.indexSet i
  · have hh : CeYes p s := hgood.resolve_right (fun h => hn s h hx)
    simp [hh, indicator, hx]
  · have hh : ¬ CeYes p s := fun h => hx (hy s h)
    simp [hh, indicator, hx]

theorem generic_ce_below_computable (G : Set ℕ) (hG : IsOneGeneric G) (X : Set ℕ)
    (hX : REPred (fun x => x ∈ X)) (hred : TuringDegrees.Reducible X G) :
    ComputablePred (fun x => x ∈ X) := by
  classical
  obtain ⟨i, hi⟩ := (enumerable_iff_index _).mp hX
  have hEq : EffectiveEnumerations.indexSet i = X := by
    ext x
    exact (hi x).symm
  obtain ⟨c, hc⟩ := hred
  let e := encodeCode c
  have he : TuringDegrees.Reduces (decodeCode e) (EffectiveEnumerations.indexSet i) G := by
    simpa only [e, decode_encode, hEq] using hc
  have hnot : ¬ Meets G (zeroMistakes i e) := by
    rintro ⟨u, _, hr, _, x, hx, hz⟩
    have hout := certificate_sound G u e x 0 hr hz
    change 0 ∈ eval G (decodeCode e) x at hout
    rw [he x] at hout
    simp [indicator, hx] at hout
  have hvalid : ∀ u ∈ zeroMistakes i e, ValidCode u := fun _ hu => hu.1
  rcases (generic_iff_enumerable_collections G).mp hG _
    (zero_mistakes_enumerable i e) hvalid with hm | ⟨tau, htau, hr, ha⟩
  · exact (hnot hm).elim
  · have hp : Computable (fun x => ceParameters i e tau x) := by
      exact (Primrec₂.natPair.comp (Primrec.const i)
        (Primrec₂.natPair.comp (Primrec.const e)
          (Primrec₂.natPair.comp (Primrec.const tau) Primrec.id))).to_comp
    have hpart : Partrec (fun x => ceDeciderPartial (ceParameters i e tau x)) :=
      (Partrec.nat_iff.mpr ce_decider_recursive).comp hp.partrec
    have hchi : Computable (indicator (fun q => q ∈ EffectiveEnumerations.indexSet i)) :=
      hpart.of_eq_tot (fun x => by
        rw [← ce_decider_code_eval, ce_decider_correct G i e tau htau hr ha he x]
        exact Part.mem_some _)
    rw [← hEq]
    exact (decidable_iff_characteristic _).mpr ⟨_, hchi, fun _ => rfl⟩

theorem generic_no_ce_degree (G : Set ℕ) (hG : IsOneGeneric G) (X : Set ℕ)
    (hX : REPred (fun x => x ∈ X)) : ¬ TuringDegrees.Equivalent G X := by
  intro heq
  have hc := generic_ce_below_computable G hG X hX heq.2
  exact generic_noncomputable G hG (TuringDegrees.computable_of_reducible heq.1 hc)

end
end Lemmatheca.ComputabilityTheory.OneGenericSets
