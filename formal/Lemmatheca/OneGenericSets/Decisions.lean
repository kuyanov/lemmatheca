import Lemmatheca.OneGenericSets.Basic
import Lemmatheca.OracleComputation.Examples
import Lemmatheca.TruthTableAndWeakTruthTableReductions.Programs

/-! Finite halting decisions, one actual prefix recognizer, and forcing equals truth. -/
namespace Lemmatheca.ComputabilityTheory.OneGenericSets

open OracleComputation OracleProgramNumberings IncomparableTuringDegrees
  ComputableTreesAndPaths PostsTheorem UniversalComputation

set_option backward.isDefEq.respectTransparency false

noncomputable section
attribute [local instance] Classical.propDecidable

def ForcesHalting (u e x : ℕ) : Prop := 0 < certificateValue u e x

def ForcesDivergence (u e x : ℕ) : Prop :=
  ∀ v, ValidCode v → Prefix u v → certificateValue v e x = 0

def haltingWords (e x : ℕ) : Set ℕ := {u | ValidCode u ∧ ForcesHalting u e x}

/-- Joint ordinary recognizer input is pair(pair(e,x),u). -/
def haltingPartial (z : ℕ) : Part ℕ :=
  (Nat.rfind (fun _ => Part.some (decide
    (ValidCode z.unpair.2 ∧ ForcesHalting z.unpair.2 z.unpair.1.unpair.1
      z.unpair.1.unpair.2)))).map (fun _ => 0)

theorem halting_partial_recursive : Nat.Partrec haltingPartial := by
  have hl : Primrec (fun z : ℕ => z.unpair.1) := Primrec.fst.comp Primrec.unpair
  have hr : Primrec (fun z : ℕ => z.unpair.2) := Primrec.snd.comp Primrec.unpair
  have hp : PrimrecPred (fun z : ℕ => ValidCode z.unpair.2 ∧
      ForcesHalting z.unpair.2 z.unpair.1.unpair.1 z.unpair.1.unpair.2) :=
    (valid_code_primitive.comp hr).and
      (Primrec.nat_lt.comp (Primrec.const 0)
        (certificate_primitive.comp ((hr.pair (hl.comp hl)).pair (hr.comp hl))))
  have hc : Computable₂ (fun (z : ℕ) (_ : ℕ) => decide
      (ValidCode z.unpair.2 ∧ ForcesHalting z.unpair.2 z.unpair.1.unpair.1 z.unpair.1.unpair.2)) :=
    (hp.decide.to_comp.comp Computable.fst).to₂
  exact Partrec.nat_iff.mp ((Partrec.rfind hc.partrec₂).map (Computable.const 0).to₂)

def haltingCode : Nat.Partrec.Code :=
  Classical.choose (Nat.Partrec.Code.exists_code.mp halting_partial_recursive)

def haltingIndex (e x : ℕ) : ℕ :=
  UniversalComputation.specialize (Encodable.encode haltingCode) (Nat.pair e x)

theorem halting_index_primitive : Primrec₂ haltingIndex := by
  exact UniversalComputation.specialize_primitive.comp₂
    (Primrec₂.const (Encodable.encode haltingCode)) Primrec₂.natPair

theorem halting_index_eval (e x u : ℕ) :
    UniversalComputation.phi (haltingIndex e x) u =
      if u ∈ haltingWords e x then Part.some 0 else Part.none := by
  rw [haltingIndex, UniversalComputation.specialize_eval]
  simp only [UniversalComputation.phi, Denumerable.ofNat_encode]
  rw [show haltingCode.eval = haltingPartial from
    Classical.choose_spec (Nat.Partrec.Code.exists_code.mp halting_partial_recursive)]
  simp only [haltingPartial, Nat.unpair_pair]
  by_cases h : ValidCode u ∧ ForcesHalting u e x
  · have hs : Nat.rfind (fun _ : ℕ => Part.some (decide (ValidCode u ∧ ForcesHalting u e x))) = Part.some 0 := by
      apply Part.eq_some_iff.mpr
      exact Nat.mem_rfind.mpr ⟨by simp [h], fun {m} hm => by omega⟩
    rw [hs, Part.map_some]
    simp [haltingWords, h]
  · have hn : u ∉ haltingWords e x := h
    rw [ite_eq_right hn]
    apply Part.eq_none_iff.mpr
    intro y hy
    rw [Part.mem_map_iff] at hy
    obtain ⟨n, hn, _⟩ := hy
    have ht := Nat.rfind_spec hn
    simp [h] at ht

theorem halting_index_words (e x : ℕ) : wordSet (haltingIndex e x) = haltingWords e x := by
  ext u
  simp [wordSet, EffectiveEnumerations.indexSet, halting_index_eval, haltingWords]
  by_cases hv : ValidCode u <;> by_cases hh : ForcesHalting u e x <;> simp_all

theorem halting_words_enumerable (e x : ℕ) : REPred (fun u => u ∈ haltingWords e x) := by
  rw [← halting_index_words]
  exact word_set_enumerable _

theorem forces_halting_sound (G : Set ℕ) (u e x : ℕ) (hu : Realizes u G)
    (hf : ForcesHalting u e x) : (OracleProgramNumberings.phi G e x).Dom := by
  let y := certificateValue u e x - 1
  have hy : certificateValue u e x = y + 1 := by dsimp [y]; unfold ForcesHalting at hf; omega
  exact (certificate_sound G u e x y hu hy).1

theorem valid_prefix_adequacy (G : Set ℕ) (u e x y : ℕ)
    (hu : Realizes u G) (hy : y ∈ OracleProgramNumberings.phi G e x) :
    ∃ v, ValidCode v ∧ Prefix u v ∧ Realizes v G ∧ certificateValue v e x = y + 1 := by
  obtain ⟨v, hp, hr, hc⟩ := prefix_adequacy G u e x y hu hy
  let w := prefixCode G (wordLength v)
  have hs := prefixCode_spec G (wordLength v)
  have hwlen : wordLength w = wordLength v := hs.1
  have hw : Realizes w G := by
    intro q hq
    exact hs.2 q (by rw [← hwlen]; exact hq)
  refine ⟨w, prefix_code_valid G _, ⟨by rw [hwlen]; exact hp.1, ?_⟩, hw, ?_⟩
  · intro q hq
    exact (hu q hq).trans (hs.2 q (lt_of_lt_of_le hq hp.1)).symm
  · change finiteValue w (wordLength w) e x = y + 1
    rw [hwlen, finiteValue_agreement G w (wordLength v) e x hs.2]
    rw [← finiteValue_agreement G v (wordLength v) e x hr]
    exact hc

theorem forces_divergence_sound (G : Set ℕ) (u e x : ℕ) (hu : Realizes u G)
    (hf : ForcesDivergence u e x) : ¬ (OracleProgramNumberings.phi G e x).Dom := by
  intro hd
  obtain ⟨y, hy⟩ := Part.dom_iff_mem.mp hd
  obtain ⟨v, hv, hp, _, hc⟩ := valid_prefix_adequacy G u e x y hu hy
  have hz := hf v hv hp
  omega

theorem forcing_persists (u v e x : ℕ) (huv : Prefix u v) :
    (ForcesHalting u e x → ForcesHalting v e x) ∧
      (ForcesDivergence u e x → ForcesDivergence v e x) := by
  constructor
  · intro h
    let y := certificateValue u e x - 1
    have hy : certificateValue u e x = y + 1 := by dsimp [y]; unfold ForcesHalting at h; omega
    have hv := certificate_persists u v e x y huv hy
    unfold ForcesHalting
    omega
  · intro h w hw hvw
    exact h w hw (prefix_trans huv hvw)

theorem forcing_exclusive (u e x : ℕ) (hu : ValidCode u) :
    ¬ (ForcesHalting u e x ∧ ForcesDivergence u e x) := by
  rintro ⟨hh, hd⟩
  have hz := hd u hu (prefix_refl u)
  unfold ForcesHalting at hh
  omega

/-- Reuse the established finite oracle-prefix recursion, with unary input packing. -/
def prefixCollectorCode : Code :=
  .comp StrongReductions.prefixProgram (.pair .zero identityCode)

theorem prefix_collector_eval (A : Set ℕ) (n : ℕ) :
    eval A prefixCollectorCode n = Part.some (prefixCode A n) := by
  obtain ⟨tau, ht, hc, _⟩ := StrongReductions.prefix_program_trace A 0 n
  have he : eval A StrongReductions.prefixProgram (Nat.pair 0 n) = Part.some (prefixCode A n) :=
    Part.eq_some_iff.mpr (trace_sound ht hc)
  simpa [prefixCollectorCode, eval, identity_eval] using he

/-- z = pair(pair(e,k),u), where u is the length-k oracle prefix. -/
def watchFiniteTest (z : ℕ) : ℕ :=
  if ∃ v < z.unpair.1.unpair.2,
    ValidCode v ∧ v ∈ EffectiveEnumerations.stage z.unpair.1.unpair.1 z.unpair.1.unpair.2 ∧
      Prefix v z.unpair.2 then 0 else 1

theorem watch_finite_test_primitive : Primrec watchFiniteTest := by
  have hl : Primrec (fun z : ℕ × ℕ => z.1.unpair.1) :=
    (Primrec.fst.comp Primrec.unpair).comp Primrec.fst
  have he := (Primrec.fst.comp Primrec.unpair).comp hl
  have hk := (Primrec.snd.comp Primrec.unpair).comp hl
  have hu : Primrec (fun z : ℕ × ℕ => z.1.unpair.2) :=
    (Primrec.snd.comp Primrec.unpair).comp Primrec.fst
  have hR : PrimrecRel (fun z : ℕ => fun v => ValidCode v ∧
      v ∈ EffectiveEnumerations.stage z.unpair.1.unpair.1 z.unpair.1.unpair.2 ∧ Prefix v z.unpair.2) :=
    (valid_code_primitive.comp Primrec.snd).and
      ((EffectiveEnumerations.stage_predicate_primitive.comp ((he.pair hk).pair Primrec.snd)).and
        (prefix_primitive.comp (Primrec.snd.pair hu)))
  have hb := (PrimitiveRecursion.bounded_exists_primrec hR).comp Primrec.id
    ((Primrec.snd.comp Primrec.unpair).comp (Primrec.fst.comp Primrec.unpair))
  exact Primrec.ite hb (Primrec.const 0) (Primrec.const 1)

def watchFiniteTestCode : Nat.Partrec.Code :=
  ordinaryCode watchFiniteTest (Primrec.nat_iff.mp watch_finite_test_primitive)

def watchTestCode : Code :=
  .comp (embed watchFiniteTestCode)
    (.pair identityCode (.comp prefixCollectorCode .right))

def prefixRecognizerCode : Code :=
  .comp (.find' watchTestCode) (.pair identityCode .zero)

def prefixRecognizerIndex (e : ℕ) : ℕ :=
  encodeCode (.comp prefixRecognizerCode (constantCode e))

def WatchSuccess (A : Set ℕ) (e k : ℕ) : Prop :=
  ∃ v < k, ValidCode v ∧ v ∈ EffectiveEnumerations.stage e k ∧ Realizes v A

theorem watch_test_eval (A : Set ℕ) (e k : ℕ) :
    eval A watchTestCode (Nat.pair e k) = Part.some (if WatchSuccess A e k then 0 else 1) := by
  have hiff (v : ℕ) (hvk : v < k) : Prefix v (prefixCode A k) ↔ Realizes v A := by
    have hs := prefixCode_spec A k
    constructor
    · intro hp q hq
      exact (hp.2 q hq).trans (hs.2 q (lt_of_lt_of_le hq (by rw [← hs.1]; exact hp.1)))
    · intro hr
      have hvlen : wordLength v ≤ v := by
        simpa [wordLength, FiniteSequenceCoding.length] using
          Encodable.length_le_encode (FiniteSequenceCoding.decode v)
      refine ⟨?_, fun q hq => ?_⟩
      · change wordLength v ≤ FiniteSequenceCoding.length (prefixCode A k)
        rw [hs.1]
        omega
      · exact (hr q hq).trans (hs.2 q (by omega)).symm
  have hex : (∃ v < k, ValidCode v ∧ v ∈ EffectiveEnumerations.stage e k ∧
      Prefix v (prefixCode A k)) ↔ WatchSuccess A e k := by
    constructor
    · rintro ⟨v, hvk, hv, hs, hp⟩
      exact ⟨v, hvk, hv, hs, (hiff v hvk).mp hp⟩
    · rintro ⟨v, hvk, hv, hs, hr⟩
      exact ⟨v, hvk, hv, hs, (hiff v hvk).mpr hr⟩
  simp only [watchTestCode, eval, identity_eval, Nat.unpair_pair, prefix_collector_eval,
    Part.bind_some, Part.map_some, eval_embed, watchFiniteTestCode, ordinaryCode_eval]
  simp only [watchFiniteTest, Nat.unpair_pair, hex]

theorem prefix_recognizer_index_primitive : Primrec prefixRecognizerIndex := by
  apply (compIndex_primitive.comp (Primrec.const (encodeCode prefixRecognizerCode)) constantIndex_primitive).of_eq
  intro e
  simp only [prefixRecognizerIndex, encodeCode, compIndex, constantIndex]

theorem prefix_recognizer_eval (A : Set ℕ) (e x : ℕ) :
    OracleProgramNumberings.phi A (prefixRecognizerIndex e) x =
      Nat.rfind (fun k => Part.some (decide (WatchSuccess A e k))) := by
  simp only [OracleProgramNumberings.phi, prefixRecognizerIndex, decode_encode, eval,
    constant_eval, Part.bind_some, prefixRecognizerCode, identity_eval, Part.map_some,
    Nat.unpair_pair, Nat.add_zero, watch_test_eval]
  rw [Part.map_id' (fun _ => rfl)]
  congr 1
  funext k
  by_cases h : WatchSuccess A e k <;> simp [h]

theorem prefix_recognizer_domain (A : Set ℕ) (e x : ℕ) :
    (OracleProgramNumberings.phi A (prefixRecognizerIndex e) x).Dom ↔ Meets A (wordSet e) := by
  rw [prefix_recognizer_eval]
  have he : (∃ k, WatchSuccess A e k) ↔ Meets A (wordSet e) := by
    constructor
    · rintro ⟨k, v, _, hv, hs, hr⟩
      exact ⟨v, hv, hr, hv, (EffectiveEnumerations.stage_union _ _).mpr ⟨k, hs⟩⟩
    · rintro ⟨v, hv, hr, _, hi⟩
      obtain ⟨k, hk⟩ := (EffectiveEnumerations.stage_union _ _).mp hi
      exact ⟨k, v, hk.1, hv, hk, hr⟩
  simpa using he

theorem generic_iff_halting_decisions (G : Set ℕ) :
    IsOneGeneric G ↔ ∀ e x, ∃ u, ValidCode u ∧ Realizes u G ∧
      (ForcesHalting u e x ∨ ForcesDivergence u e x) := by
  constructor
  · intro hG e x
    rcases hG (haltingIndex e x) with ⟨u, hu, hr, hm⟩ | ⟨u, hu, hr, ha⟩
    · rw [halting_index_words] at hm
      exact ⟨u, hu, hr, Or.inl hm.2⟩
    · refine ⟨u, hu, hr, Or.inr ?_⟩
      intro v hv hp
      by_contra hn
      have hh : ForcesHalting v e x := by unfold ForcesHalting; omega
      apply ha v hv hp
      rw [halting_index_words]
      exact ⟨hv, hh⟩
  · intro hG e
    obtain ⟨u, hu, hr, hh | hd⟩ := hG (prefixRecognizerIndex e) 0
    · exact Or.inl ((prefix_recognizer_domain G e 0).mp (forces_halting_sound G u _ 0 hr hh))
    · refine Or.inr ⟨u, hu, hr, ?_⟩
      intro v hv hp hm
      have hvr : Realizes v (finiteOracle v) := prefix_finiteOracle (prefix_refl v)
      have hs : Meets (finiteOracle v) (wordSet e) := ⟨v, hv, hvr, hm⟩
      exact (forces_divergence_sound (finiteOracle v) u _ 0 (realizes_prefix hp hvr) hd)
        ((prefix_recognizer_domain _ e 0).mpr hs)

theorem convergence_iff_prefix (G : Set ℕ) (e x : ℕ) :
    (OracleProgramNumberings.phi G e x).Dom ↔
      ∃ u, ValidCode u ∧ Realizes u G ∧ ForcesHalting u e x := by
  constructor
  · intro hd
    obtain ⟨y, hy⟩ := Part.dom_iff_mem.mp hd
    have h0 : Realizes 0 G := by intro q hq; simp [wordLength, FiniteSequenceCoding.length] at hq
    obtain ⟨u, hu, _, hr, hc⟩ := valid_prefix_adequacy G 0 e x y h0 hy
    exact ⟨u, hu, hr, by unfold ForcesHalting; omega⟩
  · rintro ⟨u, _, hr, hh⟩
    exact forces_halting_sound G u e x hr hh

theorem generic_divergence_iff_prefix (G : Set ℕ) (hG : IsOneGeneric G) (e x : ℕ) :
    (¬ (OracleProgramNumberings.phi G e x).Dom) ↔
      ∃ u, ValidCode u ∧ Realizes u G ∧ ForcesDivergence u e x := by
  constructor
  · intro hd
    obtain ⟨u, hu, hr, hh | hv⟩ := (generic_iff_halting_decisions G).mp hG e x
    · exact (hd (forces_halting_sound G u e x hr hh)).elim
    · exact ⟨u, hu, hr, hv⟩
  · rintro ⟨u, _, hr, hd⟩
    exact forces_divergence_sound G u e x hr hd

theorem full_oracle_no_forcing_prefix :
    ∀ u, ValidCode u → Realizes u Set.univ →
      ¬ ForcesDivergence u (encodeCode Lemmatheca.Entry.OracleComputation.firstMissing)
        (Nat.pair 0 0) := by
  intro u _ hfull hd
  let A : Set ℕ := {q | q < wordLength u}
  have hr : Realizes u A := by
    intro q hq
    have h := hfull q hq
    simpa [A, indicator, hq] using h
  apply forces_divergence_sound A u _ (Nat.pair 0 0) hr hd
  simp only [OracleProgramNumberings.phi, decode_encode]
  rw [Lemmatheca.Entry.OracleComputation.firstMissing_truncated]
  trivial

end
end Lemmatheca.ComputabilityTheory.OneGenericSets
