import Lemmatheca.OneGenericSets.Basic

/-! One deterministic ordinary extension search and the displayed actual selector program. -/
namespace Lemmatheca.ComputabilityTheory.OneGenericSets

open OracleComputation OracleProgramNumberings IncomparableTuringDegrees
  ComputableTreesAndPaths PostsTheorem UniversalComputation

set_option backward.isDefEq.respectTransparency false

noncomputable section
attribute [local instance] Classical.propDecidable

/-- p = pair(e,u); t = pair(v,s). Only valid candidate word codes enter the search. -/
def Candidate (p t : ℕ) : Prop :=
  ValidCode t.unpair.1 ∧ Prefix (normalize p.unpair.2) t.unpair.1 ∧
    t.unpair.1 ∈ EffectiveEnumerations.stage p.unpair.1 t.unpair.2

def HasExtension (e u : ℕ) : Prop :=
  ∃ v, Prefix (normalize u) v ∧ v ∈ wordSet e

def searchPartial (p : ℕ) : Part ℕ :=
  Nat.rfind (fun t => Part.some (@decide (Candidate p t) (Classical.propDecidable _)))

theorem candidate_primitive : PrimrecPred (fun p : ℕ × ℕ => Candidate p.1 p.2) := by
  have he : Primrec (fun z : ℕ × ℕ => z.1.unpair.1) :=
    (Primrec.fst.comp Primrec.unpair).comp Primrec.fst
  have hu : Primrec (fun z : ℕ × ℕ => z.1.unpair.2) :=
    (Primrec.snd.comp Primrec.unpair).comp Primrec.fst
  have hv : Primrec (fun z : ℕ × ℕ => z.2.unpair.1) :=
    (Primrec.fst.comp Primrec.unpair).comp Primrec.snd
  have hs : Primrec (fun z : ℕ × ℕ => z.2.unpair.2) :=
    (Primrec.snd.comp Primrec.unpair).comp Primrec.snd
  exact (valid_code_primitive.comp hv).and
    ((prefix_primitive.comp ((normalize_primitive.comp hu).pair hv)).and
      (EffectiveEnumerations.stage_predicate_primitive.comp ((he.pair hs).pair hv)))

theorem candidate_exists_iff (e u : ℕ) :
    (∃ t, Candidate (Nat.pair e u) t) ↔ HasExtension e u := by
  constructor
  · rintro ⟨t, hv, hp, hs⟩
    refine ⟨t.unpair.1, ?_, hv, ?_⟩
    · simpa only [Nat.unpair_pair] using hp
    · exact (EffectiveEnumerations.stage_union _ _).mpr ⟨t.unpair.2, by simpa only [Nat.unpair_pair] using hs⟩
  · rintro ⟨v, hp, hv, hi⟩
    obtain ⟨k, hk⟩ := (EffectiveEnumerations.stage_union _ _).mp hi
    exact ⟨Nat.pair v k, by simpa only [Candidate, Nat.unpair_pair] using And.intro hv (And.intro hp hk)⟩

theorem search_recursive : Nat.Partrec searchPartial := by
  have hc : Computable₂ (fun p t => decide (Candidate p t)) :=
    candidate_primitive.decide.to_comp
  exact Partrec.nat_iff.mp (Partrec.rfind hc.partrec₂)

def searchCode : Nat.Partrec.Code :=
  Classical.choose (Nat.Partrec.Code.exists_code.mp search_recursive)

def searchIndex : ℕ := Encodable.encode searchCode

/-- This is q(e,u) from the human entry; the runtime argument is ignored. -/
def testIndex (e u : ℕ) : ℕ := TuringJump.ordinaryFreeze searchIndex (Nat.pair e u)

def selectedCandidate (e u : ℕ) : ℕ :=
  if h : ∃ t, Candidate (Nat.pair e u) t then Nat.find h else 0

/-- Exact H: unchanged normalized input in the negative branch, least pair-candidate otherwise. -/
def H (e u : ℕ) : ℕ :=
  if HasExtension e u then (selectedCandidate e u).unpair.1 else normalize u

theorem search_code_eval (p : ℕ) : searchCode.eval p = searchPartial p := by
  exact congrFun (Classical.choose_spec (Nat.Partrec.Code.exists_code.mp search_recursive)) p

theorem test_index_primitive : Primrec₂ testIndex := by
  exact TuringJump.ordinary_freeze_primitive.comp₂ (Primrec₂.const searchIndex) Primrec₂.natPair

theorem test_index_eval (e u x : ℕ) :
    UniversalComputation.phi (testIndex e u) x = searchPartial (Nat.pair e u) := by
  rw [testIndex, TuringJump.ordinary_freeze_eval]
  simp only [UniversalComputation.phi, searchIndex, Denumerable.ofNat_encode]
  exact search_code_eval _

theorem search_domain (e u : ℕ) :
    (searchPartial (Nat.pair e u)).Dom ↔ HasExtension e u := by
  simpa [searchPartial] using candidate_exists_iff e u

theorem selected_candidate_spec (e u : ℕ) (h : HasExtension e u) :
    Candidate (Nat.pair e u) (selectedCandidate e u) ∧
      ∀ t < selectedCandidate e u, ¬ Candidate (Nat.pair e u) t := by
  have hex := (candidate_exists_iff e u).mpr h
  simpa only [selectedCandidate, dite_eq_left hex] using
    (show Candidate (Nat.pair e u) (Nat.find hex) ∧
      ∀ t < Nat.find hex, ¬ Candidate (Nat.pair e u) t from
      ⟨Nat.find_spec hex, fun _ ht => Nat.find_min hex ht⟩)

theorem test_index_correct (e u : ℕ) :
    testIndex e u ∈ haltingDiagonal ↔ HasExtension e u := by
  change (UniversalComputation.phi (testIndex e u) (testIndex e u)).Dom ↔ _
  rw [test_index_eval, search_domain]

/-- z = pair(a,t), a = pair(pair(e,u),b). -/
def selectorTest (z : ℕ) : ℕ :=
  if (z.unpair.1.unpair.2 = 0 ∧ z.unpair.2 = 0) ∨
      (z.unpair.1.unpair.2 = 1 ∧ Candidate z.unpair.1.unpair.1 z.unpair.2)
    then 0 else 1

def selectorOutput (z : ℕ) : ℕ :=
  if z.unpair.1.unpair.2 = 0 then normalize z.unpair.1.unpair.1.unpair.2
  else z.unpair.2.unpair.1

def queryInput (z : ℕ) : ℕ := testIndex z.unpair.1 z.unpair.2

theorem selector_test_primitive : Primrec selectorTest := by
  have ha : Primrec (fun z : ℕ => z.unpair.1) := Primrec.fst.comp Primrec.unpair
  have ht : Primrec (fun z : ℕ => z.unpair.2) := Primrec.snd.comp Primrec.unpair
  have hp := ha.comp ha
  have hb := ht.comp ha
  have hzero := (Primrec.eq.comp hb (Primrec.const 0)).and
    (Primrec.eq.comp ht (Primrec.const 0))
  have hone := (Primrec.eq.comp hb (Primrec.const 1)).and
    (candidate_primitive.comp (hp.pair ht))
  exact Primrec.ite (hzero.or hone) (Primrec.const 0) (Primrec.const 1)

theorem selector_output_primitive : Primrec selectorOutput := by
  have hl : Primrec (fun z : ℕ => z.unpair.1) := Primrec.fst.comp Primrec.unpair
  have hr : Primrec (fun z : ℕ => z.unpair.2) := Primrec.snd.comp Primrec.unpair
  exact Primrec.ite (Primrec.eq.comp (hr.comp hl) (Primrec.const 0))
    (normalize_primitive.comp (hr.comp (hl.comp hl))) (hl.comp hr)

theorem query_input_primitive : Primrec queryInput := by
  exact test_index_primitive.comp (Primrec.fst.comp Primrec.unpair) (Primrec.snd.comp Primrec.unpair)

def selectorTestCode : Nat.Partrec.Code :=
  ordinaryCode selectorTest (Primrec.nat_iff.mp selector_test_primitive)

def selectorOutputCode : Nat.Partrec.Code :=
  ordinaryCode selectorOutput (Primrec.nat_iff.mp selector_output_primitive)

def queryInputCode : Nat.Partrec.Code :=
  ordinaryCode queryInput (Primrec.nat_iff.mp query_input_primitive)

/-- R, L and h are exactly the displayed human program trees. -/
def selectorParameterCode : Code :=
  .pair identityCode (.comp .query (embed queryInputCode))

def selectorSearchCode : Code :=
  .comp (.find' (embed selectorTestCode)) (.pair selectorParameterCode .zero)

def selectorCode : Code :=
  .comp (embed selectorOutputCode) (.pair selectorParameterCode selectorSearchCode)

/-- The full behavior with arbitrary oracle answer b, including possible false-positive divergence. -/
def selectorPartial (a : ℕ) : Part ℕ :=
  (Nat.rfind (fun t => Part.some (@decide
    ((a.unpair.2 = 0 ∧ t = 0) ∨ (a.unpair.2 = 1 ∧ Candidate a.unpair.1 t))
    (Classical.propDecidable _)))).map (fun t => selectorOutput (Nat.pair a t))

theorem selector_eval (A : Set ℕ) (e u : ℕ) :
    eval A selectorCode (Nat.pair e u) = selectorPartial
      (Nat.pair (Nat.pair e u) (indicator (fun q => q ∈ A) (testIndex e u))) := by
  let p := Nat.pair e u
  let b := indicator (fun q => q ∈ A) (testIndex e u)
  let a := Nat.pair p b
  let Good (t : ℕ) := (b = 0 ∧ t = 0) ∨ (b = 1 ∧ Candidate p t)
  let result := Nat.rfind (fun t => Part.some (decide (Good t)))
  have hR : eval A selectorParameterCode p = Part.some a := by
    simp [selectorParameterCode, eval, identity_eval, eval_embed, queryInputCode,
      ordinaryCode_eval, p, a, b, queryInput]
  have hf : eval A (.find' (embed selectorTestCode)) (Nat.pair a 0) = result := by
    simp only [eval, Nat.unpair_pair, Nat.add_zero, eval_embed, selectorTestCode,
      ordinaryCode_eval, Part.map_some]
    rw [Part.map_id' (fun _ => rfl)]
    congr 1
    funext t
    by_cases h : Good t <;> simp [selectorTest, a, Good, h]
  have hStart : eval A (.pair selectorParameterCode .zero) p = Part.some (Nat.pair a 0) := by
    rw [eval, hR, Part.bind_some]
    rfl
  have hL : eval A selectorSearchCode p = result := by
    change (eval A (.pair selectorParameterCode .zero) p).bind
      (eval A (.find' (embed selectorTestCode))) = _
    rw [hStart, Part.bind_some, hf]
  change (eval A (.pair selectorParameterCode selectorSearchCode) p).bind
    (eval A (embed selectorOutputCode)) = _
  rw [eval, hR, Part.bind_some, hL, Part.bind_map]
  simp only [eval_embed, selectorOutputCode, ordinaryCode_eval, Part.bind_some_eq_map]
  simp only [selectorPartial, a, p, b, result, Good, Nat.unpair_pair]

theorem selector_code_eval (e u : ℕ) :
    eval haltingDiagonal selectorCode (Nat.pair e u) = Part.some (H e u) := by
  rw [selector_eval]
  by_cases h : HasExtension e u
  · have hb : indicator (fun q => q ∈ haltingDiagonal) (testIndex e u) = 1 := by
      simp [indicator, (test_index_correct e u).mpr h]
    rw [hb]
    have hs : searchPartial (Nat.pair e u) = Part.some (selectedCandidate e u) := by
      apply Part.eq_some_iff.mpr
      apply Nat.mem_rfind.mpr
      exact ⟨by simp [(selected_candidate_spec e u h).1],
        fun {t} ht => by simp [(selected_candidate_spec e u h).2 t ht]⟩
    simpa [selectorPartial, selectorOutput, Nat.unpair_pair, H, h, searchPartial]
      using congrArg (fun p : Part ℕ => p.map (fun t => t.unpair.1)) hs
  · have hn : testIndex e u ∉ haltingDiagonal := fun hm => h ((test_index_correct e u).mp hm)
    have hb : indicator (fun q => q ∈ haltingDiagonal) (testIndex e u) = 0 := by
      simp [indicator, hn]
    rw [hb]
    have hs : Nat.rfind (fun t => Part.some (decide (t = 0))) = Part.some 0 := by
      apply Part.eq_some_iff.mpr
      exact Nat.mem_rfind.mpr ⟨by simp, fun {t} ht => by omega⟩
    simpa [selectorPartial, selectorOutput, H, h] using
      congrArg (fun p : Part ℕ => p.map (fun _ => normalize u)) hs

theorem H_spec (e u : ℕ) :
    ValidCode (H e u) ∧ Prefix (normalize u) (H e u) ∧
      H e u ∈ densification (wordSet e) := by
  by_cases h : HasExtension e u
  · have hc := (selected_candidate_spec e u h).1
    simp only [Candidate, Nat.unpair_pair] at hc
    have he : H e u = (selectedCandidate e u).unpair.1 := ite_eq_left h
    rw [he]
    have hm : (selectedCandidate e u).unpair.1 ∈ wordSet e :=
      ⟨hc.1, (EffectiveEnumerations.stage_union _ _).mpr ⟨_, hc.2.2⟩⟩
    exact ⟨hc.1, hc.2.1, hc.1, Or.inl hm⟩
  · rw [H, ite_eq_right h]
    refine ⟨(normalize_spec u).1, prefix_refl _, (normalize_spec u).1, Or.inr ?_⟩
    intro v _ hp hm
    exact h ⟨v, hp, hm⟩

theorem H_positive (e u : ℕ) (h : HasExtension e u) :
    H e u = (selectedCandidate e u).unpair.1 ∧ H e u ∈ wordSet e := by
  have hc := (selected_candidate_spec e u h).1
  simp only [Candidate, Nat.unpair_pair] at hc
  refine ⟨ite_eq_left h, ?_⟩
  rw [H, ite_eq_left h]
  exact ⟨hc.1, (EffectiveEnumerations.stage_union _ _).mpr ⟨_, hc.2.2⟩⟩

theorem H_negative (e u : ℕ) (h : ¬ HasExtension e u) :
    H e u = normalize u ∧ Avoids (normalize u) (wordSet e) := by
  rw [H, ite_eq_right h]
  refine ⟨rfl, ?_⟩
  intro v _ hp hm
  exact h ⟨v, hp, hm⟩

end
end Lemmatheca.ComputabilityTheory.OneGenericSets
