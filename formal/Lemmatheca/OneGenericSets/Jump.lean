import Lemmatheca.OneGenericSets.Selector
import Lemmatheca.OneGenericSets.Construction
import Lemmatheca.OneGenericSets.Decisions

/-! The displayed all-oracle jump-search program and its generic correctness. -/
namespace Lemmatheca.ComputabilityTheory.OneGenericSets

open OracleComputation OracleProgramNumberings IncomparableTuringDegrees
  ComputableTreesAndPaths PostsTheorem UniversalComputation

set_option backward.isDefEq.respectTransparency false

noncomputable section
attribute [local instance] Classical.propDecidable

def evenOracle (A : Set ℕ) : Set ℕ := {x | 2 * x ∈ A}

def evenPrefix (A : Set ℕ) (n : ℕ) : ℕ := prefixCode (evenOracle A) n

def doubleInput (n : ℕ) : ℕ := 2 * n

theorem double_input_primitive : Primrec doubleInput := by
  exact Primrec.nat_mul.comp (Primrec.const 2) Primrec.id

def doubleInputCode : Nat.Partrec.Code :=
  ordinaryCode doubleInput (Primrec.nat_iff.mp double_input_primitive)

def evenQueryCode : Code := .comp .query (embed doubleInputCode)

/-- Input z = pair(e,n), output the word obtained from the even oracle answers. -/
def evenPrefixCode : Code := .comp (subst evenQueryCode prefixCollectorCode) .right

def jumpParameterCode : Code := .pair identityCode evenPrefixCode

/-- Input p = pair(pair(e,n),u). -/
def jumpQuestion (p : ℕ) : ℕ :=
  2 * testIndex (haltingIndex p.unpair.1.unpair.1 p.unpair.1.unpair.1) p.unpair.2 + 1

/-- Input pair(p,b), where b is the odd-position query answer. -/
def jumpCombineTest (z : ℕ) : ℕ :=
  if 0 < certificateValue z.unpair.1.unpair.2 z.unpair.1.unpair.1.unpair.1
      z.unpair.1.unpair.1.unpair.1 ∨ z.unpair.2 = 0 then 0 else 1

def jumpResult (p : ℕ) : ℕ :=
  if 0 < certificateValue p.unpair.2 p.unpair.1.unpair.1 p.unpair.1.unpair.1 then 1 else 0

theorem jump_question_primitive : Primrec jumpQuestion := by
  have hl : Primrec (fun z : ℕ => z.unpair.1) := Primrec.fst.comp Primrec.unpair
  have hr : Primrec (fun z : ℕ => z.unpair.2) := Primrec.snd.comp Primrec.unpair
  have he := hl.comp hl
  exact Primrec.nat_add.comp
    (Primrec.nat_mul.comp (Primrec.const 2)
      (test_index_primitive.comp (halting_index_primitive.comp he he) hr)) (Primrec.const 1)

theorem jump_combine_test_primitive : Primrec jumpCombineTest := by
  have hl : Primrec (fun z : ℕ => z.unpair.1) := Primrec.fst.comp Primrec.unpair
  have hr : Primrec (fun z : ℕ => z.unpair.2) := Primrec.snd.comp Primrec.unpair
  have he := hl.comp (hl.comp hl)
  have hc := IncomparableTuringDegrees.certificate_primitive.comp (((hr.comp hl).pair he).pair he)
  exact Primrec.ite
    ((Primrec.nat_lt.comp (Primrec.const 0) hc).or (Primrec.eq.comp hr (Primrec.const 0)))
    (Primrec.const 0) (Primrec.const 1)

theorem jump_result_primitive : Primrec jumpResult := by
  have hl : Primrec (fun z : ℕ => z.unpair.1) := Primrec.fst.comp Primrec.unpair
  have hr : Primrec (fun z : ℕ => z.unpair.2) := Primrec.snd.comp Primrec.unpair
  have he := hl.comp hl
  exact Primrec.ite
    (Primrec.nat_lt.comp (Primrec.const 0) (IncomparableTuringDegrees.certificate_primitive.comp ((hr.pair he).pair he)))
    (Primrec.const 1) (Primrec.const 0)

def jumpQuestionCode : Nat.Partrec.Code :=
  ordinaryCode jumpQuestion (Primrec.nat_iff.mp jump_question_primitive)
def jumpCombineTestCode : Nat.Partrec.Code :=
  ordinaryCode jumpCombineTest (Primrec.nat_iff.mp jump_combine_test_primitive)
def jumpResultCode : Nat.Partrec.Code :=
  ordinaryCode jumpResult (Primrec.nat_iff.mp jump_result_primitive)

/-- These are exactly T, V, U, j from the displayed human program. -/
def jumpTestCode : Code :=
  .comp (embed jumpCombineTestCode)
    (.pair jumpParameterCode
      (.comp .query (.comp (embed jumpQuestionCode) jumpParameterCode)))

def jumpOutputCode : Code := .comp (embed jumpResultCode) jumpParameterCode

def jumpSearchCode : Code := .comp (.find' jumpTestCode) (.pair identityCode .zero)

def genericJumpCode : Code := .comp jumpOutputCode (.pair identityCode jumpSearchCode)

def JumpDecision (A : Set ℕ) (e n : ℕ) : Prop :=
  ForcesHalting (evenPrefix A n) e e ∨
    2 * testIndex (haltingIndex e e) (evenPrefix A n) + 1 ∉ A

def genericJumpPartial (A : Set ℕ) (e : ℕ) : Part ℕ :=
  (Nat.rfind (fun n => Part.some (decide (JumpDecision A e n)))).map
    (fun n => if ForcesHalting (evenPrefix A n) e e then 1 else 0)

theorem even_prefix_eval (A : Set ℕ) (e n : ℕ) :
    eval A evenPrefixCode (Nat.pair e n) = Part.some (evenPrefix A n) := by
  have hq (q : ℕ) : eval A evenQueryCode q = Part.some (indicator (fun x => x ∈ evenOracle A) q) := by
    simp [evenQueryCode, eval, eval_embed, doubleInputCode, ordinaryCode_eval, doubleInput, evenOracle, indicator]
  change (eval A .right (Nat.pair e n)).bind (eval A (subst evenQueryCode prefixCollectorCode)) = _
  simp only [eval, Nat.unpair_pair, Part.bind_some]
  rw [subst_eval (evenOracle A) A evenQueryCode hq, prefix_collector_eval]
  rfl

theorem jump_test_eval (A : Set ℕ) (e n : ℕ) :
    eval A jumpTestCode (Nat.pair e n) = Part.some (if JumpDecision A e n then 0 else 1) := by
  have hp : eval A jumpParameterCode (Nat.pair e n) =
      Part.some (Nat.pair (Nat.pair e n) (evenPrefix A n)) := by
    simp [jumpParameterCode, eval, identity_eval, even_prefix_eval]
  simp only [jumpTestCode, eval, hp, Part.bind_some, eval_embed, jumpQuestionCode,
    jumpCombineTestCode, ordinaryCode_eval, Part.map_some, jumpQuestion, jumpCombineTest,
    Nat.unpair_pair]
  by_cases hh : ForcesHalting (evenPrefix A n) e e <;>
    by_cases hq : 2 * testIndex (haltingIndex e e) (evenPrefix A n) + 1 ∈ A <;>
      simp_all [JumpDecision, ForcesHalting, indicator]

theorem generic_jump_eval (A : Set ℕ) (e : ℕ) :
    eval A genericJumpCode e = genericJumpPartial A e := by
  have hU : eval A jumpSearchCode e =
      Nat.rfind (fun n => Part.some (decide (JumpDecision A e n))) := by
    simp only [jumpSearchCode, eval, identity_eval, Part.bind_some, Part.map_some,
      Nat.unpair_pair, Nat.add_zero, jump_test_eval]
    rw [Part.map_id' (fun _ => rfl)]
    congr 1
    funext n
    by_cases h : JumpDecision A e n <;> simp [h]
  have hV (n : ℕ) : eval A jumpOutputCode (Nat.pair e n) =
      Part.some (if ForcesHalting (evenPrefix A n) e e then 1 else 0) := by
    simp [jumpOutputCode, jumpParameterCode, eval, identity_eval, even_prefix_eval,
      eval_embed, jumpResultCode, ordinaryCode_eval, jumpResult, ForcesHalting]
  change (eval A (.pair identityCode jumpSearchCode) e).bind (eval A jumpOutputCode) = _
  rw [eval, identity_eval, Part.bind_some, hU, Part.bind_map]
  simp only [hV, Part.bind_some_eq_map]
  rfl

private theorem even_prefix_join (G : Set ℕ) (n : ℕ) :
    evenPrefix (TuringDegrees.join G haltingDiagonal) n = prefixCode G n := by
  have h : evenOracle (TuringDegrees.join G haltingDiagonal) = G := by
    ext x
    exact ((TuringDegrees.join_even_reduction G haltingDiagonal).2 x).symm
  rw [evenPrefix, h]

private theorem divergence_iff_no_extension (u e x : ℕ) (hu : ValidCode u) :
    ForcesDivergence u e x ↔ ¬ HasExtension (haltingIndex e x) u := by
  constructor
  · intro hd ⟨v, hp, hm⟩
    rw [normalize_valid u hu] at hp
    rw [halting_index_words] at hm
    have hz := hd v hm.1 hp
    have hh := hm.2
    unfold ForcesHalting at hh
    omega
  · intro hn v hv hp
    by_contra hz
    have hh : ForcesHalting v e x := by unfold ForcesHalting; omega
    apply hn
    refine ⟨v, ?_, ?_⟩
    · rwa [normalize_valid u hu]
    · rw [halting_index_words]
      exact ⟨hv, hh⟩

private theorem join_decision_iff (G : Set ℕ) (e n : ℕ) :
    JumpDecision (TuringDegrees.join G haltingDiagonal) e n ↔
      ForcesHalting (prefixCode G n) e e ∨ ForcesDivergence (prefixCode G n) e e := by
  unfold JumpDecision
  rw [even_prefix_join]
  have hq := (TuringDegrees.join_odd_reduction G haltingDiagonal).2
    (testIndex (haltingIndex e e) (prefixCode G n))
  have hn : (2 * testIndex (haltingIndex e e) (prefixCode G n) + 1 ∉
      TuringDegrees.join G haltingDiagonal) ↔ ¬ HasExtension (haltingIndex e e) (prefixCode G n) :=
    not_congr (hq.symm.trans (test_index_correct _ _))
  rw [hn, ← divergence_iff_no_extension _ e e (prefix_code_valid G n)]

theorem generic_jump_code_correct (G : Set ℕ) (hG : IsOneGeneric G) :
    TuringDegrees.Reduces genericJumpCode (TuringJump.jump G)
      (TuringDegrees.join G haltingDiagonal) := by
  intro e
  rw [generic_jump_eval]
  have hex : ∃ n, JumpDecision (TuringDegrees.join G haltingDiagonal) e n := by
    obtain ⟨u, hu, hr, hh⟩ := (generic_iff_halting_decisions G).mp hG e e
    have hs := prefixCode_spec G (wordLength u)
    have hp : Prefix u (prefixCode G (wordLength u)) :=
      ⟨by change wordLength u ≤ FiniteSequenceCoding.length (prefixCode G (wordLength u)); rw [hs.1],
        fun q hq => (hr q hq).trans (hs.2 q hq).symm⟩
    apply Exists.intro (wordLength u)
    apply (join_decision_iff G e (wordLength u)).mpr
    rcases hh with hh | hd
    · exact Or.inl ((forcing_persists _ _ e e hp).1 hh)
    · exact Or.inr ((forcing_persists _ _ e e hp).2 hd)
  let result := Nat.rfind (fun n => Part.some (decide
    (JumpDecision (TuringDegrees.join G haltingDiagonal) e n)))
  have hdom : result.Dom := by simpa [result] using hex
  obtain ⟨n, hn⟩ := Part.dom_iff_mem.mp hdom
  have hgood := Nat.rfind_spec hn
  have hd : ForcesHalting (prefixCode G n) e e ∨ ForcesDivergence (prefixCode G n) e e := by
    apply (join_decision_iff G e n).mp
    simpa [result] using hgood
  change result.map (fun n => if ForcesHalting (evenPrefix (TuringDegrees.join G haltingDiagonal) n) e e then 1 else 0) = _
  rw [Part.eq_some_iff.mpr hn, Part.map_some, even_prefix_join]
  have hreal : Realizes (prefixCode G n) G := by
    intro q hq
    exact (prefixCode_spec G n).2 q (by rw [← (prefixCode_spec G n).1]; exact hq)
  by_cases hh : ForcesHalting (prefixCode G n) e e
  · have hm : e ∈ TuringJump.jump G :=
      forces_halting_sound G _ e e hreal hh
    simp [hh, indicator, hm]
  · have hv := hd.resolve_left hh
    have hm : e ∉ TuringJump.jump G :=
      forces_divergence_sound G _ e e hreal hv
    simp [hh, indicator, hm]

theorem generalized_low (G : Set ℕ) (hG : IsOneGeneric G) :
    TuringDegrees.Equivalent (TuringJump.jump G) (TuringDegrees.join G haltingDiagonal) := by
  have h0 : TuringDegrees.Reducible ∅ G :=
    ⟨.zero, fun x => by simp [eval, indicator]⟩
  have hKG : TuringDegrees.Reducible haltingDiagonal (TuringJump.jump G) :=
    TuringDegrees.manyOne_imp_reducible
      (TuringJump.empty_jump_equiv_halting.2.trans (TuringJump.jump_monotone h0))
  exact ⟨⟨genericJumpCode, generic_jump_code_correct G hG⟩,
    (TuringDegrees.join_reducible_iff _ _ _).mpr ⟨(TuringJump.jump_strict G).1, hKG⟩⟩

theorem constructed_low (rho : ℕ) :
    TuringDegrees.Equivalent (TuringJump.jump (constructedSet rho)) haltingDiagonal := by
  have hGL := generalized_low (constructedSet rho) (constructed_generic rho)
  have hjoin : TuringDegrees.Reducible (TuringDegrees.join (constructedSet rho) haltingDiagonal) haltingDiagonal :=
    (TuringDegrees.join_reducible_iff _ _ _).mpr
      ⟨constructed_bound rho, TuringDegrees.reducible_refl _⟩
  have hKjoin : TuringDegrees.Reducible haltingDiagonal (TuringDegrees.join (constructedSet rho) haltingDiagonal) :=
    TuringDegrees.manyOne_imp_reducible ⟨_, (TuringDegrees.join_odd_reduction (constructedSet rho) haltingDiagonal).1.to_comp,
      (TuringDegrees.join_odd_reduction (constructedSet rho) haltingDiagonal).2⟩
  exact ⟨TuringDegrees.reducible_trans hGL.1 hjoin, TuringDegrees.reducible_trans hKjoin hGL.2⟩

theorem constructed_strict_bounds (rho : ℕ) :
    TuringDegrees.Reducible ∅ (constructedSet rho) ∧
      ¬ TuringDegrees.Reducible (constructedSet rho) ∅ ∧
      TuringDegrees.Reducible (constructedSet rho) haltingDiagonal ∧
      ¬ TuringDegrees.Reducible haltingDiagonal (constructedSet rho) := by
  refine ⟨⟨.zero, fun x => by simp [eval, indicator]⟩, ?_, constructed_bound rho, ?_⟩
  · intro h
    exact generic_noncomputable _ (constructed_generic rho)
      ((TuringDegrees.reducible_empty_iff _).mp h)
  · intro h
    exact (TuringJump.jump_strict (constructedSet rho)).2
      (TuringDegrees.reducible_trans (constructed_low rho).1 h)

end
end Lemmatheca.ComputabilityTheory.OneGenericSets
