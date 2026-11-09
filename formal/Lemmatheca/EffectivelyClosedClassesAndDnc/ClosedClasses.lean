import Lemmatheca.ComputableTreesAndPaths.HaltingPath
import Lemmatheca.EffectiveEnumerations.Stages

/-! Effective binary classes and the common-current-length tree compiler. -/
namespace Lemmatheca.ComputabilityTheory.EffectivelyClosedClassesAndDnc

open ComputableTreesAndPaths IncomparableTuringDegrees PostsTheorem
open UniversalComputation EffectiveEnumerations

noncomputable section

private theorem prefix_length (X : Set ℕ) (n : ℕ) :
    wordLength (prefixCode X n) = n := (prefixCode_spec X n).1

def ForbiddenFamily (F : Set ℕ) : Prop :=
  (∀ u ∈ F, ValidCode u) ∧ REPred (fun u => u ∈ F)

def avoidance (F : Set ℕ) : Set (Set ℕ) :=
  {X | ∀ n, prefixCode X n ∉ F}

def EffectivelyClosed (P : Set (Set ℕ)) : Prop :=
  ∃ F, ForbiddenFamily F ∧ avoidance F = P

theorem avoidance_boundary :
    ForbiddenFamily ∅ ∧ avoidance ∅ = Set.univ ∧
      ∀ F : Set ℕ, 0 ∈ F → avoidance F = ∅ := by
  classical
  have hf : ComputablePred (fun _ : ℕ => False) :=
    Computable.computablePred (Computable.const false)
  refine ⟨⟨by simp, by simpa using hf.to_re⟩, ?_, ?_⟩
  · ext X
    simp [avoidance]
  · intro F hF
    ext X
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hX
    apply hX 0
    simpa [prefixCode, FiniteSequenceCoding.code] using hF

def commonStageTree (r : ℕ) : Set ℕ :=
  {u | ValidCode u ∧
    ∀ i ≤ wordLength u, takeCode i u ∉ stage r (wordLength u)}

def commonStageTest (r u : ℕ) : ℕ := indicator (fun v => v ∈ commonStageTree r) u

def commonStageInput (z : ℕ) : ℕ := commonStageTest z.unpair.1 z.unpair.2

theorem common_stage_input_primitive : Primrec commonStageInput := by
  classical
  have hr : Primrec (fun z : ℕ => z.unpair.1) := Primrec.fst.comp Primrec.unpair
  have hu : Primrec (fun z : ℕ => z.unpair.2) := Primrec.snd.comp Primrec.unpair
  have hl : Primrec (fun z : ℕ => wordLength z.unpair.2) :=
    FiniteSequenceCoding.primrec_length.comp hu
  have ht : Primrec (fun p : ℕ × ℕ => takeCode p.2 p.1.unpair.2) :=
    take_code_primitive.comp Primrec.snd (hu.comp Primrec.fst)
  have hm : PrimrecPred (fun p : ℕ × ℕ =>
      takeCode p.2 p.1.unpair.2 ∈ stage p.1.unpair.1 (wordLength p.1.unpair.2)) :=
    stage_predicate_primitive.comp
      (((hr.comp Primrec.fst).pair (hl.comp Primrec.fst)).pair ht)
  have hn : PrimrecRel (fun z : ℕ => fun i =>
      takeCode i z.unpair.2 ∉ stage z.unpair.1 (wordLength z.unpair.2)) := hm.not
  have hb := (PrimitiveRecursion.bounded_forall_primrec hn).comp Primrec.id
    (Primrec.succ.comp hl)
  have hp : PrimrecPred (fun z : ℕ => z.unpair.2 ∈ commonStageTree z.unpair.1) :=
    ((valid_code_primitive.comp hu).and hb).of_eq (fun z => by
      simp only [commonStageTree, Set.mem_ofPred_eq, Nat.lt_succ_iff, id_eq])
  exact (Primrec.ite hp (Primrec.const 1) (Primrec.const 0)).of_eq (fun z => by
    by_cases hz : z.unpair.2 ∈ commonStageTree z.unpair.1 <;>
      simp [commonStageInput, commonStageTest, indicator, hz])

def jointDeciderIndex : ℕ := Encodable.encode
  (OracleProgramNumberings.ordinaryCode commonStageInput
    (Primrec.nat_iff.mp common_stage_input_primitive))

def treeDeciderIndex (r : ℕ) : ℕ := UniversalComputation.specialize jointDeciderIndex r

theorem tree_decider_index_primitive : Primrec treeDeciderIndex := by
  exact UniversalComputation.specialize_primitive.comp
    (Primrec.const jointDeciderIndex) Primrec.id

theorem tree_decider_eval (r u : ℕ) :
    phi (treeDeciderIndex r) u = Part.some (commonStageTest r u) := by
  rw [treeDeciderIndex, UniversalComputation.specialize_eval]
  change Nat.Partrec.Code.eval (Denumerable.ofNat Nat.Partrec.Code
    (Encodable.encode (OracleProgramNumberings.ordinaryCode commonStageInput
      (Primrec.nat_iff.mp common_stage_input_primitive)))) (Nat.pair r u) = _
  rw [Denumerable.ofNat_encode, OracleProgramNumberings.ordinaryCode_eval]
  simp only [commonStageInput, Nat.unpair_pair]

theorem common_stage_test_spec (r u : ℕ) :
    (commonStageTest r u = 0 ∨ commonStageTest r u = 1) ∧
      (commonStageTest r u = 1 ↔ u ∈ commonStageTree r) := by
  classical
  by_cases h : u ∈ commonStageTree r <;> simp [commonStageTest, indicator, h]

theorem common_stage_computable (r : ℕ) :
    ComputablePred (fun u => u ∈ commonStageTree r) := by
  have hp : Primrec (fun u => commonStageInput (Nat.pair r u)) :=
    common_stage_input_primitive.comp (Primrec₂.natPair.comp (Primrec.const r) Primrec.id)
  exact (Primrec.eq.comp hp (Primrec.const 1)).computablePred.of_eq (fun u => by
    simpa only [commonStageInput, Nat.unpair_pair] using (common_stage_test_spec r u).2)

theorem common_stage_is_tree (r : ℕ) : IsBinaryTree (commonStageTree r) := by
  refine ⟨fun _ h => h.1, ?_⟩
  intro u v hu hv huv
  refine ⟨hu, fun i hi hmem => ?_⟩
  have he : takeCode i u = takeCode i v := by
    apply code_ext _ _ (take_valid _ _ hu) (take_valid _ _ hv.1)
    · rw [(take_spec i u hu).1, (take_spec i v hv.1).1,
        min_eq_left hi, min_eq_left (hi.trans huv.1)]
    · intro q hq
      have hqi : q < i := by
        rw [(take_spec i u hu).1, min_eq_left hi] at hq
        exact hq
      exact ((take_spec i u hu).2.2 q hq).trans
        ((huv.2 q (hqi.trans_le hi)).trans
          ((take_spec i v hv.1).2.2 q (by
            rw [(take_spec i v hv.1).1, min_eq_left (hi.trans huv.1)]
            exact hqi)).symm)
  apply hv.2 i (hi.trans huv.1)
  rw [← he]
  exact stage_monotone r huv.1 hmem


/-- The shared finite word restriction agrees with restricting the actual path prefix. -/
theorem take_prefix_code (X : Set ℕ) (i m : ℕ) (him : i ≤ m) :
    takeCode i (prefixCode X m) = prefixCode X i := by
  apply code_ext _ _ (take_valid _ _ (prefix_code_valid X m)) (prefix_code_valid X i)
  · rw [(take_spec _ _ (prefix_code_valid X m)).1,
      prefix_length X m, min_eq_left him, prefix_length X i]
  · intro q hq
    have hqi : q < i := by
      rw [(take_spec _ _ (prefix_code_valid X m)).1,
        prefix_length X m, min_eq_left him] at hq
      exact hq
    exact ((take_spec i (prefixCode X m) (prefix_code_valid X m)).2.2 q hq).trans
      (((prefixCode_spec X m).2 q (hqi.trans_le him)).trans
        ((prefixCode_spec X i).2 q hqi).symm)

theorem common_stage_paths (r : ℕ) :
    {X | Path (commonStageTree r) X} = avoidance (indexSet r) := by
  ext X
  constructor
  · intro hX i hi
    obtain ⟨k, hk⟩ := (stage_union r (prefixCode X i)).mp hi
    let m := max i k
    have him : i ≤ m := le_max_left _ _
    have hm : prefixCode X m ∈ commonStageTree r := hX m
    have he : takeCode i (prefixCode X m) = prefixCode X i := by
      apply code_ext _ _ (take_valid _ _ (prefix_code_valid X m)) (prefix_code_valid X i)
      · rw [(take_spec _ _ (prefix_code_valid X m)).1,
          prefix_length X m, min_eq_left him, prefix_length X i]
      · intro q hq
        have hqi : q < i := by
          rw [(take_spec _ _ (prefix_code_valid X m)).1,
            prefix_length X m, min_eq_left him] at hq
          exact hq
        exact ((take_spec i (prefixCode X m) (prefix_code_valid X m)).2.2 q hq).trans
          (((prefixCode_spec X m).2 q (hqi.trans_le him)).trans
            ((prefixCode_spec X i).2 q hqi).symm)
    apply hm.2 i (by rw [prefix_length X m]; exact him)
    rw [he, prefix_length X m]
    exact stage_monotone r (le_max_right _ _) hk
  · intro hX m
    refine ⟨prefix_code_valid X m, fun i hi hmem => ?_⟩
    have him : i ≤ m := by simpa only [prefix_length X m] using hi
    have he : takeCode i (prefixCode X m) = prefixCode X i := by
      apply code_ext _ _ (take_valid _ _ (prefix_code_valid X m)) (prefix_code_valid X i)
      · rw [(take_spec _ _ (prefix_code_valid X m)).1,
          prefix_length X m, min_eq_left him, prefix_length X i]
      · intro q hq
        have hqi : q < i := by
          rw [(take_spec _ _ (prefix_code_valid X m)).1,
            prefix_length X m, min_eq_left him] at hq
          exact hq
        exact ((take_spec i (prefixCode X m) (prefix_code_valid X m)).2.2 q hq).trans
          (((prefixCode_spec X m).2 q (hqi.trans_le him)).trans
            ((prefixCode_spec X i).2 q hqi).symm)
    exact hX i ((stage_union r _).mpr ⟨_, he ▸ hmem⟩)

def missingWords (T : Set ℕ) : Set ℕ := {u | ValidCode u ∧ u ∉ T}

theorem missing_words_computable (T : Set ℕ)
    (hc : ComputablePred (fun u => u ∈ T)) :
    ComputablePred (fun u => u ∈ missingWords T) ∧ ForbiddenFamily (missingWords T) := by
  classical
  have hp : ComputablePred (fun u => u ∈ missingWords T) :=
    Computable.computablePred
      ((Primrec.and.to_comp.comp valid_code_primitive.decide.to_comp hc.not.decide).of_eq
        (fun u => by
          by_cases hv : ValidCode u <;> by_cases ht : u ∈ T <;>
            simp [missingWords, hv, ht]))
  exact ⟨hp, ⟨fun _ h => h.1, hp.to_re⟩⟩

theorem missing_words_paths (T : Set ℕ) :
    avoidance (missingWords T) = {X | Path T X} := by
  ext X
  simp only [avoidance, missingWords, Set.mem_ofPred_eq, ComputableTreesAndPaths.Path]
  constructor
  · intro h n
    exact Classical.byContradiction (fun hn => h n ⟨prefix_code_valid X n, hn⟩)
  · intro h n hn
    exact hn.2 (h n)

theorem effectively_closed_iff_tree (P : Set (Set ℕ)) :
    EffectivelyClosed P ↔ ∃ T : Set ℕ, IsBinaryTree T ∧
      ComputablePred (fun u => u ∈ T) ∧ {X | Path T X} = P := by
  constructor
  · rintro ⟨F, hF, hP⟩
    obtain ⟨r, hr⟩ := (enumerable_iff_index (fun u => u ∈ F)).mp hF.2
    have he : indexSet r = F := by
      ext u
      exact (hr u).symm
    refine ⟨commonStageTree r, common_stage_is_tree r, common_stage_computable r, ?_⟩
    rw [common_stage_paths, he, hP]
  · rintro ⟨T, _, hc, hP⟩
    exact ⟨missingWords T, (missing_words_computable T hc).2,
      (missing_words_paths T).trans hP⟩

def CoCETree (T : Set ℕ) : Prop :=
  IsBinaryTree T ∧ REPred (fun u => u ∈ missingWords T)

theorem co_ce_tree_complement (T : Set ℕ) :
    CoCETree T ↔ IsBinaryTree T ∧ REPred (fun u => u ∉ T) := by
  constructor
  · rintro ⟨hT, hF⟩
    obtain ⟨R, hR, he⟩ := (enumerable_iff_primitive_certificate
      (fun u => u ∈ missingWords T)).mp hF
    refine ⟨hT, (enumerable_iff_primitive_certificate _).mpr
      ⟨fun u k => ¬ ValidCode u ∨ R u k,
        (valid_code_primitive.comp Primrec.fst).not.or hR, ?_⟩⟩
    intro u
    constructor
    · intro hu
      by_cases hv : ValidCode u
      · obtain ⟨k, hk⟩ := (he u).mp ⟨hv, hu⟩
        exact ⟨k, Or.inr hk⟩
      · exact ⟨0, Or.inl hv⟩
    · rintro ⟨k, hn | hk⟩
      · exact fun hu => hn (hT.1 u hu)
      · exact ((he u).mpr ⟨k, hk⟩).2
  · rintro ⟨hT, hF⟩
    obtain ⟨R, hR, he⟩ := (enumerable_iff_primitive_certificate
      (fun u => u ∉ T)).mp hF
    refine ⟨hT, (enumerable_iff_primitive_certificate _).mpr
      ⟨fun u k => ValidCode u ∧ R u k,
        (valid_code_primitive.comp Primrec.fst).and hR, ?_⟩⟩
    intro u
    simp only [missingWords, Set.mem_ofPred_eq, he u, exists_and_left]

theorem co_ce_conversion (T : Set ℕ) (r : ℕ)
    (hindex : indexSet r = missingWords T) :
    IsBinaryTree (commonStageTree r) ∧
      ComputablePred (fun u => u ∈ commonStageTree r) ∧
      ∀ X, Path (commonStageTree r) X ↔ Path T X := by
  refine ⟨common_stage_is_tree r, common_stage_computable r, ?_⟩
  have he := common_stage_paths r
  rw [hindex, missing_words_paths] at he
  intro X
  exact Set.ext_iff.mp he X

end
end Lemmatheca.ComputabilityTheory.EffectivelyClosedClassesAndDnc
