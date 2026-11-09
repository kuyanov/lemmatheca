import Lemmatheca.ComputableTreesAndPaths.HaltingPath

/-! Finite divergence restrictions and one fixed ordinary search compiler. -/
namespace Lemmatheca.ComputabilityTheory.LowBasisTheorem

open ComputableTreesAndPaths IncomparableTuringDegrees PostsTheorem
open UniversalComputation OracleProgramNumberings PaddingAndInjectiveReductions
open ProductiveAndCreativeSets

noncomputable section
set_option backward.isDefEq.respectTransparency false

def restricted (T : Set ℕ) (l : ℕ) : Set ℕ :=
  {u | u ∈ T ∧ ∀ j ∈ FiniteSequenceCoding.decode l, certificateValue u j j = 0}

def EmptyLevel (T : Set ℕ) (l m : ℕ) : Prop :=
  ∀ u ∈ binaryLevel m, u ∉ restricted T l

def Failed (T : Set ℕ) (l : ℕ) : Prop := ∃ m, EmptyLevel T l m

def emptyTest (T : Set ℕ) (l m : ℕ) : Bool := by
  classical
  exact decide (EmptyLevel T l m)

theorem restricted_computable (T : Set ℕ)
    (hc : ComputablePred (fun u => u ∈ T)) :
    ComputablePred (fun p : ℕ × ℕ => p.2 ∈ restricted T p.1) := by
  classical
  have hz : PrimrecRel (fun j u : ℕ => certificateValue u j j = 0) :=
    (Primrec.eq.comp
      (certificate_primitive.comp ((Primrec.snd.pair Primrec.fst).pair Primrec.fst))
      (Primrec.const 0))
  have hl : PrimrecPred (fun p : ℕ × ℕ =>
      ∀ j ∈ FiniteSequenceCoding.decode p.1, certificateValue p.2 j j = 0) :=
    hz.forall_mem_list.comp ((Primrec.ofNat (List ℕ)).comp Primrec.fst) Primrec.snd
  have h := (Primrec.dom_bool₂ Bool.and).to_comp.comp
    (hc.decide.comp Computable.snd) hl.decide.to_comp
  exact ⟨inferInstance, h.of_eq (fun _ => by simp only [restricted, Set.mem_ofPred_eq,
    Bool.decide_and])⟩

theorem restricted_tree (T : Set ℕ) (hT : IsBinaryTree T) (l : ℕ) :
    IsBinaryTree (restricted T l) := by
  refine ⟨fun u hu => hT.1 u hu.1, ?_⟩
  intro u v hu hv hp
  refine ⟨hT.2 u v hu hv.1 hp, fun j hj => ?_⟩
  by_contra hz
  obtain ⟨y, hy⟩ := Nat.exists_eq_succ_of_ne_zero hz
  have he := certificate_persists u v j j y hp hy
  have hzero := hv.2 j hj
  omega

theorem restricted_subsets (T : Set ℕ) (l e : ℕ) :
    restricted T (FiniteSequenceCoding.cons e l) ⊆ restricted T l ∧
      restricted T l ⊆ T := by
  have hd : FiniteSequenceCoding.decode (FiniteSequenceCoding.cons e l) =
      e :: FiniteSequenceCoding.decode l := by
    rw [← FiniteSequenceCoding.code_decode l, ← FiniteSequenceCoding.code_cons,
      FiniteSequenceCoding.decode_code, FiniteSequenceCoding.decode_code]
  exact ⟨fun u hu => ⟨hu.1, fun j hj => hu.2 j (by rw [hd]; simp [hj])⟩,
    fun _ hu => hu.1⟩

theorem restricted_zero (T : Set ℕ) : restricted T 0 = T := by
  ext u
  simp [restricted]

theorem restricted_paths (T : Set ℕ) (l : ℕ) (X : Set ℕ) :
    Path (restricted T l) X ↔ Path T X ∧
      ∀ j ∈ FiniteSequenceCoding.decode l, j ∉ TuringJump.jump X := by
  constructor
  · intro hX
    refine ⟨fun n => (hX n).1, ?_⟩
    intro j hj hhalt
    obtain ⟨y, hy⟩ := Part.dom_iff_mem.mp hhalt
    obtain ⟨u, hu, hc⟩ := (prefix_output_iff X j j y).mp hy
    let n := wordLength u
    have hp : Prefix u (prefixCode X n) :=
      ⟨(prefixCode_spec X n).1.ge,
        fun q hq => (hu q hq).trans ((prefixCode_spec X n).2 q hq).symm⟩
    have he := certificate_persists u (prefixCode X n) j j y hp hc
    have hz := (hX n).2 j hj
    omega
  · rintro ⟨hX, hd⟩ n
    refine ⟨hX n, fun j hj => ?_⟩
    by_contra hz
    obtain ⟨y, hy⟩ := Nat.exists_eq_succ_of_ne_zero hz
    have hr : Realizes (prefixCode X n) X := by
      intro q hq
      apply (prefixCode_spec X n).2 q
      simpa only [(prefixCode_spec X n).1] using hq
    exact hd j hj (Part.dom_iff_mem.mpr
      ⟨y, certificate_sound X _ j j y hr hy⟩)

theorem empty_test_computable (T : Set ℕ)
    (hc : ComputablePred (fun u => u ∈ T)) :
    Computable₂ (emptyTest T) := by
  classical
  have hb : Computable₂ (fun l u => decide (u ∈ restricted T l)) :=
    (restricted_computable T hc).decide
  have hm := (computable_list_map (fun l u => decide (u ∈ restricted T l)) hb).comp
    Computable.fst (binary_level_primitive.to_comp.comp Computable.snd)
  have hp : ComputablePred (fun p : ℕ × ℕ => ∀ b ∈
      (binaryLevel p.2).map (fun u => decide (u ∈ restricted T p.1)), b = false) :=
    (((Primrec.eq.comp (Primrec.id : Primrec (fun b : Bool => b))
      (Primrec.const false)).forall_mem_list).decide.to_comp.comp hm).computablePred
  have he : ComputablePred (fun p : ℕ × ℕ => EmptyLevel T p.1 p.2) :=
    hp.of_eq (fun _ => by simp [EmptyLevel])
  exact he.decide

theorem empty_level_iff (T : Set ℕ) (hT : IsBinaryTree T) (l m : ℕ) :
    EmptyLevel T l m ↔ ¬ HasLevel (restricted T l) m := by
  constructor
  · rintro he ⟨u, hu, hl⟩
    exact he u ((binary_level_spec m u).mpr ⟨hT.1 u hu.1, hl⟩) hu
  · intro he u hu hmem
    exact he ⟨u, hmem, ((binary_level_spec m u).mp hu).2⟩

theorem failed_iff (T : Set ℕ) (hT : IsBinaryTree T) (l : ℕ) :
    Failed T l ↔ ¬ ∃ X, Path (restricted T l) X := by
  classical
  rw [← all_levels_path (restricted T l) (restricted_tree T hT l)]
  simp only [Failed, empty_level_iff T hT l, not_forall]

def failureSearch (T : Set ℕ) (l : ℕ) : Part ℕ :=
  (Nat.rfind fun m => Part.some (emptyTest T l m)).map (fun _ => 0)

theorem failure_search_recursive (T : Set ℕ)
    (hc : ComputablePred (fun u => u ∈ T)) :
    Nat.Partrec (failureSearch T) := by
  exact Partrec.nat_iff.mp
    ((Partrec.rfind (empty_test_computable T hc).partrec₂).map (Computable.const 0).to₂)

theorem failure_search_domain (T : Set ℕ) (l : ℕ) :
    (failureSearch T l).Dom ↔ Failed T l := by
  classical
  simp [failureSearch, Failed, emptyTest]

def failureCode (T : Set ℕ) (hc : ComputablePred (fun u => u ∈ T)) :
    Nat.Partrec.Code :=
  Classical.choose (Nat.Partrec.Code.exists_code.mp (failure_search_recursive T hc))

def failureIndex (T : Set ℕ) (hc : ComputablePred (fun u => u ∈ T)) : ℕ :=
  Encodable.encode (failureCode T hc)

def failureQuery (T : Set ℕ) (hc : ComputablePred (fun u => u ∈ T)) (l : ℕ) : ℕ :=
  enumerableMap ComputableTreesAndPaths.constantRunIndex (failureIndex T hc) l

theorem failure_code_eval (T : Set ℕ) (hc : ComputablePred (fun u => u ∈ T)) (l : ℕ) :
    UniversalComputation.phi (failureIndex T hc) l = failureSearch T l := by
  unfold UniversalComputation.phi failureIndex
  rw [Denumerable.ofNat_encode]
  exact congrFun (Classical.choose_spec
    (Nat.Partrec.Code.exists_code.mp (failure_search_recursive T hc))) l

theorem failure_query_primitive (T : Set ℕ)
    (hc : ComputablePred (fun u => u ∈ T)) : Primrec (failureQuery T hc) := by
  exact enumerableMap_primitive _ _

theorem failure_query_correct (T : Set ℕ)
    (hc : ComputablePred (fun u => u ∈ T)) (l : ℕ) :
    failureQuery T hc l ∈ haltingDiagonal ↔ Failed T l := by
  have hv : ConstantRunIndex ComputableTreesAndPaths.constantRunIndex :=
    Classical.choose_spec constant_run_index_exists
  rw [failureQuery, ← enumerableMap_membership _ hv]
  change (UniversalComputation.phi (failureIndex T hc) l).Dom ↔ _
  rw [failure_code_eval, failure_search_domain]

end
end Lemmatheca.ComputabilityTheory.LowBasisTheorem
