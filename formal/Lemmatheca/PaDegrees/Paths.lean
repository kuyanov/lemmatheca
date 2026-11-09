import Lemmatheca.PaDegrees.TreeRace

set_option autoImplicit false

namespace Lemmatheca.ComputabilityTheory.PaDegrees

open UniversalComputation TuringDegrees OracleComputation EffectivelyClosedClassesAndDnc
open ComputableTreesAndPaths IncomparableTuringDegrees BusyBeaverFunctions OracleProgramNumberings PostsTheorem

noncomputable section

def selectedTreeWord (t : ℕ) (D : Set ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => appendBit (selectedTreeWord t D n)
      (branchSelector t D (selectedTreeWord t D n))

def selectedTreeBit (t : ℕ) (D : Set ℕ) (n : ℕ) : ℕ :=
  branchSelector t D (selectedTreeWord t D n)

def selectedTreePath (t : ℕ) (D : Set ℕ) : Set ℕ := {n | selectedTreeBit t D n = 1}

private theorem tree_pair_map_computable (t : ℕ) : Computable (treePairMap t) := by
  exact (tree_pair_map_primitive.comp (Primrec.const t) Primrec.id).to_comp

private def treeQueryCode (t : ℕ) : OracleComputation.Code :=
  .comp .query (embed (ordinaryProgram (treePairMap t) (tree_pair_map_computable t)))

private def treeStepCode (t : ℕ) : OracleComputation.Code :=
  .comp (embed appendPairCode) (.pair identityCode (treeQueryCode t))

/-- This one finite program is fixed by the tree-decider index, before D varies. -/
def treeWordsProgram (t : ℕ) : OracleComputation.Code :=
  .comp (.prec .zero (.comp (treeStepCode t) (.comp .right .right)))
    (.pair .zero identityCode)

def treePathProgram (t : ℕ) : OracleComputation.Code :=
  .comp (treeQueryCode t) (treeWordsProgram t)

private theorem tree_query_eval (t : ℕ) (D : Set ℕ) (u : ℕ) :
    eval D (treeQueryCode t) u = Part.some (branchSelector t D u) := by
  simp [treeQueryCode, eval, eval_embed, ordinaryProgram_eval, branchSelector]

private theorem tree_step_eval (t : ℕ) (D : Set ℕ) (u : ℕ) :
    eval D (treeStepCode t) u = Part.some (appendBit u (branchSelector t D u)) := by
  simp [treeStepCode, eval, identity_eval, tree_query_eval, eval_embed,
    appendPairCode, ordinaryCode_eval]

theorem tree_words_program_eval (t : ℕ) (D : Set ℕ) (n : ℕ) :
    eval D (treeWordsProgram t) n = Part.some (selectedTreeWord t D n) := by
  have hw (k : ℕ) : eval D
      (.prec .zero (.comp (treeStepCode t) (.comp .right .right))) (Nat.pair 0 k) =
      Part.some (selectedTreeWord t D k) := by
    induction k with
    | zero => simp [eval, selectedTreeWord]
    | succ k ih =>
      rw [eval_prec_succ, ih, Part.bind_some]
      change (eval D (.comp .right .right)
        (Nat.pair 0 (Nat.pair k (selectedTreeWord t D k)))).bind
          (eval D (treeStepCode t)) = _
      simp only [eval, Nat.unpair_pair, Part.bind_some]
      exact tree_step_eval t D _
  simpa only [treeWordsProgram, eval, identity_eval, Part.bind_some,
    Part.map_some] using hw n

theorem tree_path_program_eval (t : ℕ) (D : Set ℕ) (n : ℕ) :
    eval D (treePathProgram t) n = Part.some (selectedTreeBit t D n) := by
  simp only [treePathProgram, eval, tree_words_program_eval, Part.bind_some]
  exact tree_query_eval t D _

theorem tree_path_program_reduces (t : ℕ) (D : Set ℕ) :
    Reduces (treePathProgram t) (selectedTreePath t D) D := by
  classical
  intro n
  rw [tree_path_program_eval]
  congr 1
  unfold selectedTreePath selectedTreeBit branchSelector
  by_cases h : treePairMap t (selectedTreeWord t D n) ∈ D <;> simp [indicator, h]

theorem selected_tree_words_correct (t : ℕ) (T : Set ℕ) (ht : TreeDeciderIndex t T)
    (hT : IsBinaryTree T) (hne : ∃ X, Path T X) (D : Set ℕ)
    (hD : D ∈ binaryDNCClass) (n : ℕ) :
    ValidCode (selectedTreeWord t D n) ∧ wordLength (selectedTreeWord t D n) = n ∧
      Extendible T (selectedTreeWord t D n) ∧
      Prefix (selectedTreeWord t D n) (selectedTreeWord t D (n + 1)) ∧
      selectedTreeWord t D n = prefixCode (selectedTreePath t D) n := by
  have hz : Extendible T 0 := by
    obtain ⟨X, hX⟩ := hne
    intro m hm
    have hzlen : wordLength 0 = 0 := by simp [wordLength, FiniteSequenceCoding.length]
    have hlevel : prefixCode X m ∈ binaryLevel (wordLength 0 + m) := by
      rw [hzlen, Nat.zero_add]
      exact (binary_level_spec m _).mpr ⟨prefix_code_valid X m, (prefixCode_spec X m).1⟩
    apply hm (prefixCode X m) hlevel (hX m)
    refine ⟨by rw [hzlen]; exact Nat.zero_le _, ?_⟩
    intro q hq
    simp [wordLength, FiniteSequenceCoding.length] at hq
  have hi : ∀ k, ValidCode (selectedTreeWord t D k) ∧
      wordLength (selectedTreeWord t D k) = k ∧ Extendible T (selectedTreeWord t D k) := by
    intro k
    induction k with
    | zero => exact ⟨by simp [selectedTreeWord, ValidCode, BinaryWord],
        by simp [selectedTreeWord, wordLength, FiniteSequenceCoding.length], hz⟩
    | succ k ih =>
      refine ⟨append_valid _ _ ih.1, ?_, ?_⟩
      · change wordLength (appendBit (selectedTreeWord t D k) _) = k + 1
        rw [(appendBit_spec _ _).1, ih.2.1]
      · exact branch_selector_correct t T ht hT D hD _ ih.1 ih.2.2
  have hp (k : ℕ) : Prefix (selectedTreeWord t D k) (selectedTreeWord t D (k + 1)) :=
    (appendBit_spec _ _).2.1
  have hu : unionSet (selectedTreeWord t D) = selectedTreePath t D := by
    ext q
    change wordBit (appendBit (selectedTreeWord t D q) (selectedTreeBit t D q)) q = 1 ↔ _
    have he := (appendBit_spec (selectedTreeWord t D q) (selectedTreeBit t D q)).2.2
    rw [(hi q).2.1] at he
    rw [he]
    unfold selectedTreePath selectedTreeBit branchSelector
    by_cases h : treePairMap t (selectedTreeWord t D q) ∈ D <;> simp [indicator, h]
  have hr := (coherent_union (selectedTreeWord t D) hp (fun k => (hi k).2.1.ge)).1 n
  rw [hu] at hr
  refine ⟨(hi n).1, (hi n).2.1, (hi n).2.2, hp n, ?_⟩
  simpa only [(hi n).2.1] using realizes_code _ _ (hi n).1 hr

theorem dnc_path_uniform (t : ℕ) (T : Set ℕ) (ht : TreeDeciderIndex t T)
    (hT : IsBinaryTree T) (hne : ∃ X, Path T X) :
    ∀ D : Set ℕ, D ∈ binaryDNCClass →
      Path T (selectedTreePath t D) ∧
        Reduces (treePathProgram t) (selectedTreePath t D) D := by
  intro D hD
  refine ⟨?_, tree_path_program_reduces t D⟩
  intro n
  have hs := selected_tree_words_correct t T ht hT hne D hD n
  obtain ⟨v, hvT, _, hp⟩ : ∃ v ∈ T,
      wordLength v = wordLength (selectedTreeWord t D n) + 0 ∧
        Prefix (selectedTreeWord t D n) v := by
    simpa only [empty_extension_spec T hT, not_not] using hs.2.2.1 0
  have hm := hT.2 _ _ hs.1 hvT hp
  simpa only [hs.2.2.2.2] using hm

theorem tree_decider_index_exists (T : Set ℕ)
    (hc : ComputablePred (fun u => u ∈ T)) : ∃ t, TreeDeciderIndex t T := by
  obtain ⟨f, hf, he⟩ := (decidable_iff_characteristic (fun u => u ∈ T)).mp hc
  have hchi : Computable (indicator (fun u => u ∈ T)) := hf.of_eq he
  let c := ordinaryProgram (indicator (fun u => u ∈ T)) hchi
  refine ⟨Encodable.encode c, fun u => ?_⟩
  change Nat.Partrec.Code.eval (Denumerable.ofNat _ _) u = _
  rw [Denumerable.ofNat_encode]
  exact ordinaryProgram_eval _ hchi u

theorem dnc_path_property (D : Set ℕ) (hD : D ∈ binaryDNCClass) : PathProperty D := by
  intro T hT hc hne
  obtain ⟨t, ht⟩ := tree_decider_index_exists T hc
  have h := dnc_path_uniform t T ht hT hne D hD
  exact ⟨selectedTreePath t D, h.1, treePathProgram t, h.2⟩

theorem path_property_computes_dnc (A : Set ℕ) (hA : PathProperty A) : ComputesDNC A := by
  obtain ⟨D, hD, hDA⟩ := hA kleeneTree kleene_tree.1 kleene_tree.2.1 kleene_tree.2.2.2.1
  refine ⟨D, ?_, hDA⟩
  rw [dnc_separator_tree]
  exact hD

end
end Lemmatheca.ComputabilityTheory.PaDegrees
