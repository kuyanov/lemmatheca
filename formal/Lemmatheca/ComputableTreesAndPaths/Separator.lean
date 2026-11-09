import Lemmatheca.ComputableTreesAndPaths.Basic
import Lemmatheca.ComputablyInseparableSets.Separation
import Lemmatheca.EffectiveEnumerations.Stages

/-! The word-length-stage separator tree, with ones on the first c.e. set. -/
namespace Lemmatheca.ComputabilityTheory.ComputableTreesAndPaths

open IncomparableTuringDegrees PostsTheorem UniversalComputation
open EffectiveEnumerations ComputableSeparation

noncomputable section

def separatorTree (a b : ℕ) : Set ℕ :=
  {u | ValidCode u ∧ ∀ q < wordLength u,
    (q ∈ stage a (wordLength u) → wordBit u q = 1) ∧
    (q ∈ stage b (wordLength u) → wordBit u q = 0)}

def levelWitness (a n : ℕ) : ℕ :=
  FiniteSequenceCoding.code ((List.range n).map (stageTest a n))

theorem separator_tree_primitive (a b : ℕ) :
    PrimrecPred (fun u => u ∈ separatorTree a b) := by
  have hs (e : ℕ) : PrimrecRel (fun u q => q ∈ stage e (wordLength u)) :=
    stage_predicate_primitive.comp
      (((Primrec.const e).pair (FiniteSequenceCoding.primrec_length.comp Primrec.fst)).pair
        Primrec.snd)
  have hb (z : ℕ) : PrimrecRel (fun u q => wordBit u q = z) :=
    Primrec.eq.comp beta_primitive (Primrec.const z)
  have hr : PrimrecRel (fun u q =>
      (q ∈ stage a (wordLength u) → wordBit u q = 1) ∧
      (q ∈ stage b (wordLength u) → wordBit u q = 0)) :=
    (((hs a).not.or (hb 1)).and ((hs b).not.or (hb 0))).of_eq
      (fun _ => by simp only [imp_iff_not_or])
  exact valid_code_primitive.and
    ((PrimitiveRecursion.bounded_forall_primrec hr).comp Primrec.id
      FiniteSequenceCoding.primrec_length)

theorem separator_tree_closed (a b : ℕ) :
    IsBinaryTree (separatorTree a b) := by
  refine ⟨fun _ h => h.1, ?_⟩
  intro u v hu hv huv
  refine ⟨hu, fun q hq => ?_⟩
  have hqv : q < wordLength v := lt_of_lt_of_le hq huv.1
  constructor
  · intro ha
    rw [huv.2 q hq]
    exact (hv.2 q hqv).1 (stage_monotone a huv.1 ha)
  · intro hb
    rw [huv.2 q hq]
    exact (hv.2 q hqv).2 (stage_monotone b huv.1 hb)

theorem level_witness_primitive (a : ℕ) : Primrec (levelWitness a) := by
  have hs : Primrec₂ (stageTest a) :=
    (stage_test_primitive.comp (((Primrec.const a).pair Primrec.fst).pair Primrec.snd)).to₂
  exact Primrec.encode.comp (Primrec.list_map Primrec.list_range hs)

theorem level_witness_spec (a n : ℕ) :
    ValidCode (levelWitness a n) ∧ wordLength (levelWitness a n) = n ∧
      ∀ q < n, wordBit (levelWitness a n) q = stageTest a n q := by
  refine ⟨?_, ?_, ?_⟩
  · intro b hb
    simp only [levelWitness, FiniteSequenceCoding.decode_code, List.mem_map,
      List.mem_range] at hb
    obtain ⟨q, _, rfl⟩ := hb
    exact (stage_test_spec a n q).1
  · simp [levelWitness, wordLength, FiniteSequenceCoding.length]
  · intro q hq
    have he : FiniteSequenceCoding.entry (levelWitness a n) q = stageTest a n q := by
      simp [levelWitness, FiniteSequenceCoding.entry, List.getElem?_range hq]
    change FiniteSequenceCoding.entry (levelWitness a n) q % 2 = _
    rw [he]
    rcases (stage_test_spec a n q).1 with h | h <;> simp [h]

theorem separator_tree_levels (a b : ℕ)
    (hab : Disjoint (indexSet a) (indexSet b)) (n : ℕ) :
    levelWitness a n ∈ separatorTree a b ∧ HasLevel (separatorTree a b) n := by
  have hs := level_witness_spec a n
  have hm : levelWitness a n ∈ separatorTree a b := by
    refine ⟨hs.1, fun q hq => ?_⟩
    rw [hs.2.1] at hq ⊢
    rw [hs.2.2 q hq]
    refine ⟨fun ha => (stage_test_spec a n q).2.mpr ha, ?_⟩
    intro hb
    have hnot : q ∉ stage a n := by
      intro ha
      apply Set.disjoint_left.mp hab
      · exact (stage_union a q).mpr ⟨n, ha⟩
      · exact (stage_union b q).mpr ⟨n, hb⟩
    rcases (stage_test_spec a n q).1 with h | h
    · exact h
    · exact False.elim (hnot ((stage_test_spec a n q).2.mp h))
  exact ⟨hm, levelWitness a n, hm, hs.2.1⟩

theorem paths_are_separators (a b : ℕ) (X : Set ℕ) :
    Path (separatorTree a b) X ↔ Separator (indexSet a) (indexSet b) X := by
  classical
  constructor
  · intro hX
    have forced (e q bit : ℕ) (hq : q ∈ indexSet e)
        (hf : ∀ n, q < n → q ∈ stage e n →
          wordBit (prefixCode X n) q = bit) :
        indicator (fun x => x ∈ X) q = bit := by
      obtain ⟨s, hs⟩ := (stage_union e q).mp hq
      let n := max s (q + 1)
      have hqn : q < n := by dsimp [n]; omega
      exact ((prefixCode_spec X n).2 q hqn).symm.trans
        (hf n hqn (stage_monotone e (le_max_left _ _) hs))
    constructor
    · intro q hq
      have he := forced a q 1 hq (fun n hqn hs => by
        have hn := hX n
        have hl := (prefixCode_spec X n).1
        exact (hn.2 q (by simpa only [hl] using hqn)).1 (by simpa only [hl] using hs))
      by_contra hnot
      simp [indicator, hnot] at he
    · apply Set.disjoint_left.mpr
      intro q hqx hqb
      have he := forced b q 0 hqb (fun n hqn hs => by
        have hn := hX n
        have hl := (prefixCode_spec X n).1
        exact (hn.2 q (by simpa only [hl] using hqn)).2 (by simpa only [hl] using hs))
      simp [indicator, hqx] at he
  · intro hs n
    have hl := (prefixCode_spec X n).1
    refine ⟨prefix_code_valid X n, fun q hq => ?_⟩
    have hqn : q < n := by simpa only [hl] using hq
    have he : wordBit (prefixCode X n) q = indicator (fun x => x ∈ X) q :=
      (prefixCode_spec X n).2 q hqn
    rw [he]
    constructor
    · intro ha
      have hqa : q ∈ indexSet a := (stage_union a q).mpr
        ⟨n, by simpa only [hl] using ha⟩
      simp [indicator, hs.1 hqa]
    · intro hb
      have hqb : q ∈ indexSet b := (stage_union b q).mpr
        ⟨n, by simpa only [hl] using hb⟩
      have hnot : q ∉ X := fun hx => Set.disjoint_left.mp hs.2 hx hqb
      simp [indicator, hnot]

def diagonalAIndex : ℕ :=
  Classical.choose ((enumerable_iff_index (diagonalOutput 0)).mp
    (diagonalOutput_enumerable 0))

def diagonalBIndex : ℕ :=
  Classical.choose ((enumerable_iff_index (diagonalOutput 1)).mp
    (diagonalOutput_enumerable 1))

def kleeneTree : Set ℕ := separatorTree diagonalAIndex diagonalBIndex

theorem diagonal_indices :
    indexSet diagonalAIndex = diagonalOutput 0 ∧
      indexSet diagonalBIndex = diagonalOutput 1 := by
  constructor
  · ext x
    exact (Classical.choose_spec ((enumerable_iff_index (diagonalOutput 0)).mp
      (diagonalOutput_enumerable 0)) x).symm
  · ext x
    exact (Classical.choose_spec ((enumerable_iff_index (diagonalOutput 1)).mp
      (diagonalOutput_enumerable 1)) x).symm

theorem kleene_tree :
    IsBinaryTree kleeneTree ∧ ComputablePred (fun u => u ∈ kleeneTree) ∧
      (∀ n, HasLevel kleeneTree n) ∧ (∃ X, Path kleeneTree X) ∧
      ¬ ∃ X, Path kleeneTree X ∧ ComputablePred (fun q => q ∈ X) := by
  have hd : Disjoint (indexSet diagonalAIndex) (indexSet diagonalBIndex) := by
    rw [diagonal_indices.1, diagonal_indices.2]
    exact diagonal_inseparable.1
  have ht : IsBinaryTree kleeneTree := separator_tree_closed _ _
  have hi (n : ℕ) : HasLevel kleeneTree n := (separator_tree_levels _ _ hd n).2
  refine ⟨ht, (separator_tree_primitive _ _).computablePred, hi,
    (all_levels_path _ ht).mp hi, ?_⟩
  rintro ⟨X, hX, hc⟩
  have hs := (paths_are_separators diagonalAIndex diagonalBIndex X).mp hX
  rw [diagonal_indices.1, diagonal_indices.2] at hs
  exact diagonal_inseparable.2 ⟨X, hc, hs⟩

theorem witnesses_need_not_agree (a q s : ℕ) (hqs : q + 1 < s)
    (hnot : q ∉ stage a (q + 1)) (hyes : q ∈ stage a s) :
    wordBit (levelWitness a (q + 1)) q = 0 ∧
      wordBit (levelWitness a s) q = 1 := by
  rw [(level_witness_spec a (q + 1)).2.2 q (by omega),
    (level_witness_spec a s).2.2 q (by omega)]
  refine ⟨?_, (stage_test_spec a s q).2.mpr hyes⟩
  rcases (stage_test_spec a (q + 1) q).1 with h | h
  · exact h
  · exact False.elim (hnot ((stage_test_spec a (q + 1) q).2.mp h))

end
end Lemmatheca.ComputabilityTheory.ComputableTreesAndPaths
