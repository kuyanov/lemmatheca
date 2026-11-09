import Lemmatheca.EffectivelyClosedClassesAndDnc.HaltingMembers
import Lemmatheca.ComputablyInseparableSets.Examples

/-! The delayed-prohibition counterexample and the partial-diagonal boundary case. -/
namespace Lemmatheca.Entry.EffectivelyClosedClassesAndDnc

open Lemmatheca.ComputabilityTheory
open EffectivelyClosedClassesAndDnc ComputableTreesAndPaths IncomparableTuringDegrees
open PostsTheorem UniversalComputation

noncomputable section

def containsOne : Set ℕ :=
  {u | ValidCode u ∧ ∃ q < wordLength u, wordBit u q = 1}

def zeroTree : Set ℕ :=
  {u | ValidCode u ∧ ∀ q < wordLength u, wordBit u q = 0}

def delayedStage (s : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range s).filter (fun u => u ∈ containsOne ∧ wordLength u < s)

def wrongTree : Set ℕ :=
  {u | ValidCode u ∧ ∀ i ≤ wordLength u, takeCode i u ∉ delayedStage i}

def delayedTree : Set ℕ :=
  {u | ValidCode u ∧ ∀ i ≤ wordLength u, takeCode i u ∉ delayedStage (wordLength u)}


private theorem bit_binary (u q : ℕ) : wordBit u q = 0 ∨ wordBit u q = 1 := by
  have h := Nat.mod_lt (FiniteSequenceCoding.entry u q) (by decide : 0 < 2)
  change wordBit u q < 2 at h
  omega

private theorem contains_one_primitive : PrimrecPred (fun u => u ∈ containsOne) := by
  have hr : PrimrecRel (fun u q => wordBit u q = 1) :=
    Primrec.eq.comp beta_primitive (Primrec.const 1)
  exact valid_code_primitive.and
    ((PrimitiveRecursion.bounded_exists_primrec hr).comp Primrec.id
      FiniteSequenceCoding.primrec_length)

private theorem delayed_mem_primitive :
    PrimrecPred (fun p : ℕ × ℕ => p.2 ∈ delayedStage p.1) := by
  classical
  have h := (Primrec.nat_lt.comp Primrec.snd Primrec.fst).and
    ((contains_one_primitive.comp Primrec.snd).and
      (Primrec.nat_lt.comp (FiniteSequenceCoding.primrec_length.comp Primrec.snd)
        Primrec.fst))
  exact h.of_eq (fun p => by simp only [delayedStage, Finset.mem_filter, Finset.mem_range])

theorem delayed_stage_properties :
    Computable₂ (fun s u => decide (u ∈ delayedStage s)) ∧
      Monotone (fun s => (↑(delayedStage s) : Set ℕ)) ∧
      ∀ u, u ∈ containsOne ↔ ∃ s, u ∈ delayedStage s := by
  classical
  refine ⟨delayed_mem_primitive.decide.to_comp, ?_, ?_⟩
  · intro s t hst u hu
    have h : u < s ∧ u ∈ containsOne ∧ wordLength u < s := by
      simpa only [delayedStage, Finset.mem_filter, Finset.mem_range, Finset.mem_coe] using hu
    show u ∈ delayedStage t
    simp only [delayedStage, Finset.mem_filter, Finset.mem_range]
    exact ⟨h.1.trans_le hst, h.2.1, h.2.2.trans_le hst⟩
  · intro u
    constructor
    · intro hu
      refine ⟨max u (wordLength u) + 1, ?_⟩
      simp only [delayedStage, Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, hu, by omega⟩
    · rintro ⟨s, hs⟩
      exact (Finset.mem_filter.mp hs).2.1

theorem contains_one_complement :
    containsOne = {u | ValidCode u ∧ u ∉ zeroTree} := by
  ext u
  constructor
  · rintro ⟨hu, q, hq, hb⟩
    exact ⟨hu, fun hz => by have he := hz.2 q hq; omega⟩
  · rintro ⟨hu, hn⟩
    refine ⟨hu, ?_⟩
    by_contra h
    push Not at h
    apply hn
    refine ⟨hu, fun q hq => ?_⟩
    have hb := bit_binary u q
    exact hb.resolve_right (h q hq)

theorem wrong_tree_full :
    wrongTree = {u | ValidCode u} ∧ ∀ X : Set ℕ, Path wrongTree X := by
  classical
  have he : wrongTree = {u | ValidCode u} := by
    ext u
    constructor
    · exact fun h => h.1
    · intro hu
      refine ⟨hu, fun i hi hmem => ?_⟩
      have hlen : wordLength (takeCode i u) = i := by
        rw [(take_spec i u hu).1, min_eq_left hi]
      have hs : wordLength (takeCode i u) < i := (Finset.mem_filter.mp hmem).2.2
      omega
  refine ⟨he, fun X n => ?_⟩
  rw [he]
  exact prefix_code_valid X n

theorem zero_tree_paths (X : Set ℕ) : Path zeroTree X ↔ X = ∅ := by
  classical
  constructor
  · intro hX
    ext q
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hq
    have hn := hX (q + 1)
    have hlen : wordLength (prefixCode X (q + 1)) = q + 1 :=
      (prefixCode_spec X (q + 1)).1
    have hb := hn.2 q (by rw [hlen]; omega)
    have hv : wordBit (prefixCode X (q + 1)) q = indicator (fun e => e ∈ X) q :=
      (prefixCode_spec X (q + 1)).2 q (by omega)
    rw [hv] at hb
    simp [indicator, hq] at hb
  · rintro rfl n
    refine ⟨prefix_code_valid ∅ n, fun q hq => ?_⟩
    have hqn : q < n := by simpa only [(prefixCode_spec ∅ n).1] using hq
    exact ((prefixCode_spec ∅ n).2 q hqn).trans (by simp [indicator])

theorem zero_tree_properties :
    IsBinaryTree zeroTree ∧ ComputablePred (fun u => u ∈ zeroTree) := by
  have hr : PrimrecRel (fun u q => wordBit u q = 0) :=
    Primrec.eq.comp beta_primitive (Primrec.const 0)
  have hp : PrimrecPred (fun u => u ∈ zeroTree) := valid_code_primitive.and
    ((PrimitiveRecursion.bounded_forall_primrec hr).comp Primrec.id
      FiniteSequenceCoding.primrec_length)
  refine ⟨⟨fun _ h => h.1, ?_⟩, hp.computablePred⟩
  intro u v hu hv huv
  refine ⟨hu, fun q hq => ?_⟩
  exact (huv.2 q hq).trans (hv.2 q (hq.trans_le huv.1))

theorem delayed_tree_paths (X : Set ℕ) : Path delayedTree X ↔ X = ∅ := by
  classical
  constructor
  · intro hX
    ext q
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hq
    have hc : prefixCode X (q + 1) ∈ containsOne := by
      refine ⟨prefix_code_valid _ _, q, ?_, ?_⟩
      · rw [show wordLength (prefixCode X (q + 1)) = q + 1 from
          (prefixCode_spec X (q + 1)).1]
        omega
      · exact ((prefixCode_spec X (q + 1)).2 q (by omega)).trans (by simp [indicator, hq])
    obtain ⟨s, hs⟩ := (delayed_stage_properties.2.2 _).mp hc
    let m := max (q + 1) s
    have hn := hX m
    have hi : q + 1 ≤ wordLength (prefixCode X m) := by
      simpa only [(prefixCode_spec X m).1] using (le_max_left (q + 1) s)
    apply hn.2 (q + 1) hi
    rw [take_prefix_code X (q + 1) m (le_max_left _ _)]
    rw [show wordLength (prefixCode X m) = m from (prefixCode_spec X m).1]
    change prefixCode X (q + 1) ∈ (↑(delayedStage m) : Set ℕ)
    exact delayed_stage_properties.2.1 (show s ≤ m from le_max_right _ _) hs
  · rintro rfl m
    refine ⟨prefix_code_valid _ _, fun i _ hmem => ?_⟩
    have hc := (Finset.mem_filter.mp hmem).2.1
    have hn := (zero_tree_paths ∅).mpr rfl m
    have ht : takeCode i (prefixCode ∅ m) ∈ zeroTree :=
      zero_tree_properties.1.2 _ _ (take_valid _ _ hn.1) hn (take_spec _ _ hn.1).2
    exact ((Set.ext_iff.mp contains_one_complement _).mp hc).2 ht

def partialDiagonal (e : ℕ) : Part ℕ := (phi e e).map Nat.succ

theorem partial_diagonal_properties :
    Nat.Partrec partialDiagonal ∧
      (∀ e y z, y ∈ phi e e → z ∈ partialDiagonal e → z ≠ y) ∧
      (∃ e, ¬ (partialDiagonal e).Dom) := by
  have hc : Partrec partialDiagonal :=
    (phi_recursive.comp Computable.id Computable.id).map
      (Computable.succ.comp Computable.snd).to₂
  refine ⟨Partrec.nat_iff.mp hc, ?_, ?_⟩
  · intro e y z hy hz
    change z ∈ (phi e e).map Nat.succ at hz
    obtain ⟨a, ha, he⟩ := (Part.mem_map_iff _).mp hz
    have heq := Part.mem_unique ha hy
    omega
  · obtain ⟨q, hq, _⟩ := ComputablyInseparableSets.nowhere_defined_outside
    exact ⟨q, by simp [partialDiagonal, hq q]⟩

end
end Lemmatheca.Entry.EffectivelyClosedClassesAndDnc
