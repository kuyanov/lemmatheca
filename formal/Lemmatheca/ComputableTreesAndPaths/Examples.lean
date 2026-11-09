import Lemmatheca.ComputableTreesAndPaths.Separator
import Lemmatheca.ComputableTreesAndPaths.UniquePath

/-! Boundary cases for the quantified path claims. -/
namespace Lemmatheca.Entry.ComputableTreesAndPaths

open Lemmatheca.ComputabilityTheory
open ComputableTreesAndPaths IncomparableTuringDegrees PostsTheorem UniversalComputation

noncomputable section

def fullTree : Set ℕ := {u | ValidCode u}

def rootTree : Set ℕ := {0}

theorem full_tree :
    IsBinaryTree fullTree ∧ ComputablePred (fun u => u ∈ fullTree) ∧
      ∀ X : Set ℕ, Path fullTree X := by
  exact ⟨⟨fun _ h => h, fun _ _ h _ _ => h⟩, valid_code_primitive.computablePred,
    fun X n => prefix_code_valid X n⟩

theorem root_tree :
    IsBinaryTree rootTree ∧ ComputablePred (fun u => u ∈ rootTree) ∧
      (¬ ∃ X, Path rootTree X) ∧ ¬ (uniqueSearch rootTree 0).Dom := by
  classical
  have hz : ValidCode 0 := by simp [ValidCode, BinaryWord]
  have hzero : wordLength 0 = 0 := by simp [wordLength, FiniteSequenceCoding.length]
  have ht : IsBinaryTree rootTree := by
    refine ⟨fun u hu => by simpa only [show u = 0 from hu] using hz, ?_⟩
    intro u v hu hv hp
    have hv0 : v = 0 := hv
    subst v
    have hl : wordLength u = wordLength 0 := by
      have h := hp.1
      rw [hzero] at h ⊢
      omega
    have he : u = 0 := code_ext u 0 hu hz hl (fun q hq => by
      rw [hl, hzero] at hq
      omega)
    exact he
  have hc : ComputablePred (fun u => u ∈ rootTree) :=
    (Primrec.eq.comp Primrec.id (Primrec.const 0)).computablePred
  have hnone : ¬ ∃ X, Path rootTree X := by
    rintro ⟨X, hX⟩
    have he : prefixCode X 1 = 0 := hX 1
    have hl : wordLength (prefixCode X 1) = 1 := (prefixCode_spec X 1).1
    rw [he] at hl
    rw [hzero] at hl
    omega
  have hempty (m : ℕ) (hm : 1 ≤ m) : survivors rootTree 0 m = [] := by
    have hf : (binaryLevel m).filter (fun u => decide (u ∈ rootTree)) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro u hu
      simp only [decide_eq_true_eq]
      intro hroot
      have he : u = 0 := hroot
      have hl := ((binary_level_spec m u).mp hu).2
      rw [he] at hl
      rw [hzero] at hl
      omega
    simp [survivors, hf]
  refine ⟨ht, hc, hnone, ?_⟩
  intro hdom
  have hd : (Nat.rfind fun k => Part.some
      (decide ((survivors rootTree 0 (0 + 1 + k)).length = 1))).Dom := hdom
  obtain ⟨k, hk⟩ := Part.dom_iff_mem.mp hd
  have hs := Nat.rfind_spec hk
  rw [hempty (0 + 1 + k) (by omega)] at hs
  simp at hs

end
end Lemmatheca.Entry.ComputableTreesAndPaths
