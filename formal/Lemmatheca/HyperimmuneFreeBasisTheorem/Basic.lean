import Lemmatheca.LowBasisTheorem.Construction
import Lemmatheca.DominationAndHyperimmuneDegrees.Bounds

set_option autoImplicit false
namespace Lemmatheca.ComputabilityTheory.HyperimmuneFreeBasisTheorem
open ComputableTreesAndPaths IncomparableTuringDegrees UniversalComputation
open LowBasisTheorem HyperimmuneDegrees
noncomputable section
local instance hfbBasicPropDecidable (p : Prop) : Decidable p := Classical.propDecidable p

def HyperimmuneFreePath (T : Set ℕ) (A : Set ℕ) : Prop :=
  Path T A ∧ HyperimmuneFree A

def divergenceTree (S : Set ℕ) (e x : ℕ) : Set ℕ :=
  restricted S (FiniteSequenceCoding.code [TuringJump.freeze e x])

theorem divergence_membership (S : Set ℕ) (e x u : ℕ) :
    u ∈ divergenceTree S e x ↔
      u ∈ S ∧ certificateValue u (TuringJump.freeze e x) (TuringJump.freeze e x) = 0 := by
  simp [divergenceTree, restricted]

theorem frozen_output_certificate (A : Set ℕ) (e x y : ℕ) :
    y ∈ OracleProgramNumberings.phi A e x ↔
      ∃ u, Realizes u A ∧
        certificateValue u (TuringJump.freeze e x) (TuringJump.freeze e x) = y + 1 := by
  rw [← TuringJump.freeze_eval A e x (TuringJump.freeze e x)]
  exact prefix_output_iff A (TuringJump.freeze e x) (TuringJump.freeze e x) y

theorem divergence_paths (S : Set ℕ) (e x : ℕ) (A : Set ℕ) :
    Path (divergenceTree S e x) A ↔
      Path S A ∧ ¬ (OracleProgramNumberings.phi A e x).Dom := by
  simpa [divergenceTree, TuringJump.jump, TuringJump.freeze_eval] using
    restricted_paths S (FiniteSequenceCoding.code [TuringJump.freeze e x]) A

def SuccessfulLevel (S : Set ℕ) (e x m : ℕ) : Prop :=
  ∀ u ∈ binaryLevel m, u ∈ S →
    0 < certificateValue u (TuringJump.freeze e x) (TuringJump.freeze e x)

def successTest (S : Set ℕ) (e x m : ℕ) : Bool :=
  @decide (SuccessfulLevel S e x m) (Classical.propDecidable _)

theorem success_test_computable (S : Set ℕ) (hc : ComputablePred (fun u => u ∈ S)) :
    Computable (fun z : ℕ × (ℕ × ℕ) => successTest S z.1 z.2.1 z.2.2) := by
  have hj : Computable (fun z : ℕ × (ℕ × ℕ) => TuringJump.freeze z.1 z.2.1) :=
    TuringJump.freeze_primitive.to_comp.comp Computable.fst (Computable.fst.comp Computable.snd)
  have hl : Computable (fun z : ℕ × (ℕ × ℕ) =>
      FiniteSequenceCoding.cons (TuringJump.freeze z.1 z.2.1) 0) :=
    FiniteSequenceCoding.primrec_cons.to_comp.comp hj (Computable.const 0)
  have he := (LowBasisTheorem.empty_test_computable S hc).comp hl (Computable.snd.comp Computable.snd)
  refine he.of_eq ?_
  intro z
  apply Bool.eq_iff_iff.mpr
  simp only [LowBasisTheorem.emptyTest, successTest, decide_eq_true_eq]
  have hcode : FiniteSequenceCoding.cons (TuringJump.freeze z.1 z.2.1) 0 =
      FiniteSequenceCoding.code [TuringJump.freeze z.1 z.2.1] := by
    rw [FiniteSequenceCoding.code_cons]
    rfl
  rw [hcode]
  simp [LowBasisTheorem.EmptyLevel, restricted, SuccessfulLevel, Nat.pos_iff_ne_zero]

theorem successful_level_iff (S : Set ℕ) (hS : IsBinaryTree S) (e x m : ℕ) :
    SuccessfulLevel S e x m ↔ ¬ HasLevel (divergenceTree S e x) m := by
  constructor
  · intro hs
    rintro ⟨u, hu, hm⟩
    have hb := (binary_level_spec m u).mpr ⟨hS.1 u hu.1, hm⟩
    have hn := hs u hb hu.1
    have hz := (divergence_membership S e x u).mp hu
    omega
  · intro hn u hu hmem
    have hb := (binary_level_spec m u).mp hu
    by_contra hz
    apply hn
    refine ⟨u, (divergence_membership S e x u).mpr ⟨hmem, ?_⟩, hb.2⟩
    omega

theorem successful_level_exists (S : Set ℕ) (hS : IsBinaryTree S) (e x : ℕ)
    (ht : ∀ A, Path S A → (OracleProgramNumberings.phi A e x).Dom) :
    ∃ m, SuccessfulLevel S e x m := by
  by_contra hn
  have hi : ∀ m, HasLevel (divergenceTree S e x) m := by
    intro m
    by_contra hm
    exact hn ⟨m, (successful_level_iff S hS e x m).mpr hm⟩
  obtain ⟨A, hA⟩ := (all_levels_path _
    (restricted_tree S hS (FiniteSequenceCoding.code [TuringJump.freeze e x]))).mp hi
  have ha := (divergence_paths S e x A).mp hA
  exact ha.2 (ht A ha.1)

end
end Lemmatheca.ComputabilityTheory.HyperimmuneFreeBasisTheorem
