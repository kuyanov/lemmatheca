import Lemmatheca.HyperimmuneFreeBasisTheorem.Construction
import Lemmatheca.PaDegrees.Degrees

set_option autoImplicit false
namespace Lemmatheca.ComputabilityTheory.HyperimmuneFreeBasisTheorem
open ComputableTreesAndPaths IncomparableTuringDegrees UniversalComputation
open LowBasisTheorem HyperimmuneDegrees PaDegrees EffectivelyClosedClassesAndDnc
noncomputable section
local instance hfbBasisPropDecidable (p : Prop) : Decidable p := Classical.propDecidable p

theorem common_path_hyperimmune_free (T : Set ℕ) (hT : IsBinaryTree T)
    (t : ℕ) (ht : TreeDeciderIndex t T) (A : Set ℕ)
    (hA : ∀ e, Path (stageTree T e) A) : HyperimmuneFreePath T A := by
  refine ⟨?_, ?_⟩
  · simpa only [stageTree, restrictionHistory, restricted_zero] using hA 0
  · intro f hf
    obtain ⟨c, hc⟩ := hf
    let e := OracleProgramNumberings.encodeCode c
    have he (x : ℕ) : OracleProgramNumberings.phi A e x = Part.some (f x) := by
      change OracleComputation.eval A
        (OracleProgramNumberings.decodeCode (OracleProgramNumberings.encodeCode c)) x = _
      rw [OracleProgramNumberings.decode_encode]
      exact congrFun hc x
    rcases stage_alternatives T hT t ht e with ⟨_, _, hbad⟩ | ⟨_, _, hbound⟩
    · have hn := hbad A (hA (e + 1))
      rw [he] at hn
      exact False.elim (hn (Part.some_dom _))
    · obtain ⟨h, hh, _, hb⟩ := hbound
      refine ⟨h, hh, Filter.Eventually.of_forall ?_⟩
      intro x
      apply hb A (hA e) x (f x)
      rw [he]
      exact Part.mem_some _

theorem hyperimmune_free_basis (T : Set ℕ) (hT : IsBinaryTree T)
    (hc : ComputablePred (fun u => u ∈ T)) (hi : ∀ n, HasLevel T n) :
    ∃ A, HyperimmuneFreePath T A := by
  obtain ⟨Y, hY⟩ := (all_levels_path T hT).mp hi
  obtain ⟨t, ht⟩ := tree_decider_index_exists T hc
  obtain ⟨A, hA⟩ := common_path T hT hc ⟨Y, hY⟩
  exact ⟨A, common_path_hyperimmune_free T hT t ht A hA⟩

theorem closed_hyperimmune_free_basis (P : Set (Set ℕ)) (hP : EffectivelyClosed P)
    (hne : P.Nonempty) : ∃ A ∈ P, HyperimmuneFree A := by
  obtain ⟨T, hT, hc, he⟩ := (effectively_closed_iff_tree P).mp hP
  obtain ⟨Y, hY⟩ := hne
  have hpY : Path T Y := (Set.ext_iff.mp he Y).mpr hY
  have hi := (all_levels_path T hT).mpr ⟨Y, hpY⟩
  obtain ⟨A, hpA, hfree⟩ := hyperimmune_free_basis T hT hc hi
  exact ⟨A, (Set.ext_iff.mp he A).mp hpA, hfree⟩

theorem co_ce_hyperimmune_free_basis (T : Set ℕ) (hT : CoCETree T)
    (hne : ∃ A, Path T A) : ∃ A, HyperimmuneFreePath T A := by
  obtain ⟨r, hr⟩ := (enumerable_iff_index
    (fun u => u ∈ missingWords T)).mp hT.2
  have hindex : EffectiveEnumerations.indexSet r = missingWords T := by
    ext u
    exact (hr u).symm
  obtain ⟨htree, hc, he⟩ := co_ce_conversion T r hindex
  obtain ⟨Y, hY⟩ := hne
  have hi := (all_levels_path (commonStageTree r) htree).mpr ⟨Y, (he Y).mpr hY⟩
  obtain ⟨A, hpA, hfree⟩ := hyperimmune_free_basis (commonStageTree r) htree hc hi
  exact ⟨A, (he A).mp hpA, hfree⟩

theorem hyperimmune_free_pa : ∃ A : Set ℕ,
    Path kleeneTree A ∧ A ∈ binaryDNCClass ∧ HyperimmuneFree A ∧ IsPAOracle A ∧
      ¬ ComputablePred (fun n => n ∈ A) := by
  obtain ⟨A, hpA, hfree⟩ := hyperimmune_free_basis kleeneTree kleene_tree.1
    kleene_tree.2.1 kleene_tree.2.2.1
  have hdnc : A ∈ binaryDNCClass := by
    rw [dnc_separator_tree]
    exact hpA
  have hpa : IsPAOracle A := (pa_iff_computes_dnc A).mpr
    ⟨A, hdnc, TuringDegrees.reducible_refl A⟩
  exact ⟨A, hpA, hdnc, hfree, hpa, binary_dnc_not_computable A hdnc⟩

end
end Lemmatheca.ComputabilityTheory.HyperimmuneFreeBasisTheorem
