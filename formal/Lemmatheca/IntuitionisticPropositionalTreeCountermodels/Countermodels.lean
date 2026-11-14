import Lemmatheca.IntuitionisticPropositionalTreeCountermodels.Models
import Lemmatheca.IntuitionisticPropositionalFiniteModelProperty.Traces

namespace Lemmatheca.ProofTheory.Intuitionistic.Kripke.StrictPaths

open Lemmatheca.MathematicalLogic.Propositional

abbrev NumberedFormula := PropFormula ℕ

/-- A finite-premise failure in the actual IPC relation has a finite tree witness. -/
theorem finite_tree_countermodel (Γ : Finset NumberedFormula) (A : NumberedFormula)
    (h : ¬ Derives (Γ : Set NumberedFormula) A) :
    ∃ (T : Type) (rt : PartialOrder T) (_ft : Fintype T)
      (M : @Model ℕ T rt.toPreorder) (o : T),
      @IsFiniteRootedTree T rt o ∧
        @Countermodel ℕ T rt.toPreorder M o (Γ : Set NumberedFormula) A := by
  classical
  obtain ⟨W, rW, fw, M, w, _, hc⟩ := FiniteModels.finite_poset_countermodel Γ A h
  let : PartialOrder W := rW
  let : Fintype W := fw
  let c : {x : W // w ≤ x} := ⟨w, le_rfl⟩
  let G := generated M w
  let U := model G c
  refine ⟨Path c, inferInstance, inferInstance, U, root c, ?_, ?_⟩
  · exact ⟨inferInstance, fun p => root_le p,
      fun p q s hp hq => predecessors_compare p q s hp hq⟩
  · have hG := generated_countermodel M w (Γ : Set NumberedFormula) A hc
    have hi := boundedMorphism_countermodel U G last (last_morphism G c)
      (root c) (Γ : Set NumberedFormula) A
    exact hi.mpr (by simpa only [last_root] using hG)

theorem root_consequence_iff (Γ : Finset NumberedFormula) (A : NumberedFormula) :
    Derives (Γ : Set NumberedFormula) A ↔
      ∀ (T : Type) (rt : PartialOrder T) (_ft : Fintype T)
        (M : @Model ℕ T rt.toPreorder) (o : T),
        @IsFiniteRootedTree T rt o →
        @ForcesContext ℕ T rt.toPreorder M o (Γ : Set NumberedFormula) →
        @Forces ℕ T rt.toPreorder M o A := by
  constructor
  · intro hd T rt _ft M o _ht hΓ
    exact sound hd M o hΓ
  · intro htest
    by_contra hn
    obtain ⟨T, rt, ft, M, o, ht, hc⟩ := finite_tree_countermodel Γ A hn
    exact hc.2 (htest T rt ft M o ht hc.1)

end Lemmatheca.ProofTheory.Intuitionistic.Kripke.StrictPaths
