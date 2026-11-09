import Lemmatheca.LowBasisTheorem.Basis

/-! Empty initial trees cannot acquire paths by adding restrictions. -/
namespace Lemmatheca.Entry.LowBasisTheorem

open Lemmatheca.ComputabilityTheory
open ComputableTreesAndPaths LowBasisTheorem UniversalComputation

theorem empty_tree :
    IsBinaryTree (∅ : Set ℕ) ∧ ComputablePred (fun u : ℕ => u ∈ (∅ : Set ℕ)) ∧
      ∀ X, ¬ Path (∅ : Set ℕ) X := by
  have hc : ComputablePred (fun _ : ℕ => False) :=
    Computable.computablePred (Computable.const false)
  refine ⟨by simp [IsBinaryTree], by simpa only [Set.mem_empty_iff_false] using hc, ?_⟩
  intro X hX
  exact hX 0

theorem inherited_empty_level (T : Set ℕ) (n l : ℕ) (hn : ¬ HasLevel T n) :
    ¬ HasLevel (restricted T l) n := by
  rintro ⟨u, hu, hl⟩
  exact hn ⟨u, hu.1, hl⟩

end Lemmatheca.Entry.LowBasisTheorem
