import Lemmatheca.KcPropositionalFiniteModels.Search
import Lemmatheca.IntuitionisticPropositionalFiniteModelProperty.Examples

namespace Lemmatheca.Entry.KcPropositionalFiniteModels

open Lemmatheca.MathematicalLogic.Propositional
open Lemmatheca.ProofTheory.Intuitionistic
open FiniteModels

theorem chain_rootedTop :
    KCFiniteModels.RootedTop IntuitionisticPropositionalFiniteModelProperty.exampleRelation 0 1 := by
  decide

theorem chain_candidate :
    KCFiniteModels.candidate [] IntuitionisticPropositionalFiniteModelProperty.excludedMiddle
      IntuitionisticPropositionalFiniteModelProperty.exampleRelation
      (fun i _ => decide (i = 1)) 0 1 = true := by
  decide

theorem chain_refute :
    KCFiniteModels.refute [] IntuitionisticPropositionalFiniteModelProperty.excludedMiddle =
      true := by
  simp only [KCFiniteModels.refute, decide_eq_true_eq]
  refine ⟨⟨2, ?_⟩,
    IntuitionisticPropositionalFiniteModelProperty.exampleRelation,
    (fun i _ => decide (i = 1)), 0, 1, chain_candidate⟩
  change 2 < worldBound ∅ IntuitionisticPropositionalFiniteModelProperty.excludedMiddle + 1
  rw [IntuitionisticPropositionalFiniteModelProperty.example_problem.2.2]
  decide

end Lemmatheca.Entry.KcPropositionalFiniteModels
