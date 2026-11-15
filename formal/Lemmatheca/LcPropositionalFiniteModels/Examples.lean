import Lemmatheca.LcPropositionalFiniteModels.Search
import Lemmatheca.KcPropositionalFiniteModels.Examples
import Lemmatheca.PropositionalDummettLinearity.Examples

namespace Lemmatheca.Entry.LcPropositionalFiniteModels

open Lemmatheca.MathematicalLogic.Propositional
open Lemmatheca.ProofTheory.Intuitionistic
open PropFormula FiniteModels

theorem chain_comparable :
    LCFiniteModels.ComparableCode
      IntuitionisticPropositionalFiniteModelProperty.exampleRelation := by
  decide

theorem chain_candidate :
    LCFiniteModels.candidate [] IntuitionisticPropositionalFiniteModelProperty.excludedMiddle
      IntuitionisticPropositionalFiniteModelProperty.exampleRelation
      (fun i _ => decide (i = 1)) 0 1 = true := by
  decide

theorem chain_refute :
    LCFiniteModels.refute [] IntuitionisticPropositionalFiniteModelProperty.excludedMiddle =
      true := by
  simp only [LCFiniteModels.refute, decide_eq_true_eq]
  refine ⟨⟨2, ?_⟩,
    IntuitionisticPropositionalFiniteModelProperty.exampleRelation,
    (fun i _ => decide (i = 1)), 0, 1, chain_candidate⟩
  change 2 < worldBound ∅ IntuitionisticPropositionalFiniteModelProperty.excludedMiddle + 1
  rw [IntuitionisticPropositionalFiniteModelProperty.example_problem.2.2]
  decide

abbrev diamondFormula : Formula := Dummett.linearity (atom 0) (atom 1)

/-- The four rows are 1111, 0101, 0011 and 0001. -/
def diamondRelation : RelationCode 4 :=
  fun i j => decide (i = 0 ∨ j = 3 ∨ i = j)

def diamondValuation : ValuationCode 4 (problemAtoms ∅ diamondFormula) :=
  fun i p => decide ((p.val = 0 ∧ (i = 1 ∨ i = 3)) ∨
    (p.val = 1 ∧ (i = 2 ∨ i = 3)))

theorem diamond_values (p : ℕ) :
    extendedValuation diamondValuation 0 p = false ∧
      (extendedValuation diamondValuation 1 p = true ↔ p = 0) ∧
      (extendedValuation diamondValuation 2 p = true ↔ p = 1) ∧
      (extendedValuation diamondValuation 3 p = true ↔ p = 0 ∨ p = 1) := by
  simp [extendedValuation, diamondValuation, problemAtoms,
    diamondFormula, Dummett.linearity, atoms]
  tauto

theorem diamond_noncomparison :
    diamondRelation 1 2 = false ∧ diamondRelation 2 1 = false ∧
      LCFiniteModels.comparable diamondRelation = false := by
  decide

theorem diamond_candidates :
    KCFiniteModels.candidate [] diamondFormula diamondRelation diamondValuation 0 3 = true ∧
      LCFiniteModels.candidate [] diamondFormula diamondRelation diamondValuation 0 3 = false := by
  decide

theorem diamond_searches :
    KCFiniteModels.refute [] diamondFormula = true ∧
      LCFiniteModels.refute [] diamondFormula = false := by
  constructor
  · apply (KCFiniteModels.refute_iff_not_derives [] diamondFormula).mpr
    simpa using PropositionalDummettLinearity.not_kc_linearity
  · apply (LCFiniteModels.refute_false_iff_derives [] diamondFormula).mpr
    simpa using Dummett.instance_theorem (atom (0 : ℕ)) (atom 1)

end Lemmatheca.Entry.LcPropositionalFiniteModels
