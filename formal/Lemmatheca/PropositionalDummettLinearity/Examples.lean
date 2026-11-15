import Lemmatheca.PropositionalDummettLinearity.Frames
import Lemmatheca.IntuitionisticPropositionalFiniteFiltrations.Examples
import Lemmatheca.PropositionalWeakExcludedMiddle.Examples
import Lemmatheca.IntuitionisticPropositionalTreeCountermodels.Examples

namespace Lemmatheca.Entry.PropositionalDummettLinearity
open Lemmatheca.MathematicalLogic.Propositional
open Lemmatheca.ProofTheory.Intuitionistic
open Kripke Dummett Extensions
open Lemmatheca.Entry.IntuitionisticPropositionalTreeCountermodels
universe u

/-- The left and right middle worlds generate the two separate atom upsets. -/
def diamondComparisonModel : Model ℕ Diamond := twoUpsetModel diamondLeft diamondRight

theorem diamond_comparison_values (p : ℕ) :
    ¬ diamondComparisonModel.valuation diamondRoot p ∧
      (diamondComparisonModel.valuation diamondLeft p ↔ p = 0) ∧
      (diamondComparisonModel.valuation diamondRight p ↔ p = 1) ∧
      (diamondComparisonModel.valuation diamondTop p ↔ p = 0 ∨ p = 1) := by
  simp [diamondComparisonModel, twoUpsetModel, diamondRoot, diamondLeft,
    diamondRight, diamondTop]

theorem diamond_frame_wem (A : PropFormula ℕ) :
    FrameValid Diamond (WeakExcludedMiddle.wem A) := by
  apply (WeakExcludedMiddle.finite_rooted_wem_iff_greatest diamondRoot
    (fun _ => bot_le)).mpr
    ⟨diamondTop, fun _ => le_top⟩ A

theorem diamond_countermodel :
    Countermodel diamondComparisonModel diamondRoot ∅ (linearity (.atom 0) (.atom 1)) := by
  refine ⟨?_, ?_⟩
  · intro A hA
    exact hA.elim
  · exact (incomparable_countervaluation diamondRoot diamondLeft diamondRight
      (by decide) (by decide) (by decide) (by decide)).2.2.2.2.2.2

theorem not_kc_linearity :
    ¬ SchemaConsequence WeakExcludedMiddle.axioms ∅ (linearity (.atom (0 : ℕ)) (.atom 1)) := by
  intro h
  apply diamond_countermodel.2
  apply schemaConsequence_sound WeakExcludedMiddle.axioms ∅ _ ?_ h
    diamondComparisonModel diamondRoot diamond_countermodel.1
  intro B hB
  obtain ⟨A, rfl⟩ := hB
  exact diamond_frame_wem A

theorem not_intuitionistic_linearity :
    ¬ Lemmatheca.ProofTheory.Intuitionistic.Derives ∅ (linearity (.atom (0 : ℕ)) (.atom 1)) := by
  intro h
  apply not_kc_linearity
  apply (schemaConsequence_iff_union _ _ _).mpr
  exact h.weaken (Set.empty_subset _)

theorem chain_schema_valid {α : Type u} (A B : PropFormula α) :
    FrameValid Bool (linearity A B) := by
  intro M w
  apply linear_cone_forces_linearity M w ?_ A B
  intro u v _ _
  cases u <;> cases v <;> decide

theorem not_lc_excluded_middle :
    ¬ SchemaConsequence axioms ∅ (.disj (.atom (0 : ℕ)) (.neg (.atom 0))) := by
  intro h
  apply Lemmatheca.Entry.IntuitionisticKripkeSemantics.chain_not_excluded_middle (0 : ℕ)
  apply schemaConsequence_sound axioms ∅ _ ?_ h
    (Lemmatheca.Entry.IntuitionisticKripkeSemantics.chainModel 0) false
    (by intro A hA; cases hA)
  intro E hE
  obtain ⟨⟨A, B⟩, rfl⟩ := hE
  exact chain_schema_valid A B


theorem discrete_local_not_global :
    @LocallyLinear Bool discretePreorder ∧
      ¬ (∀ u v : Bool, @LE.le Bool discretePreorder.toLE u v ∨
        @LE.le Bool discretePreorder.toLE v u) := by
  constructor
  · intro w u v hwu hwv
    exact Or.inl (hwu.symm.trans hwv)
  · intro h
    have he := h false true
    rcases he with he | he
    · exact Bool.false_ne_true he
    · exact Bool.false_ne_true he.symm

theorem discrete_schema_valid {α : Type u} (A B : PropFormula α) :
    @FrameValid α Bool discretePreorder inferInstance (linearity A B) := by
  intro M w
  apply @linear_cone_forces_linearity α Bool discretePreorder M w ?_ A B
  exact discrete_local_not_global.1 w

end Lemmatheca.Entry.PropositionalDummettLinearity
