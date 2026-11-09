import Lemmatheca.FiniteMindChanges.Operations

/-! A recursive sufficient budget for finite Boolean expressions in enumerable sets. -/
namespace Lemmatheca.ComputabilityTheory.FiniteMindChanges

inductive BooleanExpression where
  | atom : ℕ → BooleanExpression
  | compl : BooleanExpression → BooleanExpression
  | union : BooleanExpression → BooleanExpression → BooleanExpression
  | inter : BooleanExpression → BooleanExpression → BooleanExpression

def BooleanExpression.eval (U : ℕ → Set ℕ) : BooleanExpression → Set ℕ
  | .atom i => U i
  | .compl F => (F.eval U)ᶜ
  | .union F G => F.eval U ∪ G.eval U
  | .inter F G => F.eval U ∩ G.eval U

def BooleanExpression.budget : BooleanExpression → ℕ
  | .atom _ => 1
  | .compl F => F.budget + 1
  | .union F G => F.budget + G.budget
  | .inter F G => F.budget + G.budget

theorem boolean_expression_bound (F : BooleanExpression) (U : ℕ → Set ℕ)
    (hu : ∀ i, REPred (U i)) : NCE F.budget (F.eval U) := by
  induction F with
  | atom i => exact (DifferenceEnumerable.enumerable_iff_one_change (U i)).mp (hu i)
  | compl F ih => exact nce_complement F.budget (F.eval U) ih
  | union F G ihF ihG => exact (nce_combination F.budget G.budget (F.eval U) (G.eval U) ihF ihG).1
  | inter F G ihF ihG => exact (nce_combination F.budget G.budget (F.eval U) (G.eval U) ihF ihG).2

end Lemmatheca.ComputabilityTheory.FiniteMindChanges
