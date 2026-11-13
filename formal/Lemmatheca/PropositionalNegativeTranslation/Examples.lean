import Lemmatheca.PropositionalNegativeTranslation.Substitution

namespace Lemmatheca.Entry.PropositionalNegativeTranslation

open Lemmatheca.MathematicalLogic.Propositional
open PropFormula
open Lemmatheca.ProofTheory.Intuitionistic.NegativeTranslation

universe u v
variable {α : Type u} {β : Type v}

/-- The actual two substituted formulas in the worked example, with their inequality. -/
theorem substitution_disjunction_example (σ : α → PropFormula β)
    (p : α) (q r : β) (hp : σ p = disj (atom q) (atom r)) :
    negative (subst σ (atom p)) =
        neg (neg (disj (neg (neg (atom q))) (neg (neg (atom r))))) ∧
      subst (fun a => negative (σ a)) (negative (atom p)) =
        neg (neg (neg (neg (disj (neg (neg (atom q))) (neg (neg (atom r))))))) ∧
      negative (subst σ (atom p)) ≠
        subst (fun a => negative (σ a)) (negative (atom p)) := by
  simp [subst, negative, hp]

end Lemmatheca.Entry.PropositionalNegativeTranslation
