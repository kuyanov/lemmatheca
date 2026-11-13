import Lemmatheca.GlivenkosPropositionalTheorem.Stability
import Lemmatheca.PropositionalNegativeTranslation.Proofs

namespace Lemmatheca.ProofTheory.Intuitionistic.Glivenko

open Lemmatheca.MathematicalLogic.Propositional
open PropFormula
open NegativeTranslation

/-- Pointwise native double negation of exactly the allowed open premises. -/
def doubleNegationContext (Γ : Set (PropFormula ℕ)) : Set (PropFormula ℕ) :=
  (fun A => neg (neg A)) '' Γ

/-- The classical context and both intuitionistic images use the same original finite premises. -/
theorem finite_premise_glivenko (Γ : Finset (PropFormula ℕ)) (A : PropFormula ℕ) :
    Lemmatheca.MathematicalLogic.Propositional.Derives Γ A ↔
      Derives (doubleNegationContext (Γ : Set (PropFormula ℕ))) (neg (neg A)) := by
  constructor
  · intro h
    have hN : Derives (doubleNegationContext (Γ : Set (PropFormula ℕ))) (negative A) := by
      apply (classical_translate h).replace
      rintro _ ⟨B, hB, rfl⟩
      exact .implElim ((negative_double_negation B).2.weaken (Set.empty_subset _))
        (.assumption ⟨B, hB, rfl⟩)
    exact .implElim ((negative_double_negation A).1.weaken (Set.empty_subset _)) hN
  · intro h
    apply Lemmatheca.MathematicalLogic.Propositional.derives_complete
    intro b hΓ
    have hv := boolean_sound h b (by
      rintro _ ⟨B, hB, rfl⟩
      simpa [Satisfies, eval] using hΓ B hB)
    simpa [Satisfies, eval] using hv

theorem unchanged_premise_glivenko (Γ : Finset (PropFormula ℕ)) (A : PropFormula ℕ) :
    Lemmatheca.MathematicalLogic.Propositional.Derives Γ A ↔
      Derives (Γ : Set (PropFormula ℕ)) (neg (neg A)) := by
  constructor
  · intro h
    apply ((finite_premise_glivenko Γ A).mp h).replace
    rintro _ ⟨B, hB, rfl⟩
    exact .implElim ((double_negation_intro B).weaken (Set.empty_subset _))
      (.assumption hB)
  · intro h
    apply Lemmatheca.MathematicalLogic.Propositional.derives_complete
    intro b hΓ
    have hv := boolean_sound h b hΓ
    simpa [Satisfies, eval] using hv

theorem stable_consequence_iff (Γ : Finset (PropFormula ℕ)) (A : PropFormula ℕ)
    (hA : Stable A) :
    Lemmatheca.MathematicalLogic.Propositional.Derives Γ A ↔
      Derives (Γ : Set (PropFormula ℕ)) A := by
  constructor
  · intro h
    exact .implElim (hA.weaken (Set.empty_subset _))
      ((unchanged_premise_glivenko Γ A).mp h)
  · intro h
    apply (unchanged_premise_glivenko Γ A).mpr
    exact .implElim ((double_negation_intro A).weaken (Set.empty_subset _)) h

end Lemmatheca.ProofTheory.Intuitionistic.Glivenko
