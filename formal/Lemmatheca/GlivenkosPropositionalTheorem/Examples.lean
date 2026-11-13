import Lemmatheca.GlivenkosPropositionalTheorem.Consequences
import Lemmatheca.IntuitionisticKripkeSemantics.Examples

namespace Lemmatheca.Entry.GlivenkosPropositionalTheorem

open Lemmatheca.MathematicalLogic.Propositional (PropFormula Tautology)
open Lemmatheca.MathematicalLogic.Propositional.PropFormula
open Lemmatheca.ProofTheory.Intuitionistic
open NegativeTranslation

/-- The old two-leaf fork is the actual countermodel to the disjunction of two stable negations. -/
theorem weak_em_countermodel :
    ¬ Kripke.Forces (IntuitionisticKripkeSemantics.forkModel (0 : ℕ) 1) .root
      (disj (neg (atom 0)) (neg (neg (atom 0)))) := by
  rintro (hn | hnn)
  · exact hn .left (Or.inl rfl) rfl
  · apply hnn .right (Or.inl rfl)
    intro z hz hp
    rcases hz with hz | hz
    · cases hz
    · subst z
      exact (by decide : (0 : ℕ) ≠ 1) hp

theorem weak_em_tautology : Tautology
    (disj (neg (atom (0 : ℕ))) (neg (neg (atom 0)))) := by
  intro b
  cases h : b 0 <;>
    simp [Lemmatheca.MathematicalLogic.Propositional.Satisfies,
      Lemmatheca.MathematicalLogic.Propositional.eval, h]

/-- The displayed stable disjuncts have an unprovable, unstable disjunction. -/
theorem stable_disjunction_failure :
    Stable (neg (atom (0 : ℕ))) ∧ Stable (neg (neg (atom (0 : ℕ)))) ∧
      ¬ Derives ∅ (disj (neg (atom (0 : ℕ))) (neg (neg (atom 0)))) ∧
      ¬ Stable (disj (neg (atom (0 : ℕ))) (neg (neg (atom 0)))) := by
  have hnot : ¬ Derives ∅
      (disj (neg (atom (0 : ℕ))) (neg (neg (atom 0)))) := by
    apply Kripke.countermodel_not_derivable
      (IntuitionisticKripkeSemantics.forkModel (0 : ℕ) 1) .root
    exact ⟨by simp [Kripke.ForcesContext], weak_em_countermodel⟩
  refine ⟨stable_neg _, stable_neg _, hnot, ?_⟩
  intro hStable
  apply hnot
  exact (Glivenko.stable_theorem_iff _ hStable).mp
    ((Lemmatheca.MathematicalLogic.Propositional.theorem_iff_tautology _).mpr
      weak_em_tautology)

/-- The exact single-premise consequence does not imply its assumption-free double negation. -/
theorem discarded_premise :
    Lemmatheca.MathematicalLogic.Propositional.Derives {atom (0 : ℕ)} (atom 0) ∧
      Derives {neg (neg (atom (0 : ℕ)))} (neg (neg (atom 0))) ∧
      ¬ Derives ∅ (neg (neg (atom (0 : ℕ)))) := by
  refine ⟨.assumption (by simp), .assumption (by simp), ?_⟩
  intro h
  have hv := boolean_sound h (fun _ => false) (by simp)
  simp [Lemmatheca.MathematicalLogic.Propositional.eval] at hv

theorem no_double_negated_falsum :
    ¬ Derives ∅ (neg (neg (falsum : PropFormula ℕ))) := by
  intro h
  have hv := boolean_sound h (fun _ => false) (by simp)
  simp [Lemmatheca.MathematicalLogic.Propositional.eval] at hv

end Lemmatheca.Entry.GlivenkosPropositionalTheorem
