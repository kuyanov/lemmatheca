import Lemmatheca.HighDegreesAndDomination.Reverse
import Lemmatheca.LowSimpleSets.Lowness

/-! Degree closure and the stronger quantifier pattern than hyperimmunity. -/
namespace Lemmatheca.ComputabilityTheory.HighDegreesAndDomination

open UniversalComputation OracleComputation TuringDegrees TuringJump HyperimmuneDegrees

noncomputable section

theorem high_upward {A B : Set ℕ} (hAB : Reducible A B) (hA : High A) : High B := by
  exact reducible_trans hA (manyOne_imp_reducible (jump_monotone hAB))

theorem high_degree_invariant {A B : Set ℕ} (hAB : Equivalent A B) : High A ↔ High B := by
  exact ⟨fun h => high_upward hAB.1 h, fun h => high_upward hAB.2 h⟩

theorem dominates_hyperimmune (g : ℕ → ℕ) (hg : DominatesComputable g) :
    HyperimmuneFunction g := by
  rintro ⟨h, hc, hh⟩
  have hp := hg (fun n => h n + 1) (Primrec.succ.to_comp.comp hc)
  obtain ⟨n, hn⟩ := (hp.and hh).exists
  change h n + 1 ≤ g n ∧ g n ≤ h n at hn
  omega

theorem high_hyperimmune (A : Set ℕ) (hA : High A) : HasHyperimmuneDegree A := by
  obtain ⟨g, hc, hg⟩ := high_computes_dominating A hA
  exact ⟨g, hc, dominates_hyperimmune g hg⟩

theorem low_not_high (A : Set ℕ) (hA : LowSimpleSets.Low A) : ¬ High A := by
  intro hh
  exact (jump_strict haltingDiagonal).2 (reducible_trans hh hA.1)

end
end Lemmatheca.ComputabilityTheory.HighDegreesAndDomination
