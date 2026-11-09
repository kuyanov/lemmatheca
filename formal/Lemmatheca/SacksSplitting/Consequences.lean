import Lemmatheca.SacksSplitting.Lowness
import Lemmatheca.FriedbergSplitting.DisjointUnion

/-! Strict degree splitting and the nonminimality consequence. -/
namespace Lemmatheca.ComputabilityTheory.SacksSplitting

open UniversalComputation LowSimpleSets TuringDegrees TuringJump

noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem strict_incomparable_pieces (A : Set ℕ) (hA : REPred A) (hC : ¬ ComputablePred A) :
    ∃ A₀ A₁ : Set ℕ, REPred A₀ ∧ REPred A₁ ∧ Disjoint A₀ A₁ ∧ A₀ ∪ A₁ = A ∧
      Low A₀ ∧ Low A₁ ∧ ¬ ComputablePred A₀ ∧ ¬ ComputablePred A₁ ∧
      Reducible A₀ A ∧ ¬ Reducible A A₀ ∧ Reducible A₁ A ∧ ¬ Reducible A A₁ ∧
      ¬ Reducible A₀ A₁ ∧ ¬ Reducible A₁ A₀ ∧ Equivalent (join A₀ A₁) A := by
  obtain ⟨A₀, A₁, h₀, h₁, hd, hu, hl₀, hl₁, hn₀, hn₁⟩ :=
    sacks_splitting A A hA hC (LimitComputability.enumerable_limit A hA)
  have hAJ : Equivalent A (join A₀ A₁) := by
    simpa only [hu] using FriedbergSplitting.disjoint_union_join A₀ A₁ h₀ h₁ hd
  have hJA : Equivalent (join A₀ A₁) A := ⟨hAJ.2, hAJ.1⟩
  have hred := (join_reducible_iff A₀ A₁ A).mp hJA.1
  have hn₀₁ : ¬ Reducible A₀ A₁ := by
    intro hr
    exact hn₁ (reducible_trans hAJ.1
      ((join_reducible_iff A₀ A₁ A₁).mpr ⟨hr, reducible_refl A₁⟩))
  have hn₁₀ : ¬ Reducible A₁ A₀ := by
    intro hr
    exact hn₀ (reducible_trans hAJ.1
      ((join_reducible_iff A₀ A₁ A₀).mpr ⟨reducible_refl A₀, hr⟩))
  have hc₀ : ¬ ComputablePred A₀ := by
    intro hc
    obtain ⟨r, _, hr⟩ := computable_uniform A₀ hc
    exact hn₀₁ ⟨OracleComputation.embed r, hr A₁⟩
  have hc₁ : ¬ ComputablePred A₁ := by
    intro hc
    obtain ⟨r, _, hr⟩ := computable_uniform A₁ hc
    exact hn₁₀ ⟨OracleComputation.embed r, hr A₀⟩
  exact ⟨A₀, A₁, h₀, h₁, hd, hu, hl₀, hl₁, hc₀, hc₁,
    hred.1, hn₀, hred.2, hn₁, hn₀₁, hn₁₀, hJA⟩

theorem nonminimal_ce_degree (A : Set ℕ) (hA : REPred A) (hC : ¬ ComputablePred A) :
    ∃ B : Set ℕ, REPred B ∧ Low B ∧ ¬ ComputablePred B ∧
      zeroDegree < degree B ∧ degree B < degree A := by
  obtain ⟨B, _, hB, _, _, _, hlow, _, hnc, _, hBA, hnAB, _⟩ :=
    strict_incomparable_pieces A hA hC
  refine ⟨B, hB, hlow, hnc, ?_, ?_⟩
  · apply lt_of_le_of_ne (zeroDegree_le _)
    intro he
    exact hnc ((degree_eq_zero_iff B).mp he.symm)
  · exact lt_of_le_not_ge (show degree B ≤ degree A from hBA) hnAB

end
end Lemmatheca.ComputabilityTheory.SacksSplitting
