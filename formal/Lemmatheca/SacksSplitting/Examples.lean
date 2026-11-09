import Lemmatheca.SacksSplitting.Consequences

/-! A simultaneous low splitting whose join has nonlow jump. -/
namespace Lemmatheca.Entry.SacksSplitting

open Lemmatheca.ComputabilityTheory
open UniversalComputation LowSimpleSets TuringDegrees TuringJump

noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem low_join_counterexample :
    ∃ A₀ A₁ : Set ℕ, REPred A₀ ∧ REPred A₁ ∧ Disjoint A₀ A₁ ∧
      A₀ ∪ A₁ = haltingDiagonal ∧ Low A₀ ∧ Low A₁ ∧
      Equivalent (join A₀ A₁) haltingDiagonal ∧
      Equivalent (join (jump A₀) (jump A₁)) haltingDiagonal ∧
      Equivalent (jump (join A₀ A₁)) (jump haltingDiagonal) ∧
      ¬ Low (join A₀ A₁) ∧
      Reducible (join (jump A₀) (jump A₁)) (jump (join A₀ A₁)) ∧
      ¬ Reducible (jump (join A₀ A₁)) (join (jump A₀) (jump A₁)) := by
  obtain ⟨A₀, A₁, h₀, h₁, hd, hu, hl₀, hl₁, _, _⟩ :=
    SacksSplitting.sacks_splitting haltingDiagonal haltingDiagonal
      haltingDiagonal_enumerable haltingDiagonal_undecidable
      (LimitComputability.enumerable_limit haltingDiagonal haltingDiagonal_enumerable)
  have hKJ : Equivalent haltingDiagonal (join A₀ A₁) := by
    simpa only [hu] using FriedbergSplitting.disjoint_union_join A₀ A₁ h₀ h₁ hd
  have hJK : Equivalent (join A₀ A₁) haltingDiagonal := ⟨hKJ.2, hKJ.1⟩
  have hj₀ : Reducible (jump A₀) (join (jump A₀) (jump A₁)) :=
    ((join_reducible_iff _ _ _).mp (reducible_refl _)).1
  have hJJ : Equivalent (join (jump A₀) (jump A₁)) haltingDiagonal :=
    ⟨(join_reducible_iff _ _ _).mpr ⟨hl₀.1, hl₁.1⟩, reducible_trans hl₀.2 hj₀⟩
  have hjK : Equivalent (jump (join A₀ A₁)) (jump haltingDiagonal) :=
    ⟨manyOne_imp_reducible (jump_monotone hJK.1),
      manyOne_imp_reducible (jump_monotone hJK.2)⟩
  have hnlow : ¬ Low (join A₀ A₁) := by
    intro hl
    exact (jump_strict haltingDiagonal).2 (reducible_trans hjK.2 hl.1)
  have hred : Reducible (join (jump A₀) (jump A₁)) (jump (join A₀ A₁)) :=
    reducible_trans hJJ.1 (reducible_trans (jump_strict haltingDiagonal).1 hjK.2)
  have hnred : ¬ Reducible (jump (join A₀ A₁)) (join (jump A₀) (jump A₁)) := by
    intro hr
    exact (jump_strict haltingDiagonal).2 (reducible_trans hjK.2 (reducible_trans hr hJJ.1))
  exact ⟨A₀, A₁, h₀, h₁, hd, hu, hl₀, hl₁, hJK, hJJ, hjK, hnlow, hred, hnred⟩

end
end Lemmatheca.Entry.SacksSplitting
