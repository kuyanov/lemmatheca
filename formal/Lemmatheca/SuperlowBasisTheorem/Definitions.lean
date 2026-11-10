import Lemmatheca.BoundedChangesAndStrongReductions.Characterization
import Lemmatheca.LowBasisTheorem.Basis

/-! Superlowness and the literal precomposition of prefix tables. -/
namespace Lemmatheca.ComputabilityTheory.SuperlowBasisTheorem

open UniversalComputation StrongReductions TuringDegrees TuringJump

noncomputable section
set_option backward.isDefEq.respectTransparency false

def Superlow (X : Set ℕ) : Prop := TruthTableReducible (jump X) haltingDiagonal

theorem superlow_low (X : Set ℕ) (hX : Superlow X) : LowSimpleSets.Low X := by
  exact (LowSimpleSets.low_iff_jump_below_halting X).mpr
    (wtt_imp_turing (tt_imp_wtt hX))

def precomposeData (f : ℕ → ℕ) (s : TableData) : TableData :=
  ⟨fun e => s.bound (f e), fun e w => s.table (f e) w⟩

theorem precompose_scheme (f : ℕ → ℕ) (hf : Computable f) (s : TableData)
    (hs : IsScheme s) : IsScheme (precomposeData f s) := by
  exact ⟨hs.1.comp hf,
    hs.2.1.comp ((hf.comp Computable.fst).pair Computable.snd),
    fun e w => hs.2.2 (f e) w⟩

theorem precompose_presents (A B C : Set ℕ) (f : ℕ → ℕ) (hf : Computable f)
    (hm : ∀ e, e ∈ A ↔ f e ∈ B) (s : TableData) (hs : Presents s B C) :
    Presents (precomposeData f s) A C := by
  refine ⟨precompose_scheme f hf s hs.1, ?_⟩
  intro e
  change s.table (f e) (PostsTheorem.prefixCode C (s.bound (f e))) = _
  rw [hs.2 (f e)]
  by_cases he : e ∈ A
  · have hb := (hm e).mp he
    simp [indicator, he, hb]
  · have hb : f e ∉ B := fun h => he ((hm e).mpr h)
    simp [indicator, he, hb]

theorem superlow_downward {X Y : Set ℕ} (hXY : Reducible X Y) (hY : Superlow Y) :
    Superlow X := by
  obtain ⟨f, hf, hm⟩ := jump_monotone hXY
  obtain ⟨s, hs⟩ := hY
  exact ⟨precomposeData f s,
    precompose_presents (jump X) (jump Y) haltingDiagonal f hf hm s hs⟩

theorem superlow_degree_invariant {X Y : Set ℕ} (hXY : Equivalent X Y) :
    Superlow X ↔ Superlow Y := by
  exact ⟨fun h => superlow_downward hXY.2 h, fun h => superlow_downward hXY.1 h⟩

end
end Lemmatheca.ComputabilityTheory.SuperlowBasisTheorem
