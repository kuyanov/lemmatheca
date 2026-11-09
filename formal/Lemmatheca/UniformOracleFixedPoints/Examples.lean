import Lemmatheca.UniformOracleFixedPoints.Dispatch

/-! Semantic fixed points and the order of oracle-independent choices. -/
namespace Lemmatheca.Entry.UniformOracleFixedPoints

open ComputabilityTheory ComputabilityTheory.UniversalComputation
  ComputabilityTheory.OracleProgramNumberings
  ComputabilityTheory.UniformOracleFixedPoints

theorem successor_transformer_primitive : Primrec₂ (fun n (_a : ℕ) => n + 1) := by
  exact Primrec.succ.comp Primrec.fst

theorem successor_selector :
    ∃ h : ℕ → ℕ, Primrec h ∧ ∀ A : Set ℕ, ∀ a x,
      h a ≠ h a + 1 ∧ phi A (h a) x = phi A (h a + 1) x := by
  obtain ⟨h, hh, hs⟩ := parameterized_recursion successor_transformer_primitive.to_comp
  exact ⟨h, hh, fun A a x => ⟨by omega, hs A a x⟩⟩

theorem separate_oracle_bits :
    (∀ A : Set ℕ, ∃ b : ℕ, b = indicator (fun n => n ∈ A) 0) ∧
      ¬ (∃ b : ℕ, ∀ A : Set ℕ, b = indicator (fun n => n ∈ A) 0) := by
  refine ⟨fun A => ⟨indicator (fun n => n ∈ A) 0, rfl⟩, ?_⟩
  rintro ⟨b, hb⟩
  have h₀ : b = 0 := by simpa only [indicator, Set.mem_empty_iff_false, ite_false] using hb ∅
  have h₁ : b = 1 := by simpa [indicator] using hb {0}
  omega

end Lemmatheca.Entry.UniformOracleFixedPoints
