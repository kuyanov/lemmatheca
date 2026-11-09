import Lemmatheca.TuringDegrees.Degrees

/-! Generic degree consequences reusable without the finite-extension construction. -/
namespace Lemmatheca.ComputabilityTheory.IncomparableTuringDegrees

theorem incomparable_noncomputable (A B : Set ℕ)
    (hAB : ¬ TuringDegrees.Reducible A B) (hBA : ¬ TuringDegrees.Reducible B A) :
    ¬ ComputablePred (fun x => x ∈ A) ∧ ¬ ComputablePred (fun x => x ∈ B) := by
  constructor
  · intro hA
    obtain ⟨r, _, hr⟩ := TuringDegrees.computable_uniform A hA
    exact hAB ⟨OracleComputation.embed r, hr B⟩
  · intro hB
    obtain ⟨r, _, hr⟩ := TuringDegrees.computable_uniform B hB
    exact hBA ⟨OracleComputation.embed r, hr A⟩

theorem incomparable_between (A B C : Set ℕ)
    (hAB : ¬ TuringDegrees.Reducible A B) (hBA : ¬ TuringDegrees.Reducible B A)
    (hAC : TuringDegrees.Reducible A C) (hBC : TuringDegrees.Reducible B C) :
    (TuringDegrees.zeroDegree < TuringDegrees.degree A ∧
      TuringDegrees.degree A < TuringDegrees.degree C) ∧
    (TuringDegrees.zeroDegree < TuringDegrees.degree B ∧
      TuringDegrees.degree B < TuringDegrees.degree C) := by
  have hnc := incomparable_noncomputable A B hAB hBA
  have hA : TuringDegrees.zeroDegree < TuringDegrees.degree A := by
    apply lt_of_le_of_ne (TuringDegrees.zeroDegree_le _)
    intro h
    exact hnc.1 ((TuringDegrees.degree_eq_zero_iff A).mp h.symm)
  have hB : TuringDegrees.zeroDegree < TuringDegrees.degree B := by
    apply lt_of_le_of_ne (TuringDegrees.zeroDegree_le _)
    intro h
    exact hnc.2 ((TuringDegrees.degree_eq_zero_iff B).mp h.symm)
  refine ⟨⟨hA, lt_iff_le_not_ge.mpr ⟨hAC, ?_⟩⟩,
    ⟨hB, lt_iff_le_not_ge.mpr ⟨hBC, ?_⟩⟩⟩
  · intro hCA
    exact hBA (TuringDegrees.reducible_trans hBC hCA)
  · intro hCB
    exact hAB (TuringDegrees.reducible_trans hAC hCB)

end Lemmatheca.ComputabilityTheory.IncomparableTuringDegrees
