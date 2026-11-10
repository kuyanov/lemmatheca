import Lemmatheca.RelativizedLimitComputability.Backward

namespace Lemmatheca.ComputabilityTheory.RelativizedLimitComputability

open OracleComputation UniversalComputation
open LimitComputability (Approximation)

noncomputable section

theorem relative_set_limit (B X : Set ℕ) :
    RelativeLimitComputable B X ↔ TuringDegrees.Reducible X (TuringJump.jump B) := by
  constructor
  · rintro ⟨a, hc, _, ha⟩
    obtain ⟨e, he⟩ := (joint_index_iff B a).mp hc
    refine ⟨OracleProgramNumberings.decodeCode (stableIndex e), fun x => ?_⟩
    exact stable_index_eval B e a he (indicator X) ha x
  · rintro ⟨c, hc⟩
    have he (x : ℕ) : OracleProgramNumberings.phi (TuringJump.jump B)
        (OracleProgramNumberings.encodeCode c) x = Part.some (indicator X x) := by
      simpa only [OracleProgramNumberings.phi, OracleProgramNumberings.decode_encode, Membership.mem, Set.Mem] using hc x
    exact ⟨binaryApproximation B (OracleProgramNumberings.encodeCode c),
      binary_joint_computable B _, binary_approximation_bits B _, binary_convergence B X _ he⟩

theorem relative_delta_two (B X : Set ℕ) :
    RelativeLimitComputable B X ↔ ArithmeticalHierarchy.Delta B 2 X := by
  rw [relative_set_limit]
  exact (PostsTheorem.delta_iff_reducible B 1 X).symm

theorem relative_function_limit (B : Set ℕ) (f : ℕ → ℕ) :
    PartialComputable (TuringJump.jump B) (fun x => Part.some (f x)) ↔
      ∃ a, JointComputableIn B a ∧ ConvergesTo a f := by
  constructor
  · rintro ⟨c, hc⟩
    have he (x : ℕ) : OracleProgramNumberings.phi (TuringJump.jump B)
        (OracleProgramNumberings.encodeCode c) x = Part.some (f x) := by
      simpa only [OracleProgramNumberings.phi, OracleProgramNumberings.decode_encode] using congrFun hc x
    exact ⟨numericalApproximation B (OracleProgramNumberings.encodeCode c),
      numerical_joint_computable B _, numerical_convergence B _ f he⟩
  · rintro ⟨a, hc, ha⟩
    obtain ⟨e, he⟩ := (joint_index_iff B a).mp hc
    refine ⟨OracleProgramNumberings.decodeCode (stableIndex e), ?_⟩
    funext x
    exact stable_index_eval B e a he f ha x

theorem ordinary_set_specialization (X : Set ℕ) :
    RelativeLimitComputable ∅ X ↔ LimitComputability.LimitComputable X := by
  constructor
  · rintro ⟨a, hc, hb, ha⟩
    exact ⟨a, (joint_empty_iff a).mp hc, hb, (characteristic_convergence a X).mp ha⟩
  · rintro ⟨a, hc, hb, ha⟩
    exact ⟨a, (joint_empty_iff a).mpr hc, hb, (characteristic_convergence a X).mpr ha⟩

theorem ordinary_function_specialization (f : ℕ → ℕ) :
    PartialComputable haltingDiagonal (fun x => Part.some (f x)) ↔
      ∃ a : Approximation, Computable₂ a ∧ ConvergesTo a f := by
  have hbase : PartialComputable haltingDiagonal (fun x => Part.some (f x)) ↔
      PartialComputable (TuringJump.jump ∅) (fun x => Part.some (f x)) := by
    rw [BusyBeaverFunctions.function_computable_iff_graph_reducible,
      BusyBeaverFunctions.function_computable_iff_graph_reducible]
    obtain ⟨hJK, hKJ⟩ := TuringJump.empty_jump_equiv_halting
    exact ⟨fun h => TuringDegrees.reducible_trans h (TuringDegrees.manyOne_imp_reducible hKJ),
      fun h => TuringDegrees.reducible_trans h (TuringDegrees.manyOne_imp_reducible hJK)⟩
  rw [hbase, relative_function_limit]
  simp_rw [joint_empty_iff]

end
end Lemmatheca.ComputabilityTheory.RelativizedLimitComputability
