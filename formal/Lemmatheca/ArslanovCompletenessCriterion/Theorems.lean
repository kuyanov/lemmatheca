import Lemmatheca.ArslanovCompletenessCriterion.DelayedCopy

namespace Lemmatheca.ComputabilityTheory.ArslanovCompletenessCriterion

open UniversalComputation OracleComputation

noncomputable section

theorem arslanov_criterion (A : Set ℕ) (hA : REPred (fun n => n ∈ A)) :
    TuringDegrees.Reducible haltingDiagonal A ↔ ComputesFPF A := by
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨haltingFPF, ⟨subst c haltingFPFCode, funext (halting_fpf_substitution A c hc)⟩,
      halting_fpf⟩
  · rintro ⟨f, ⟨c, hc⟩, hf⟩
    obtain ⟨a, ha⟩ := (enumerable_iff_index (fun n => n ∈ A)).mp hA
    have hindex : EffectiveEnumerations.indexSet a = A := by
      ext n
      exact (ha n).symm
    let e := OracleProgramNumberings.encodeCode c
    have he (n : ℕ) : OracleProgramNumberings.phi A e n = Part.some (f n) := by
      simpa only [e, OracleProgramNumberings.phi, OracleProgramNumberings.decode_encode]
        using congrFun hc n
    have ht (n : ℕ) : (OracleProgramNumberings.phi A e n).Dom := by rw [he]; trivial
    exact ⟨haltingDecisionCode a e, fpf_halting_reduction A a e f ht hindex he hf⟩

theorem incomplete_final_guess (A : Set ℕ) (a e : ℕ) (f : ℕ → ℕ)
    (ht : ∀ n, (OracleProgramNumberings.phi A e n).Dom)
    (ha : EffectiveEnumerations.indexSet a = A)
    (he : ∀ n, OracleProgramNumberings.phi A e n = Part.some (f n))
    (hinc : ¬ TuringDegrees.Reducible haltingDiagonal A) :
    ∃ n, ∃ hn : n ∈ haltingDiagonal,
      approximation a e (firstEntry n hn) (copySelector a e n) = f (copySelector a e n) := by
  classical
  by_contra h
  have hdis : ∀ n (hn : n ∈ haltingDiagonal),
      approximation a e (firstEntry n hn) (copySelector a e n) ≠ f (copySelector a e n) := by
    intro n hn heq
    exact h ⟨n, hn, heq⟩
  have hb := disagreement_entry_bound A a e f ht ha he hdis
  exact hinc ⟨haltingDecisionCode a e, halting_decision_eval A a e ht ha hb⟩

theorem incomplete_fixed_point (A : Set ℕ) (hA : REPred (fun n => n ∈ A))
    (hinc : ¬ TuringDegrees.Reducible haltingDiagonal A) (f : ℕ → ℕ)
    (hf : PartialComputable A (fun n => Part.some (f n))) :
    ∃ i, EffectiveEnumerations.indexSet (f i) = EffectiveEnumerations.indexSet i := by
  classical
  by_contra h
  apply hinc
  apply (arslanov_criterion A hA).mpr
  exact ⟨f, hf, fun i hi => h ⟨i, hi⟩⟩

end
end Lemmatheca.ComputabilityTheory.ArslanovCompletenessCriterion
