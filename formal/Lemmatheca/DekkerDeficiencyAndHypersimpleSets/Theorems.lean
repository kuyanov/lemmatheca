import Lemmatheca.DekkerDeficiencyAndHypersimpleSets.Arrays

namespace Lemmatheca.ComputabilityTheory.DekkerDeficiencyAndHypersimpleSets

open UniversalComputation OracleComputation HyperimmuneDegrees TuringDegrees

noncomputable section

theorem deficiency_equivalent (a : ℕ → ℕ) (ha : Function.Injective a) (hc : Computable a) :
    Equivalent (deficiency a) (Set.range a) := by
  obtain ⟨p, hp⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp hc.partrec)
  exact ⟨⟨prefixDecisionCode p, deficiency_reduction a ha p (fun n => congrFun hp n)⟩,
    ⟨recoverCode p, recover_reduction a ha p (fun n => congrFun hp n)⟩⟩

theorem deficiency_noncomputable (a : ℕ → ℕ) (ha : Function.Injective a) (hc : Computable a)
    (hnc : ¬ ComputablePred (Set.range a)) : ¬ ComputablePred (deficiency a) := by
  intro hD
  exact hnc (computable_of_reducible (deficiency_equivalent a ha hc).2 hD)

theorem deficiency_infinite (a : ℕ → ℕ) (ha : Function.Injective a) (hc : Computable a)
    (hnc : ¬ ComputablePred (Set.range a)) : (deficiency a).Infinite := by
  intro hfinite
  exact deficiency_noncomputable a ha hc hnc (SimpleSets.finite_decidable hfinite)

theorem nondeficient_hyperimmune (a : ℕ → ℕ) (ha : Function.Injective a) (hc : Computable a)
    (hnc : ¬ ComputablePred (Set.range a)) : HyperimmuneSet (nondeficient a) := by
  exact (hyperimmune_iff_no_array (nondeficient a)).mpr
    ⟨nondeficient_infinite a ha, no_array_hits a ha hc hnc⟩

theorem deficiency_hypersimple (a : ℕ → ℕ) (ha : Function.Injective a) (hc : Computable a)
    (hnc : ¬ ComputablePred (Set.range a)) : Hypersimple (deficiency a) := by
  exact ⟨deficiency_ce a hc, nondeficient_hyperimmune a ha hc hnc⟩

theorem every_nonzero_ce_degree (d : Degree) (hne : d ≠ zeroDegree)
    (hce : ∃ A : Set ℕ, REPred A ∧ degree A = d) :
    ∃ a : ℕ → ℕ, Computable a ∧ Function.Injective a ∧
      Hypersimple (deficiency a) ∧ degree (deficiency a) = d := by
  obtain ⟨A, hA, hdegree⟩ := hce
  have hnc : ¬ ComputablePred A := by
    intro hc
    exact hne (hdegree.symm.trans ((degree_eq_zero_iff A).mpr hc))
  have hi : A.Infinite := fun hfinite => hnc (SimpleSets.finite_decidable hfinite)
  obtain ⟨a, hc, ha, hrange⟩ := EffectiveEnumerations.infinite_ce_injective_enumeration A hA hi
  have hnc' : ¬ ComputablePred (Set.range a) := by simpa only [hrange] using hnc
  refine ⟨a, hc, ha, deficiency_hypersimple a ha hc hnc', ?_⟩
  calc
    degree (deficiency a) = degree (Set.range a) :=
      le_antisymm (deficiency_equivalent a ha hc).1 (deficiency_equivalent a ha hc).2
    _ = d := by rw [hrange]; exact hdegree

end
end Lemmatheca.ComputabilityTheory.DekkerDeficiencyAndHypersimpleSets
