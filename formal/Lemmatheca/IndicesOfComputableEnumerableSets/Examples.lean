import Lemmatheca.IndicesOfComputableEnumerableSets.Classification
import Lemmatheca.IndexSetCompleteness.Examples

/-! Explicit finite-state and domain counterexamples from the three answers. -/
namespace Lemmatheca.Entry.IndicesOfComputableEnumerableSets
open Lemmatheca.ComputabilityTheory
open ComputableDomainIndices ThirdLevelIndexSets EffectiveEnumerations

theorem simultaneous_events_answer (z : ℕ) :
    (bump (bump [] 0) 0).toFinset = {0,1} ∧ rowCode 0 z ≠ haltingCode 0 := by
  exact ⟨by decide, (tagged_codes 0 z).2.2⟩

theorem single_marker_answer :
    marker [] 1 = 1 ∧ marker (bump [] 0) 1 = 2 ∧
      (bump (bump [] 0) 1).toFinset = {0,2} ∧
        1 ∉ bump (bump [] 0) 1 ∧
          marker (bump (bump [] 0) 1) 0 = 1 ∧
            marker (bump (bump [] 0) 1) 1 = 3 := by
  decide

theorem cofinite_promise_answer :
    Lemmatheca.Entry.IndexSetCompleteness.evenIndex ∈ ComputableIndices ∧
      Lemmatheca.Entry.IndexSetCompleteness.evenIndex ∉ CofiniteIndices := by
  constructor
  · change ComputablePred (indexSet Lemmatheca.Entry.IndexSetCompleteness.evenIndex)
    have hm : PrimrecPred (fun n : ℕ => n % 2 = 0) :=
      Primrec.eq.comp (Primrec.nat_mod.comp Primrec.id (Primrec.const 2)) (Primrec.const 0)
    exact hm.computablePred.of_eq
      (fun x => (Lemmatheca.Entry.IndexSetCompleteness.evenIndex_domain x).symm)
  · change ¬ ((indexSet Lemmatheca.Entry.IndexSetCompleteness.evenIndex)ᶜ).Finite
    intro hf
    obtain ⟨a, ha⟩ := hf.bddAbove
    have hm : 2 * (a + 1) + 1 ∉ indexSet Lemmatheca.Entry.IndexSetCompleteness.evenIndex := by
      rw [Lemmatheca.Entry.IndexSetCompleteness.evenIndex_domain]
      omega
    have := ha hm
    omega

end Lemmatheca.Entry.IndicesOfComputableEnumerableSets
