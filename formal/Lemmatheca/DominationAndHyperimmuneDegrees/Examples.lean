import Lemmatheca.DominationAndHyperimmuneDegrees.HyperimmuneFree

/-! An enumerable representative and a hyperimmune representative of the halting degree. -/
namespace Lemmatheca.Entry.DominationAndHyperimmuneDegrees

open Lemmatheca.ComputabilityTheory
open HyperimmuneDegrees UniversalComputation TuringDegrees LimitComputability

noncomputable section

/-- The first-correct-prefix function is put through the same parity construction. -/
def haltingRepresentative : Set ℕ :=
  Set.range (parityGrowth haltingDiagonal
    (firstCorrectPrefix haltingTest haltingDiagonal halting_stage_converges))

theorem first_correct_need_not_settle :
    ∃ (a : Approximation) (A : Set ℕ) (hA : Converges a A),
      Computable₂ a ∧ Binary a ∧ ∃ n s, firstCorrectPrefix a A hA n < s ∧
        a s n ≠ indicator A n := by
  classical
  let a : Approximation := fun s x => if s = 2 ∧ x = 0 then 1 else 0
  have ha : Computable₂ a := by
    exact (Computable.cond
      ((Primrec.eq.comp Primrec.fst (Primrec.const 2)).and
        (Primrec.eq.comp Primrec.snd (Primrec.const 0))).decide.to_comp
      (Computable.const 1) (Computable.const 0)).of_eq (fun p => by simp [a])
  have hbin : Binary a := by
    intro s x
    dsimp only [a]
    split_ifs <;> simp
  have hconv : Converges a ∅ := by
    intro x
    refine ⟨3, fun s hs => ?_⟩
    have hn : s ≠ 2 := by omega
    simp [a, hn, UniversalComputation.indicator]
    exact fun h => h
  refine ⟨a, ∅, hconv, ha, hbin, 0, 2, ?_, ?_⟩
  · have hfirst : firstCorrectPrefix a ∅ hconv 0 ≤ 1 := by
      apply Nat.find_min'
      constructor
      · decide
      · intro x hx
        simp [a, UniversalComputation.indicator]
        exact fun h => h
    omega
  · simp [a, UniversalComputation.indicator]
    exact fun h => h

theorem enumerable_not_hyperimmune (X : Set ℕ) (hX : REPred (fun n => n ∈ X)) :
    ¬ HyperimmuneSet X := by
  intro hhi
  exact SimpleSets.immune_not_enumerable (hyperimmune_implies_immune X hhi) hX

theorem halting_hyperimmune_representative :
    HyperimmuneSet haltingRepresentative ∧
      Equivalent haltingRepresentative haltingDiagonal ∧
      ¬ REPred (fun n => n ∈ haltingRepresentative) := by
  let f := firstCorrectPrefix haltingTest haltingDiagonal halting_stage_converges
  have hhi : HyperimmuneFunction f := first_correct_prefix_hyperimmune haltingTest
    halting_stage_data.1.to_comp haltingDiagonal halting_stage_converges haltingDiagonal_undecidable
  obtain ⟨c, hc⟩ := first_correct_prefix_relative haltingTest halting_stage_data.1.to_comp
    haltingDiagonal halting_stage_converges
  have he : ∀ n, OracleComputation.eval haltingDiagonal c n = Part.some (f n) :=
    fun n => congrFun hc n
  have hs : HyperimmuneSet haltingRepresentative := parity_range_hyperimmune haltingDiagonal f hhi
  exact ⟨hs, parity_degree_equivalence haltingDiagonal f c he,
    fun hce => enumerable_not_hyperimmune haltingRepresentative hce hs⟩

end
end Lemmatheca.Entry.DominationAndHyperimmuneDegrees
