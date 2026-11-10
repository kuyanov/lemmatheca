import Lemmatheca.BoundedChangesAndStrongReductions.Characterization
import Lemmatheca.TruthTableAndWeakTruthTableReductions.Examples

/-! A concrete parity row and the positive-answer partial guard in the question. -/
namespace Lemmatheca.Entry.BoundedChangesAndStrongReductions

open Lemmatheca.ComputabilityTheory
open UniversalComputation LimitComputability BoundedChangesStrongReductions
open OracleComputation StrongReductions PostsTheorem

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Classical

theorem two_of_three_table (a : Approximation) (hc : Computable₂ a) (b : ℕ → ℕ)
    (x w : ℕ) (hb : b x = 3)
    (h0 : beta w (thresholdQuery a hc x 0) = 1)
    (h1 : beta w (thresholdQuery a hc x 1) = 1)
    (h2 : beta w (thresholdQuery a hc x 2) = 0) :
    thresholdTable a hc b x w = 0 := by
  simp [thresholdTable, hb, Finset.sum_range_succ, h0, h1, h2]

def positiveGuard : Code :=
  subst complementQuery Lemmatheca.Entry.TruthTableAndWeakTruthTableReductions.partialOneQuery

theorem positive_guard_eval (C : Set ℕ) (x : ℕ) :
    eval C positiveGuard x = if 0 ∈ C then Part.some 0 else Part.none := by
  rw [positiveGuard, subst_eval Cᶜ C complementQuery (complement_query_eval C),
    Lemmatheca.Entry.TruthTableAndWeakTruthTableReductions.partial_one_query_eval]
  by_cases h : 0 ∈ C <;> simp [h]

theorem positive_guard_trace (x : ℕ) :
    Derives positiveGuard x [(0, 1)] 0 ∧ Consistent ({0} : Set ℕ) [(0, 1)] ∧
      useBound [(0, 1)] = 1 := by
  have hq : Derives Code.query 0 [(0, 1)] 1 := Derives.query 0 1 (Or.inr rfl)
  have hz : Derives (embed zeroTest) 1 [] 0 :=
    (embed_empty_trace zeroTest 1 0).mp
      (Part.eq_some_iff.mp (by simp [zeroTest_eval]))
  have hcomp : Derives complementQuery 0 [(0, 1)] 0 := by
    simpa only [complementQuery, List.append_nil] using Derives.comp hq hz
  have hcall : Derives (.comp complementQuery .zero) x [(0, 1)] 0 := by
    simpa using Derives.comp (Derives.zero x) hcomp
  have hp : Derives (.pair .zero (.comp complementQuery .zero)) x [(0, 1)] (Nat.pair 0 0) := by
    simpa using Derives.pair (Derives.zero x) hcall
  have hr : Derives (.prec .zero Lemmatheca.Entry.OracleComputation.never)
      (Nat.pair 0 0) [] 0 := Derives.prec_zero (Derives.zero 0)
  refine ⟨?_, ?_, ?_⟩
  · change Derives (.comp (.prec .zero Lemmatheca.Entry.OracleComputation.never)
      (.pair .zero (.comp complementQuery .zero))) x [(0, 1)] 0
    simpa using Derives.comp hp hr
  · simp [Consistent, indicator]
  · simp [useBound, querySet]

theorem positive_guard_bounded :
    BoundedReduction positiveGuard (fun _ => 1) ∅ ({0} : Set ℕ) := by
  refine ⟨Computable.const 1, fun x => ?_⟩
  obtain ⟨ht, hc, hu⟩ := positive_guard_trace x
  refine ⟨[(0, 1)], ?_, hc, hu.le⟩
  simpa [indicator] using ht

theorem positive_guard_partial :
    (∀ x, eval (∅ : Set ℕ) positiveGuard x = Part.none) ∧ ¬ AllOracleTotal positiveGuard := by
  constructor
  · intro x
    simp [positive_guard_eval]
  · intro ht
    have hd := ht (∅ : Set ℕ) 0
    simp [positive_guard_eval] at hd

theorem empty_zero_width (B : Set ℕ) :
    Presents (constantData (fun _ => 0)) ∅ B ∧
      (constantData (fun _ => 0)).bound = fun _ => 0 := by
  constructor
  · refine ⟨⟨Computable.const 0, Computable.const 0, fun _ _ => Or.inl rfl⟩, ?_⟩
    intro x
    simp [constantData, indicator]
  · rfl

end
end Lemmatheca.Entry.BoundedChangesAndStrongReductions
