import Lemmatheca.IntuitionisticPropositionalFiniteModelProperty.Search
import Lemmatheca.IntuitionisticKripkeSemantics.Examples

namespace Lemmatheca.Entry.IntuitionisticPropositionalFiniteModelProperty

open Lemmatheca.MathematicalLogic.Propositional
open PropFormula
open Lemmatheca.ProofTheory.Intuitionistic
open FiniteModels

/-- The exact native excluded-middle formula in the worked finite problem. -/
def excludedMiddle : Formula := disj (atom 0) (neg (atom 0))

def exampleRelation : RelationCode 2 := fun i j => decide (i ≤ j)

def exampleValuation : ValuationCode 2 {0} := fun i _ => decide (i = 1)

theorem example_problem :
    problemSubformulas ∅ excludedMiddle = {atom 0, neg (atom 0), excludedMiddle} ∧
      problemAtoms ∅ excludedMiddle = {0} ∧ worldBound ∅ excludedMiddle = 8 := by
  decide

theorem example_code :
    Admissible exampleRelation exampleValuation ∧
      booleanForcing exampleRelation exampleValuation (atom 0) 0 = false ∧
      booleanForcing exampleRelation exampleValuation (neg (atom 0)) 0 = false ∧
      booleanForcing exampleRelation exampleValuation excludedMiddle 0 = false := by
  decide

theorem example_refute : refute [] excludedMiddle = true := by
  simp only [refute, decide_eq_true_eq]
  refine ⟨⟨2, ?_⟩, exampleRelation, (fun i _ => decide (i = 1)), 0, ?_⟩
  · change 2 < worldBound ∅ excludedMiddle + 1
    rw [example_problem.2.2]
    decide
  · decide

/-- The actual truth theories of the existing two-world chain. -/
def chainTheory (w : Bool) : Canonical.PrimeWorld :=
  ⟨Canonical.truthTheory (IntuitionisticKripkeSemantics.chainModel (0 : ℕ)) w,
    Canonical.truthTheory_prime _ _⟩

theorem representative_ambiguity :
    trace {impl (atom 0) (atom 0)} (chainTheory false) =
        trace {impl (atom 0) (atom 0)} (chainTheory true) ∧
      atom 0 ∉ (chainTheory false).val ∧ atom 0 ∈ (chainTheory true).val := by
  have hImp (w : Bool) : impl (atom 0) (atom 0) ∈ (chainTheory w).val := by
    intro z _ hp
    exact hp
  refine ⟨?_, (IntuitionisticKripkeSemantics.chain_values (0 : ℕ)).1, ?_⟩
  · ext B
    rw [trace_mem, trace_mem]
    simp only [Finset.mem_singleton]
    constructor
    · rintro ⟨rfl, _⟩
      exact ⟨rfl, hImp true⟩
    · rintro ⟨rfl, _⟩
      exact ⟨rfl, hImp false⟩
  · exact ⟨rfl, rfl⟩

theorem missing_closure_fails :
    Kripke.Forces (traceModel {neg (atom 0)})
        (traceWorld {neg (atom 0)} (chainTheory false)) (neg (atom 0)) ∧
      neg (atom 0) ∉ (chainTheory false).val := by
  constructor
  · intro w _ hp
    obtain ⟨T, hT⟩ := w.property
    have hs : w.val ⊆ {neg (atom 0)} := by
      rw [← hT]
      exact trace_subset _ T
    have hc := hs hp
    simp at hc
  · exact (IntuitionisticKripkeSemantics.chain_values (0 : ℕ)).2.1

theorem empty_traces :
    Fintype.card (TraceWorld ∅) = 1 ∧
      ∀ w : TraceWorld ∅, w.val = ∅ ∧
        ∀ p : ℕ, ¬ Kripke.Forces (traceModel ∅) w (atom p) := by
  have hVal (w : TraceWorld ∅) : w.val = ∅ := by
    obtain ⟨T, hT⟩ := w.property
    rw [← hT]
    simp [trace]
  constructor
  · apply le_antisymm
    · simpa using (trace_card_bounds ∅).2
    · exact (trace_card_bounds ∅).1
  · intro w
    refine ⟨hVal w, ?_⟩
    intro p hp
    change atom p ∈ w.val at hp
    rw [hVal w] at hp
    simp at hp

end Lemmatheca.Entry.IntuitionisticPropositionalFiniteModelProperty
