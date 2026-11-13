import Lemmatheca.AnalyticPropositionalProofSearch.Native

namespace Lemmatheca.Entry.AnalyticPropositionalProofSearch

open Lemmatheca.ProofTheory.ClassicalPropositional
open AnalyticSearch

def successInput : Input := [.or (.neg 0) (.neg 1), .and (.pos 1) (.pos 0)]

theorem successful_search : (search ∅ successInput).succeeds = true := by
  simp [successInput, search, terminal, leastClash, clashIndices,
    positiveIndices, negativeIndices, Result.transport, Result.succeeds]
  rfl

theorem successful_leaf_indices :
    (leastClash ({.neg 0, .neg 1, .pos 1} : Sequent ℕ)).map Subtype.val = some 1 ∧
    (leastClash ({.neg 0, .neg 1, .pos 0} : Sequent ℕ)).map Subtype.val = some 0 := by
  decide

def failedInput : Input := [.and (.pos 0) (.pos 1), .neg 0]

def failedValuation (i : ℕ) : Bool := decide (i = 0)

theorem failed_second_branch : search ∅ failedInput = .counter failedValuation := by
  simp [failedInput, search, terminal, leastClash, clashIndices,
    positiveIndices, negativeIndices, Result.transport]
  change Result.counter (terminalValuation ({.neg 0, .pos 1} : Sequent ℕ)) =
    (Result.counter failedValuation : Result (context ∅ failedInput))
  congr 1
  funext i
  simp [terminalValuation, negativeIndices, failedValuation]

theorem failed_first_branch_succeeds :
    (search ∅ [.pos 0, .neg 0]).succeeds = true := by
  simp [search, terminal, leastClash, clashIndices, positiveIndices,
    negativeIndices, Result.transport, Result.succeeds]

theorem empty_input : search ∅ [] = .counter (fun _ => false) := by
  simp [search, terminal, leastClash, clashIndices, positiveIndices, negativeIndices,
    Result.transport]
  funext i
  simp [terminalValuation, negativeIndices]

theorem truth_input : (search ∅ [.top]).succeeds = true := by
  rw [search]
  rfl

theorem bottom_input : search ∅ [.bot] = .counter (fun _ => false) := by
  rw [search, empty_input]
  rfl

theorem repeated_input : search ∅ [.pos 0, .pos 0] = .counter (fun _ => false) := by
  simp [search, terminal, leastClash, clashIndices, positiveIndices, negativeIndices,
    Result.transport]
  funext i
  simp [terminalValuation, negativeIndices]

/-- A genuine schematic backward disjunction-rule edge. -/
def OrBackwardStep (Γ Δ : Sequent ℕ) : Prop :=
  ∃ (Θ : Sequent ℕ) (A B : Nnf ℕ),
    Γ = insert (.or A B) Θ ∧ Δ = insert A (insert B Θ)

def loopContext : Sequent ℕ := {.or (.pos 0) (.pos 1), .pos 0, .pos 1}

/-- This constant infinite trace is not a finite primitive proof tree. -/
theorem retained_principal_loop :
    ∀ n : ℕ, OrBackwardStep ((fun _ : ℕ => loopContext) n)
      ((fun _ : ℕ => loopContext) (n + 1)) := by
  intro n
  refine ⟨loopContext, .pos 0, .pos 1, ?_, ?_⟩
  · simp [loopContext]
  · simp [loopContext]

end Lemmatheca.Entry.AnalyticPropositionalProofSearch
