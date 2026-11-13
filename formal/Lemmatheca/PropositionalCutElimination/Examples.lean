import Lemmatheca.PropositionalCutElimination.Subformulas

namespace Lemmatheca.Entry.PropositionalCutElimination

open Lemmatheca.ProofTheory.ClassicalPropositional

universe u
variable {α : Type u} [DecidableEq α]

private theorem cast_size {Γ Δ : Sequent α} (h : Γ = Δ) (p : CutProof Γ) :
    (Eq.mp (congrArg (CutProof (α := α)) h) p).size = p.size := by
  cases h
  rfl
private theorem cast_occurrences {Γ Δ : Sequent α} (h : Γ = Δ) (p : CutProof Γ) :
    (Eq.mp (congrArg (CutProof (α := α)) h) p).occurrences = p.occurrences := by
  cases h
  rfl

/-- The specified cut of two truth leaves, concluding the truth singleton. -/
def unrelatedCut (p : α) : CutProof ({Nnf.top} : Sequent α) := by
  have h : CutProof (({Nnf.top} : Sequent α) ∪ {Nnf.top}) :=
    .cut (.pos p) (.truth (by simp)) (.truth (by simp))
  simpa using h

/-- The displayed three-node example contains both unrelated signed atoms. -/
theorem unrelated_cut_properties (p : α) :
    (unrelatedCut p).size = 3 ∧
    Nnf.pos p ∈ (unrelatedCut p).occurrences ∧
    Nnf.neg p ∈ (unrelatedCut p).occurrences ∧
    ¬ (Nnf.pos p).Subformula Nnf.top ∧
    ¬ (Nnf.neg p).Subformula Nnf.top := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold unrelatedCut
    rw [cast_size (Finset.union_self _)]
    rfl
  · unfold unrelatedCut
    rw [cast_occurrences (Finset.union_self _)]
    simp [CutProof.occurrences]
  · unfold unrelatedCut
    rw [cast_occurrences (Finset.union_self _)]
    simp [CutProof.occurrences, Nnf.dual]
  · intro h
    cases h
  · intro h
    cases h

/-- The single truth leaf offered as a cut-free replacement in the example. -/
def truthLeaf : Proof ({Nnf.top} : Sequent α) := .truth (by simp)

/-- This specified cut-free replacement consists of one rule application. -/
theorem truth_leaf_size : (truthLeaf (α := α)).size = 1 := by rfl

end Lemmatheca.Entry.PropositionalCutElimination
