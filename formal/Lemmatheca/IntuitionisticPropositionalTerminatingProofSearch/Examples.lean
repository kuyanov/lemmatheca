import Lemmatheca.IntuitionisticPropositionalTerminatingProofSearch.Native

namespace Lemmatheca.Entry.IntuitionisticPropositionalTerminatingProofSearch
open Lemmatheca.MathematicalLogic.Propositional
open PropFormula
open Lemmatheca.ProofTheory.Intuitionistic
open Lemmatheca.ProofTheory.Intuitionistic.G4ip.Search
universe u
variable {α : Type u} [DecidableEq α]

private theorem emptyAtom_none (n : ℕ) (p : α) :
    solveFuel n ([], atom p) = none := by
  cases n <;> rfl

private theorem atomicBottom_none (n : ℕ) (p : α) :
    solveFuel n ([atom p], falsum) = none := by
  cases n <;> rfl

private theorem emptyNegAtom_none (n : ℕ) (p : α) :
    solveFuel n ([], impl (atom p) falsum) = none := by
  cases n with
  | zero => rfl
  | succ n =>
      change tryMoves (solveFuel n) [.implRight (atom p) falsum] = none
      simp only [tryMoves, Move.premises, solveAll, atomicBottom_none]
      rfl

private theorem expandedMiddle_none (n : ℕ) (p : α) :
    solveFuel n ([], disj (atom p) (impl (atom p) falsum)) = none := by
  cases n with
  | zero => rfl
  | succ n =>
      change tryMoves (solveFuel n)
        [.disjRightLeft (atom p) (impl (atom p) falsum),
          .disjRightRight (atom p) (impl (atom p) falsum)] = none
      simp only [tryMoves, Move.premises, solveAll, emptyAtom_none, emptyNegAtom_none]
      rfl

theorem excludedMiddle_rejected (p : α) : prove [] (disj (atom p) (neg (atom p))) = false := by
  change (solveFuel _ ([], disj (atom p) (impl (atom p) falsum))).isSome = false
  rw [expandedMiddle_none]
  rfl

theorem doubleNegatedExcludedMiddle_accepted (p : α) :
    prove [] (neg (neg (disj (atom p) (neg (atom p))))) = true := by
  apply (native_decision _ _).mpr
  simpa using double_negated_excluded_middle (atom p)

theorem numbered_runs :
    prove ([] : List (PropFormula ℕ)) (disj (atom 0) (neg (atom 0))) = false ∧
      prove ([] : List (PropFormula ℕ)) (neg (neg (disj (atom 0) (neg (atom 0))))) = true := by
  exact ⟨excludedMiddle_rejected 0, doubleNegatedExcludedMiddle_accepted 0⟩

theorem backtracking (p q : α) :
    prove [] (atom q) = false ∧ prove [] (disj (atom q) (impl (atom p) (atom p))) = true ∧
      problemWeight ([], disj (atom q) (impl (atom p) (atom p))) = 8 := by
  refine ⟨?_, ?_, ?_⟩
  · change (solveFuel _ ([], atom q)).isSome = false
    rw [emptyAtom_none]
    rfl
  · apply (native_decision _ _).mpr
    exact .disjIntroRight (.implIntro (.assumption (by simp)))
  · simp [problemWeight, underlying,
      Lemmatheca.ProofTheory.Intuitionistic.G4ip.goalWeight,
      Lemmatheca.ProofTheory.Intuitionistic.G4ip.contextWeight,
      Lemmatheca.ProofTheory.Intuitionistic.G4ip.weight]

theorem insufficientFuel (p : α) :
    solveFuel 0 ([atom p], atom p) = none ∧
      (solveFuel 1 ([atom p], atom p)).isSome = true ∧ problemWeight ([atom p], atom p) = 4 := by
  simp [solveFuel, leaf, problemWeight, underlying,
    Lemmatheca.ProofTheory.Intuitionistic.G4ip.goalWeight,
    Lemmatheca.ProofTheory.Intuitionistic.G4ip.contextWeight,
    Lemmatheca.ProofTheory.Intuitionistic.G4ip.weight, Option.isSome]

end Lemmatheca.Entry.IntuitionisticPropositionalTerminatingProofSearch
