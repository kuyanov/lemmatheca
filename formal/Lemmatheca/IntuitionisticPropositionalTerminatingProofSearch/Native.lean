import Lemmatheca.IntuitionisticPropositionalTerminatingProofSearch.Search

namespace Lemmatheca.ProofTheory.Intuitionistic.G4ip.Search
open Lemmatheca.MathematicalLogic.Propositional
open PropFormula
universe u
variable {α : Type u} [DecidableEq α]

def expandGoal (H : List (PropFormula α)) (E : PropFormula α) : PresentedGoal α :=
  (H.map expandNegation, expandNegation E)

omit [DecidableEq α] in
theorem expandGoal_reduced [DecidableEq α] (H : List (PropFormula α)) (E : PropFormula α) :
    ReducedGoal (expandGoal H E) := by
  refine ⟨?_, expandNegation_negationFree E⟩
  intro B hB
  obtain ⟨A, _, rfl⟩ := List.mem_map.mp hB
  exact expandNegation_negationFree A

theorem expandGoal_underlying (H : List (PropFormula α)) (E : PropFormula α) :
    underlying (expandGoal H E) = (H.toFinset.image expandNegation, expandNegation E) := by
  apply Prod.ext
  · apply Finset.ext
    intro A
    simp [underlying, expandGoal]
  · rfl

/-- Compute and retain the actual certificate of the native expansion. -/
def solveNative (H : List (PropFormula α)) (E : PropFormula α) :
    Option (Certificate (expandGoal H E)) := solve (expandGoal H E)

def prove (H : List (PropFormula α)) (E : PropFormula α) : Bool := (solveNative H E).isSome

theorem native_decision (H : List (PropFormula α)) (E : PropFormula α) :
    prove H E = true ↔ Derives (H.toFinset : Set (PropFormula α)) E := by
  unfold prove solveNative
  rw [solve_iff_certificate]
  have hmap : (H.map expandNegation).toFinset = H.toFinset.image expandNegation :=
    congrArg Prod.fst (expandGoal_underlying H E)
  simpa only [Certificate, expandGoal, hmap] using
    (G4ip.native_iff H.toFinset E).symm

theorem prove_eq_of_toFinset_eq (H K : List (PropFormula α)) (E : PropFormula α)
    (h : H.toFinset = K.toFinset) : prove H E = prove K E := by
  by_cases hH : prove H E = true
  · have hK : prove K E = true := (native_decision K E).mpr (by
      simpa only [h] using (native_decision H E).mp hH)
    exact hH.trans hK.symm
  · have hK : prove K E ≠ true := by
      intro hK
      apply hH
      apply (native_decision H E).mpr
      simpa only [h] using (native_decision K E).mp hK
    exact (Bool.eq_false_of_not_eq_true hH).trans
      (Bool.eq_false_of_not_eq_true hK).symm

theorem prove_perm {H K : List (PropFormula α)} (h : H.Perm K) (E : PropFormula α) :
    prove H E = prove K E := by
  apply prove_eq_of_toFinset_eq H K E
  apply Finset.ext
  intro A
  simpa only [List.mem_toFinset] using (h.mem_iff : A ∈ H ↔ A ∈ K)

theorem prove_repeat (H : List (PropFormula α)) (A E : PropFormula α) (hA : A ∈ H) :
    prove (A :: H) E = prove H E := by
  apply prove_eq_of_toFinset_eq (A :: H) H E
  simpa only [List.toFinset_cons] using
    Finset.insert_eq_of_mem (List.mem_toFinset.mpr hA)

end Lemmatheca.ProofTheory.Intuitionistic.G4ip.Search
