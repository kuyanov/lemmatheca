import Lemmatheca.FiniteDescriptionsAndDecisionProblems.Decisions

namespace Lemmatheca.Entry.FiniteDescriptionsAndDecisionProblems

open Lemmatheca.ComputabilityTheory.FiniteDescriptions
open Lemmatheca.ComputabilityTheory.PrimitiveRecursion

theorem short_word_codes :
    wordCode [false] = 1 ∧ wordCode [true] = 2 ∧
      wordCode [false, false] = 3 ∧ wordCode [true, false] = 4 ∧
      wordCode [false, true] = 5 ∧ wordCode [true, true] = 6 ∧
      wordCode [true, false, true] = 12 ∧ ([false, true] : List Bool).length = 2 := by
  norm_num [wordCode]

theorem accepts_only_decides (E : BehaviorFamily) (e : ℕ) (A : Set ℕ)
    (hyes : ∀ x ∈ A, E e x = some 1) (hno : ∀ x ∉ A, E e x = none) :
    Decides E e A ↔ A = Set.univ := by
  constructor
  · intro hd
    apply Set.eq_univ_of_forall
    intro x
    by_contra hx
    have hc := hd x
    have hv := (characteristic_spec A x).2.mpr hx
    rw [hno x hx, hv] at hc
    cases hc
  · intro hA x
    have hx : x ∈ A := by rw [hA]; trivial
    exact (hyes x hx).trans (congrArg some ((characteristic_spec A x).1.mpr hx).symm)

theorem wrong_negative_decides (E : BehaviorFamily) (e : ℕ) (A : Set ℕ)
    (hyes : ∀ x ∈ A, E e x = some 1) (hno : ∀ x ∉ A, E e x = some 2) :
    Decides E e A ↔ A = Set.univ := by
  constructor
  · intro hd
    apply Set.eq_univ_of_forall
    intro x
    by_contra hx
    have hc := hd x
    have hv := (characteristic_spec A x).2.mpr hx
    rw [hno x hx, hv] at hc
    cases hc
  · intro hA x
    have hx : x ∈ A := by rw [hA]; trivial
    exact (hyes x hx).trans (congrArg some ((characteristic_spec A x).1.mpr hx).symm)

theorem correct_outputs_decide (E : BehaviorFamily) (e : ℕ) (A : Set ℕ)
    (h : ∀ x, E e x = some (characteristic A x)) : Decides E e A := by
  exact h

theorem diagonal_table (E : BehaviorFamily)
    (h0 : E 0 0 = some 1) (h1 : E 1 1 = some 0)
    (h2 : E 2 2 = none) (h3 : E 3 3 = some 7) :
    diagonalProblem E ∩ {0, 1, 2, 3} = {1, 2, 3} ∧
      characteristic (diagonalProblem E) 0 = 0 ∧
      characteristic (diagonalProblem E) 1 = 1 ∧
      characteristic (diagonalProblem E) 2 = 1 ∧
      characteristic (diagonalProblem E) 3 = 1 := by
  have hm0 : 0 ∉ diagonalProblem E := by
    change ¬ (E 0 0 ≠ some 1)
    exact not_not.mpr h0
  have hm1 : 1 ∈ diagonalProblem E := by
    change E 1 1 ≠ some 1
    rw [h1]
    decide
  have hm2 : 2 ∈ diagonalProblem E := by
    change E 2 2 ≠ some 1
    rw [h2]
    decide
  have hm3 : 3 ∈ diagonalProblem E := by
    change E 3 3 ≠ some 1
    rw [h3]
    decide
  refine ⟨?_, (characteristic_spec _ _).2.mpr hm0,
    (characteristic_spec _ _).1.mpr hm1,
    (characteristic_spec _ _).1.mpr hm2,
    (characteristic_spec _ _).1.mpr hm3⟩
  ext n
  by_cases hn0 : n = 0 <;> by_cases hn1 : n = 1 <;>
    by_cases hn2 : n = 2 <;> by_cases hn3 : n = 3 <;>
    simp_all only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
      false_or, true_or, and_false, and_true, or_self]

end Lemmatheca.Entry.FiniteDescriptionsAndDecisionProblems
