import Lemmatheca.TuringJump.Recoding
import Lemmatheca.TuringDegrees.Joins

/-! The jump on the existing quotient degrees and its finite iterates. -/
namespace Lemmatheca.ComputabilityTheory.TuringJump

open TuringDegrees

noncomputable section

theorem jump_degree_congr {A B : Set ℕ} (hAB : Equivalent A B) :
    degree (jump A) = degree (jump B) := by
  apply Quotient.sound
  exact ⟨manyOne_imp_reducible (jump_monotone hAB.1),
    manyOne_imp_reducible (jump_monotone hAB.2)⟩

def degreeJump : Degree → Degree :=
  Quotient.lift (fun A : Problem => degree (jump A.carrier))
    (fun _ _ hAB => jump_degree_congr hAB)

theorem degree_jump_degree (A : Set ℕ) : degreeJump (degree A) = degree (jump A) := by
  rfl

theorem degree_jump_monotone : Monotone degreeJump := by
  intro a b hab
  obtain ⟨A, rfl⟩ := degree_surjective a
  obtain ⟨B, rfl⟩ := degree_surjective b
  exact manyOne_imp_reducible (jump_monotone hab)

def iterate (A : Set ℕ) : ℕ → Set ℕ
  | 0 => A
  | n + 1 => jump (iterate A n)

def degreeIterate (a : Degree) : ℕ → Degree
  | 0 => a
  | n + 1 => degreeJump (degreeIterate a n)

theorem iterate_degree (A : Set ℕ) (n : ℕ) :
    degreeIterate (degree A) n = degree (iterate A n) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [degreeIterate, ih, degree_jump_degree, iterate]

theorem iterate_representative {A B : Set ℕ} (hAB : Equivalent A B) (n : ℕ) :
    Equivalent (iterate A n) (iterate B n) := by
  induction n with
  | zero => exact hAB
  | succ n ih =>
      exact ⟨manyOne_imp_reducible (jump_monotone ih.1),
        manyOne_imp_reducible (jump_monotone ih.2)⟩

theorem zero_jump_halting :
    degreeJump zeroDegree = degree UniversalComputation.haltingDiagonal := by
  apply Quotient.sound
  exact ⟨manyOne_imp_reducible empty_jump_equiv_halting.1,
    manyOne_imp_reducible empty_jump_equiv_halting.2⟩

private theorem iterate_reducible_le (A : Set ℕ) {m n : ℕ} (hmn : m ≤ n) :
    Reducible (iterate A m) (iterate A n) := by
  induction n generalizing m with
  | zero =>
      have hm : m = 0 := by omega
      subst m
      exact reducible_refl _
  | succ n ih =>
      by_cases he : m = n + 1
      · subst m
        exact reducible_refl _
      · have hm : m ≤ n := by omega
        exact reducible_trans (ih hm) (jump_strict (iterate A n)).1

theorem iterate_strict (A : Set ℕ) {m n : ℕ} (hmn : m < n) :
    Reducible (iterate A m) (iterate A n) ∧ ¬ Reducible (iterate A n) (iterate A m) := by
  refine ⟨iterate_reducible_le A hmn.le, ?_⟩
  intro h
  exact (jump_strict (iterate A m)).2
    (reducible_trans (iterate_reducible_le A (Nat.succ_le_of_lt hmn)) h)

theorem degree_iterate_strict (a : Degree) {m n : ℕ} (hmn : m < n) :
    degreeIterate a m < degreeIterate a n := by
  obtain ⟨A, rfl⟩ := degree_surjective a
  rw [iterate_degree, iterate_degree]
  exact lt_iff_le_not_ge.mpr (iterate_strict A hmn)

theorem degree_lt_jump (a : Degree) : a < degreeJump a := by
  obtain ⟨A, rfl⟩ := degree_surjective a
  exact lt_iff_le_not_ge.mpr (jump_strict A)

theorem no_greatest_degree : ¬ ∃ a : Degree, ∀ b : Degree, b ≤ a := by
  rintro ⟨a, ha⟩
  exact (not_le_of_gt (degree_lt_jump a)) (ha (degreeJump a))

end
end Lemmatheca.ComputabilityTheory.TuringJump
