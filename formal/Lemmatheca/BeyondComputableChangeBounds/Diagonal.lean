import Lemmatheca.BeyondComputableChangeBounds.Candidates

/-! A limit-computable diagonal outside every computably bounded-change presentation. -/
namespace Lemmatheca.ComputabilityTheory.BeyondComputableChangeBounds

open UniversalComputation LimitComputability DifferenceEnumerable FiniteMindChanges
open ComputablyBoundedChanges

set_option backward.isDefEq.respectTransparency false

noncomputable def diagonalSet : Set ℕ := {e | e ∉ candidateSet e}

def diagonalGuess : Approximation := delayedComplement (fun s e => candidateGuess e s e)

theorem diagonal_data :
    Computable₂ diagonalGuess ∧ Binary diagonalGuess ∧ StartsZero diagonalGuess ∧
      Converges diagonalGuess diagonalSet := by
  let a : Approximation := fun s e => candidateGuess e s e
  let A : Set ℕ := {e | e ∈ candidateSet e}
  have hc : Computable₂ a := by
    change Computable (fun z : ℕ × ℕ => candidateGuess z.2 z.1 z.2)
    exact candidate_data.1.comp
      ((Computable.snd.pair Computable.fst).pair Computable.snd)
  have hb : Binary a := fun s e => (candidate_data.2 e).1 s e
  have hl : Converges a A := fun e => candidate_converges e e
  exact delayed_complement_data a A hc hb hl

theorem diagonal_not_omega : ¬ OmegaCE diagonalSet := by
  intro h
  obtain ⟨e, he⟩ := omega_covered diagonalSet h
  have hh : e ∈ candidateSet e ↔ e ∉ candidateSet e := by
    conv_lhs => rw [he]
    rfl
  tauto

theorem diagonal_finite_counts : ∀ e, ∃ n, ∀ s, changeCount diagonalGuess s e ≤ n := by
  intro e
  obtain ⟨t, ht⟩ := diagonal_data.2.2.2 e
  have hstable : ∀ s, t ≤ s →
      changeCount diagonalGuess s e = changeCount diagonalGuess t e := by
    intro s hs
    induction s, hs using Nat.le_induction with
    | base => rfl
    | succ s hs ih =>
        have heq : diagonalGuess (s + 1) e = diagonalGuess s e :=
          (ht (s + 1) (by omega)).trans (ht s hs).symm
        simp only [changeCount, ite_eq_left heq, Nat.add_zero, ih]
  refine ⟨changeCount diagonalGuess t e, fun s => ?_⟩
  by_cases hs : t ≤ s
  · exact (hstable s hs).le
  · exact changeCount_monotone diagonalGuess e (by omega)

theorem diagonal_no_computable_bound : ¬ ∃ b : ℕ → ℕ, ComputableBound diagonalGuess b := by
  rintro ⟨b, hb⟩
  exact diagonal_not_omega ⟨diagonalGuess, b, diagonal_data.1,
    diagonal_data.2.1, diagonal_data.2.2.2, diagonal_data.2.2.1, hb⟩

theorem candidate_no_uniform_bound :
    ¬ ∃ B : ℕ → ℕ → ℕ, Computable₂ B ∧
      ∀ e s x, changeCount (candidateGuess e) s x ≤ B e x := by
  rintro ⟨B, hc, hn⟩
  let a : Approximation := fun s e => candidateGuess e s e
  have hb : Binary a := fun s e => (candidate_data.2 e).1 s e
  have hz : StartsZero a := fun e => (candidate_data.2 e).2 e
  have hcount : ∀ s e, changeCount a s e = changeCount (candidateGuess e) s e := by
    intro s e
    induction s with
    | zero => rfl
    | succ s ih => simp only [changeCount, a, ih]
  apply diagonal_no_computable_bound
  refine ⟨fun e => B e e + 1, ?_, ?_⟩
  · exact Primrec.nat_add.to_comp.comp (hc.comp Computable.id Computable.id)
      (Computable.const 1)
  · intro s e
    cases s with
    | zero => simp [changeCount]
    | succ s =>
        change changeCount (delayedComplement a) (s + 1) e ≤ B e e + 1
        rw [delayed_complement_count a hb hz, hcount]
        have h := hn e s e
        omega

end Lemmatheca.ComputabilityTheory.BeyondComputableChangeBounds
