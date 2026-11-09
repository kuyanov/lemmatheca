import Lemmatheca.ComputablyBoundedChanges.Operations
import Lemmatheca.UniversalFiniteChangeSets.Hierarchy

/-! A specified computably bounded join escaping every fixed finite revision allowance. -/
namespace Lemmatheca.ComputabilityTheory.ComputablyBoundedChanges

open UniversalComputation LimitComputability DifferenceEnumerable FiniteMindChanges
open UniversalFiniteChangeSets

set_option backward.isDefEq.respectTransparency false

def diagonalJoin : Set ℕ := {z | z.unpair.2 ∈ diagonalSet z.unpair.1}

def joinApproximation (s z : ℕ) : ℕ := diagonalGuess z.unpair.1 s z.unpair.2

def joinBound (z : ℕ) : ℕ := z.unpair.1 + 1

theorem join_data :
    Computable₂ joinApproximation ∧ Binary joinApproximation ∧
      StartsZero joinApproximation ∧ ComputableBound joinApproximation joinBound ∧
      Converges joinApproximation diagonalJoin := by
  have hcount : ∀ s z, changeCount joinApproximation s z =
      changeCount (diagonalGuess z.unpair.1) s z.unpair.2 := by
    intro s z
    induction s with
    | zero => rfl
    | succ s ih => simp only [changeCount, joinApproximation, ih]
  refine ⟨?_, ?_, ?_, ⟨?_, ?_⟩, ?_⟩
  · change Computable (fun p : ℕ × ℕ => diagonalGuess p.2.unpair.1 p.1 p.2.unpair.2)
    have ht : Computable (fun p : ℕ × ℕ => ((p.2.unpair.1, p.1), p.2.unpair.2)) :=
      (((Computable.fst.comp (Computable.unpair.comp Computable.snd)).pair
        Computable.fst).pair (Computable.snd.comp (Computable.unpair.comp Computable.snd)))
    apply (diagonal_computable.comp ht).of_eq
    intro p
    rfl
  · intro s z
    exact (diagonal_data z.unpair.1).1 s z.unpair.2
  · intro z
    rfl
  · exact Computable.succ.comp (Computable.fst.comp Computable.unpair)
  · intro s z
    rw [hcount]
    exact (diagonal_data z.unpair.1).2.2.1 s z.unpair.2
  · intro z
    exact (diagonal_data z.unpair.1).2.2.2.1 z.unpair.2

theorem join_column (n : ℕ) :
    Computable (Nat.pair n) ∧ (Nat.pair n) ⁻¹' diagonalJoin = diagonalSet n := by
  refine ⟨Primrec₂.natPair.to_comp.comp (Computable.const n) Computable.id, ?_⟩
  ext e
  simp [diagonalJoin]

theorem join_omega : OmegaCE diagonalJoin := by
  obtain ⟨hc, hb, hz, hn, hl⟩ := join_data
  exact ⟨joinApproximation, joinBound, hc, hb, hl, hz, hn⟩

theorem join_not_nce (n : ℕ) : ¬ NCE n diagonalJoin := by
  intro h
  obtain ⟨hc, hcol⟩ := join_column n
  have hp := nce_preimage n diagonalJoin (Nat.pair n) h hc
  rw [hcol] at hp
  exact diagonal_not_nce n hp

end Lemmatheca.ComputabilityTheory.ComputablyBoundedChanges
