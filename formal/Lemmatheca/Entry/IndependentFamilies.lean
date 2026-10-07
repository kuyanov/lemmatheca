import Lemmatheca.SetTheory.IndependentFamilies

namespace Lemmatheca.Entry.IndependentFamilies

open Set
open Lemmatheca.SetTheory.IndependentFamilies

def residueA : Set ℕ := {n | ∃ k, n = 4 * k ∨ n = 4 * k + 1}
def residueB : Set ℕ := {n | ∃ k, n = 4 * k ∨ n = 4 * k + 2}

theorem four_residue_example :
    IsIndependent {residueA, residueB} ∧
      residueA ∩ residueB = {n | ∃ k, n = 4 * k} ∧
      residueA \ residueB = {n | ∃ k, n = 4 * k + 1} ∧
      residueB \ residueA = {n | ∃ k, n = 4 * k + 2} ∧
      (residueA ∪ residueB)ᶜ = {n | ∃ k, n = 4 * k + 3} := by
  have hA (n : ℕ) : n ∈ residueA ↔ n % 4 = 0 ∨ n % 4 = 1 := by
    constructor
    · rintro ⟨k, hn | hn⟩ <;> omega
    · rintro (hn | hn)
      · exact ⟨n / 4, Or.inl (by omega)⟩
      · exact ⟨n / 4, Or.inr (by omega)⟩
  have hB (n : ℕ) : n ∈ residueB ↔ n % 4 = 0 ∨ n % 4 = 2 := by
    constructor
    · rintro ⟨k, hn | hn⟩ <;> omega
    · rintro (hn | hn)
      · exact ⟨n / 4, Or.inl (by omega)⟩
      · exact ⟨n / 4, Or.inr (by omega)⟩
  have hresidue (n r : ℕ) (hr : r < 4) :
      (∃ k, n = 4 * k + r) ↔ n % 4 = r := by
    constructor
    · rintro ⟨k, hn⟩
      omega
    · intro hn
      exact ⟨n / 4, by omega⟩
  have h₀ : residueA ∩ residueB = {n | ∃ k, n = 4 * k} := by
    ext n
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, hA, hB]
    have hh := hresidue n 0 (by omega)
    simp only [Nat.add_zero] at hh
    rw [hh]
    omega
  have h₁ : residueA \ residueB = {n | ∃ k, n = 4 * k + 1} := by
    ext n
    simp only [Set.mem_sdiff, Set.mem_ofPred_eq, hA, hB, hresidue n 1 (by omega)]
    omega
  have h₂ : residueB \ residueA = {n | ∃ k, n = 4 * k + 2} := by
    ext n
    simp only [Set.mem_sdiff, Set.mem_ofPred_eq, hA, hB, hresidue n 2 (by omega)]
    omega
  have h₃ : (residueA ∪ residueB)ᶜ = {n | ∃ k, n = 4 * k + 3} := by
    ext n
    simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_ofPred_eq, hA, hB,
      hresidue n 3 (by omega)]
    omega
  have hinf (r : ℕ) : ({n | ∃ k, n = 4 * k + r} : Set ℕ).Infinite := by
    apply Set.infinite_of_injective_forall_mem (f := fun k : ℕ => 4 * k + r)
    · intro k l h
      dsimp at h
      omega
    · intro k
      exact ⟨k, rfl⟩
  have hne : residueA ≠ residueB := by
    intro h
    have ha : 1 ∈ residueA := ⟨0, Or.inr rfl⟩
    have hb := (hB 1).mp (h ▸ ha)
    omega
  refine ⟨(pair_iff residueA residueB hne).mpr ?_, h₀, h₁, h₂, h₃⟩
  rw [h₀, h₁, h₂, h₃]
  simpa only [Nat.add_zero] using
    And.intro (hinf 0) (And.intro (hinf 1) (And.intro (hinf 2) (hinf 3)))

end Lemmatheca.Entry.IndependentFamilies
