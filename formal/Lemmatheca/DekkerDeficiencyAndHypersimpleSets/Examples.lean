import Lemmatheca.DekkerDeficiencyAndHypersimpleSets.Theorems

namespace Lemmatheca.ComputabilityTheory.DekkerDeficiencyAndHypersimpleSets

open UniversalComputation OracleComputation HyperimmuneDegrees TuringDegrees

noncomputable section

def paritySwap (n : ℕ) : ℕ := if n % 2 = 0 then n + 1 else n - 1

theorem parity_swap_primitive : Primrec paritySwap := by
  have hm : Primrec (fun n : ℕ => n % 2) :=
    Primrec.nat_mod.comp Primrec.id (Primrec.const 2)
  exact Primrec.ite (Primrec.eq.comp hm (Primrec.const 0))
    (Primrec.succ.comp Primrec.id)
    (Primrec.nat_sub.comp Primrec.id (Primrec.const 1))

theorem parity_swap_equations (n : ℕ) :
    paritySwap (2 * n) = 2 * n + 1 ∧ paritySwap (2 * n + 1) = 2 * n := by
  constructor <;> simp [paritySwap, Nat.add_mod]

theorem parity_swap_injective : Function.Injective paritySwap := by
  have invol : Function.LeftInverse paritySwap paritySwap := by
    intro n
    by_cases h : n % 2 = 0
    · have hn : (n + 1) % 2 ≠ 0 := by omega
      simp [paritySwap, h, hn]
    · have hn : (n - 1) % 2 = 0 := by omega
      simp only [paritySwap, ite_eq_right h, hn, ite_true]
      omega
  exact invol.injective

theorem parity_swap_range : Set.range paritySwap = Set.univ := by
  apply Set.eq_univ_of_forall
  intro n
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  · exact ⟨2 * k + 1, (parity_swap_equations k).2⟩
  · exact ⟨2 * k, (parity_swap_equations k).1⟩

theorem parity_swap_deficiency :
    deficiency paritySwap = {n | Even n} ∧ nondeficient paritySwap = {n | Odd n} := by
  have he : deficiency paritySwap = {n | Even n} := by
    ext n
    change (∃ t, n < t ∧ paritySwap t < paritySwap n) ↔ Even n
    rw [Nat.even_iff]
    constructor
    · rintro ⟨t, hnt, hlt⟩
      by_contra hn
      by_cases ht : t % 2 = 0
      · simp only [paritySwap, ite_eq_right hn, ht, ite_true] at hlt
        omega
      · simp only [paritySwap, ite_eq_right hn, ite_eq_right ht] at hlt
        omega
    · intro hn
      have ht : (n + 1) % 2 ≠ 0 := by omega
      refine ⟨n + 1, by omega, ?_⟩
      simp [paritySwap, hn, ht]
  refine ⟨he, ?_⟩
  ext n
  simp only [nondeficient, he, Set.mem_compl_iff, Set.mem_ofPred_eq, Nat.not_even_iff_odd]

def oddSingletonArray (n : ℕ) : ℕ := FiniteSequenceCoding.code [2 * n + 1]

theorem odd_singleton_array_spec :
    StrongArray oddSingletonArray ∧ ArrayHits oddSingletonArray (nondeficient paritySwap) := by
  have hc : Computable (fun n : ℕ => 2 * n + 1) :=
    (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id)
      (Primrec.const 1)).to_comp
  refine ⟨⟨Primrec.encode.to_comp.comp
    (Primrec.list_cons.to_comp.comp hc (Computable.const [])), ?_⟩, ?_⟩
  · intro i j hij
    have hne : 2 * i + 1 ≠ 2 * j + 1 := by omega
    simpa [arraySet, oddSingletonArray] using hne
  · intro n
    refine ⟨2 * n + 1, by simp [arraySet, oddSingletonArray], ?_⟩
    rw [parity_swap_deficiency.2]
    exact Nat.odd_iff.mpr (by omega)

theorem parity_swap_not_hypersimple : ¬ Hypersimple (deficiency paritySwap) := by
  intro hh
  exact ((hyperimmune_iff_no_array _).mp hh.2).2
    ⟨oddSingletonArray, odd_singleton_array_spec⟩

theorem halting_hypersimple_example :
    ∃ a : ℕ → ℕ, Computable a ∧ Function.Injective a ∧ Set.range a = haltingDiagonal ∧
      Hypersimple (deficiency a) ∧ Equivalent (deficiency a) haltingDiagonal := by
  obtain ⟨a, hc, ha, hr⟩ := EffectiveEnumerations.infinite_ce_injective_enumeration
    haltingDiagonal haltingDiagonal_enumerable EffectiveEnumerations.halting_infinite
  have hnc : ¬ ComputablePred (Set.range a) := by
    rw [hr]
    exact haltingDiagonal_undecidable
  refine ⟨a, hc, ha, hr, deficiency_hypersimple a ha hc hnc, ?_⟩
  simpa only [hr] using deficiency_equivalent a ha hc

end
end Lemmatheca.ComputabilityTheory.DekkerDeficiencyAndHypersimpleSets
