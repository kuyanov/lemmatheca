import Lemmatheca.FiniteDifferenceNormalForms.Stages

/-! Modular nested chains and a precise failure without nesting. -/
namespace Lemmatheca.Entry.FiniteDifferenceNormalForms

open ComputabilityTheory.UniversalComputation ComputabilityTheory.LimitComputability
  ComputabilityTheory.DifferenceEnumerable ComputabilityTheory.FiniteMindChanges
  ComputabilityTheory.FiniteDifferenceNormalForms

set_option backward.isDefEq.respectTransparency false

def multiplesChain : ℕ → Set ℕ
  | 0 => Set.univ
  | 1 => {x | x % 2 = 0}
  | 2 => {x | x % 4 = 0}
  | 3 => {x | x % 8 = 0}
  | _ => ∅

theorem multiples_chain_nested : Nested 3 multiplesChain ∧ Nested 4 multiplesChain := by
  constructor <;> intro i j hij hj x hx <;>
    interval_cases j <;> interval_cases i <;> simp_all [multiplesChain] <;> omega

theorem multiples_chain_values :
    alternatingDifference 3 multiplesChain = {x | x % 2 = 1 ∨ x % 4 = 0} ∧
      alternatingDifference 4 multiplesChain =
        {x | x % 2 = 1 ∨ (x % 4 = 0 ∧ x % 8 ≠ 0)} := by
  constructor
  · ext x
    change (∃ i, i < 3 ∧ i % 2 = 0 ∧ x ∈ multiplesChain i ∧
      (i + 1 = 3 ∨ x ∉ multiplesChain (i + 1))) ↔ _
    constructor
    · rintro ⟨i, hi, he, hm, hn⟩
      interval_cases i <;> simp_all [multiplesChain]
    · rintro (h | h)
      · refine ⟨0, by omega, rfl, trivial, Or.inr ?_⟩
        change x % 2 ≠ 0
        omega
      · exact ⟨2, by omega, rfl, h, Or.inl rfl⟩
  · ext x
    change (∃ i, i < 4 ∧ i % 2 = 0 ∧ x ∈ multiplesChain i ∧
      (i + 1 = 4 ∨ x ∉ multiplesChain (i + 1))) ↔ _
    constructor
    · rintro ⟨i, hi, he, hm, hn⟩
      interval_cases i <;> simp_all [multiplesChain]
    · rintro (h | ⟨h, hn⟩)
      · refine ⟨0, by omega, rfl, trivial, Or.inr ?_⟩
        change x % 2 ≠ 0
        omega
      · exact ⟨2, by omega, rfl, h, Or.inr hn⟩

theorem multiples_chain_ranks (x : ℕ) :
    (x % 2 = 1 → membershipRank 3 multiplesChain x = 1 ∧ membershipRank 4 multiplesChain x = 1) ∧
    (x % 4 = 2 → membershipRank 3 multiplesChain x = 2 ∧ membershipRank 4 multiplesChain x = 2) ∧
    (x % 8 = 4 → membershipRank 3 multiplesChain x = 3 ∧ membershipRank 4 multiplesChain x = 3) ∧
    (x % 8 = 0 → membershipRank 3 multiplesChain x = 3 ∧ membershipRank 4 multiplesChain x = 4) := by
  classical
  have hr3 : membershipRank 3 multiplesChain x =
      1 + (if x % 2 = 0 then 1 else 0) + (if x % 4 = 0 then 1 else 0) := by
    simp [membershipRank, multiplesChain, indicator, Set.ofPred,
      Set.univ]
  have hr4 : membershipRank 4 multiplesChain x =
      1 + (if x % 2 = 0 then 1 else 0) + (if x % 4 = 0 then 1 else 0) +
      (if x % 8 = 0 then 1 else 0) := by
    simp [membershipRank, multiplesChain, indicator, Set.ofPred,
      Set.univ]
  rw [hr3, hr4]
  split_ifs <;> omega

theorem multiples_chain_decidable :
    ComputablePred (alternatingDifference 3 multiplesChain) ∧
      ComputablePred (alternatingDifference 4 multiplesChain) ∧
      NCE 1 (alternatingDifference 3 multiplesChain) ∧
      NCE 1 (alternatingDifference 4 multiplesChain) := by
  have hmod (k : ℕ) : Computable (fun x : ℕ => x % k) :=
    Primrec.nat_mod.to_comp.comp Computable.id (Computable.const k)
  have heq (k r : ℕ) : ComputablePred (fun x : ℕ => x % k = r) :=
    (Primrec.eq.decide.to_comp.comp (hmod k) (Computable.const r)).computablePred
  have hp : ComputablePred (fun x : ℕ => x % 2 = 1 ∨ x % 4 = 0) := by
    apply Computable.computablePred
    exact (Primrec.or.to_comp.comp (heq 2 1).decide (heq 4 0).decide).of_eq
      (fun _ => by simp only [Bool.decide_or])
  have hq : ComputablePred (fun x : ℕ => x % 2 = 1 ∨ (x % 4 = 0 ∧ x % 8 ≠ 0)) := by
    apply Computable.computablePred
    exact (Primrec.or.to_comp.comp (heq 2 1).decide
      (Primrec.and.to_comp.comp (heq 4 0).decide (heq 8 0).not.decide)).of_eq
      (fun _ => by simp only [Bool.decide_or, Bool.decide_and])
  rw [multiples_chain_values.1, multiples_chain_values.2]
  exact ⟨hp, hq, (enumerable_iff_one_change _).mp hp.to_re,
    (enumerable_iff_one_change _).mp hq.to_re⟩

def nonnestedChain : ℕ → Set ℕ
  | 1 => Set.univ
  | _ => ∅

theorem nonnested_counterexample :
    (∀ i, i < 2 → ComputablePred (nonnestedChain i)) ∧ ¬ Nested 2 nonnestedChain ∧
      alternatingDifference 2 nonnestedChain = ∅ ∧
      ∀ x, membershipRank 2 nonnestedChain x = 1 := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i hi
    interval_cases i
    · change ComputablePred (fun _ : ℕ => False)
      exact Computable.computablePred (Computable.const false)
    · change ComputablePred (fun _ : ℕ => True)
      exact Computable.computablePred (Computable.const true)
  · intro h
    have hx : (0 : ℕ) ∈ nonnestedChain 0 :=
      h 0 1 (by omega) (by omega) (show (0 : ℕ) ∈ nonnestedChain 1 from trivial)
    exact hx
  · ext x
    constructor
    · rintro ⟨i, hi, he, hm, hn⟩
      interval_cases i <;> simp_all [nonnestedChain]
    · exact False.elim
  · intro x
    simp [membershipRank, nonnestedChain, indicator, Set.ofPred,
      Set.univ, EmptyCollection.emptyCollection]

end Lemmatheca.Entry.FiniteDifferenceNormalForms
