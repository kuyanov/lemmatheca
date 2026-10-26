import Lemmatheca.ProductiveAndCreativeSets.Iteration
import Mathlib.Data.Set.Card

/-! Immunity and simplicity in the shared numerical program enumeration. -/
namespace Lemmatheca.ComputabilityTheory.SimpleSets

open UniversalComputation EffectiveEnumerations ProductiveAndCreativeSets

def Immune (B : Set ℕ) : Prop :=
  B.Infinite ∧ ∀ X : Set ℕ, REPred X → X ⊆ B → X.Finite

def Simple (S : Set ℕ) : Prop := REPred S ∧ Immune Sᶜ

theorem immune_iff_index (B : Set ℕ) :
    Immune B ↔ B.Infinite ∧ ∀ e, indexSet e ⊆ B → (indexSet e).Finite := by
  constructor
  · rintro ⟨hinf, h⟩
    refine ⟨hinf, fun e he => h (indexSet e) ?_ he⟩
    exact (phi_recursive.comp (Computable.const e) Computable.id).dom_re
  · rintro ⟨hinf, h⟩
    refine ⟨hinf, ?_⟩
    intro X hce hsub
    obtain ⟨e, he⟩ := (enumerable_iff_index X).mp hce
    have hEq : indexSet e = X := Set.ext (fun x => (he x).symm)
    simpa only [hEq] using h e (by simpa only [hEq] using hsub)

theorem immune_not_enumerable {B : Set ℕ} (hB : Immune B) : ¬ REPred B := by
  intro hce
  exact hB.1 (hB.2 B hce Set.Subset.rfl)

theorem immune_not_productive {B : Set ℕ} (hB : Immune B) : ¬ Productive B := by
  intro hp
  obtain ⟨X, hXB, hinf, hce⟩ := productive_infinite_enumerable_subset hp
  exact hinf (hB.2 X hce hXB)

theorem simple_iff_meets (S : Set ℕ) (hce : REPred S) (hinf : Sᶜ.Infinite) :
    Simple S ↔ ∀ e, (indexSet e).Infinite → (indexSet e ∩ S).Nonempty := by
  classical
  constructor
  · intro hS e he
    by_contra hn
    have hsub : indexSet e ⊆ Sᶜ := by
      intro x hx hxS
      exact hn ⟨x, hx, hxS⟩
    exact he (((immune_iff_index Sᶜ).mp hS.2).2 e hsub)
  · intro hmeet
    refine ⟨hce, (immune_iff_index Sᶜ).mpr ⟨hinf, ?_⟩⟩
    intro e he
    by_contra hn
    obtain ⟨x, hx, hxS⟩ := hmeet e hn
    exact he hx hxS

theorem finite_decidable {S : Set ℕ} (hS : S.Finite) : ComputablePred S := by
  classical
  let L : List ℕ := hS.toFinset.toList
  have htest : PrimrecPred (fun x : ℕ => ∃ a ∈ L, a = x) :=
    Primrec.eq.exists_mem_list.comp (Primrec.const L) Primrec.id
  exact htest.computablePred.of_eq (fun x => by simp [L]; rfl)

theorem simple_undecidable {S : Set ℕ} (hS : Simple S) : ¬ ComputablePred S := by
  intro hc
  exact immune_not_enumerable hS.2 hc.not.to_re

theorem simple_infinite_coinfinite {S : Set ℕ} (hS : Simple S) :
    S.Infinite ∧ Sᶜ.Infinite := by
  exact ⟨fun hf => simple_undecidable hS (finite_decidable hf), hS.2.1⟩

theorem simple_not_creative {S : Set ℕ} (hS : Simple S) : ¬ Creative S := by
  intro hc
  exact immune_not_productive hS.2 hc.2

theorem simple_not_complete {S : Set ℕ} (hS : Simple S) :
    ¬ ∀ X : ℕ → Prop, REPred X → X ≤₀ S := by
  intro hc
  exact simple_not_creative hS ((creative_iff_complete hS.1).mpr hc)

theorem simple_not_diagonal_reducible {S : Set ℕ} (hS : Simple S) :
    ¬ haltingDiagonal ≤₀ S := by
  intro hc
  exact simple_not_creative hS ((creative_iff_diagonal_reduces hS.1).mpr hc)

theorem simple_not_omit {S X : Set ℕ} (hS : Simple S)
    (hce : REPred X) (hinf : X.Infinite) : ¬ X ⊆ Sᶜ := by
  intro hsub
  exact hinf (hS.2.2 X hce hsub)

end Lemmatheca.ComputabilityTheory.SimpleSets
