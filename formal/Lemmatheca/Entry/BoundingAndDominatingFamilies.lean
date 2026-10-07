import Lemmatheca.SetTheory.BoundingAndDominating

/-! Illustrative parity and spike examples for bounding and dominating families. -/

namespace Lemmatheca.Entry.BoundingAndDominatingFamilies

open Set Filter
open Lemmatheca.SetTheory.BoundingAndDominating

theorem strict_eventual_comparison_example :
    (fun _ : ℕ => 0) ≤ᶠ[atTop] (fun n : ℕ => if n % 2 = 0 then 1 else 0) ∧
    ¬ (fun n : ℕ => if n % 2 = 0 then 1 else 0) ≤ᶠ[atTop] (fun _ => 0) ∧
    ¬ Lemmatheca.SetTheory.FiniteErrors.EventuallyLT
      (fun _ => 0) (fun n => if n % 2 = 0 then 1 else 0) := by
  refine ⟨Filter.Eventually.of_forall fun n => Nat.zero_le _, ?_, ?_⟩
  · intro h
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp h
    have hh := hN (2 * N) (by omega)
    simp at hh
  · intro h
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp h
    have hh := hN (2 * N + 1) (by omega)
    simp at hh

def spikeFamily : Set (ℕ → ℕ) :=
  Set.range (fun p : ℕ × ℕ => Function.update (fun _ : ℕ => 0) p.1 p.2)

theorem spikeFamily_spec :
    IsBounded spikeFamily ∧
    (∀ f ∈ spikeFamily, f ≤ᶠ[atTop] (fun _ => 0)) ∧
    (∀ i k n : ℕ, i + 1 ≤ n → Function.update (fun _ : ℕ => 0) i k n = 0) ∧
    (∀ (g : ℕ → ℕ) (i : ℕ),
      Function.update (fun _ : ℕ => 0) i (g i + 1) ∈ spikeFamily ∧
      g i < Function.update (fun _ : ℕ => 0) i (g i + 1) i) ∧
    (¬ ∃ g : ℕ → ℕ, ∀ f ∈ spikeFamily, ∀ n : ℕ, f n ≤ g n) ∧
    (∀ f ∈ spikeFamily, ¬ (fun _ : ℕ => 1) ≤ᶠ[atTop] f) ∧
    ¬ IsDominating spikeFamily := by
  classical
  have htail (i k n : ℕ) (hn : i + 1 ≤ n) :
      Function.update (fun _ : ℕ => 0) i k n = 0 := by
    rw [Function.update_of_ne (by omega)]
  have heventual : ∀ f ∈ spikeFamily, f ≤ᶠ[atTop] (fun _ => 0) := by
    rintro f ⟨⟨i, k⟩, rfl⟩
    exact Filter.eventually_atTop.mpr ⟨i + 1, fun n hn => (htail i k n hn).le⟩
  have hwitness (g : ℕ → ℕ) (i : ℕ) :
      Function.update (fun _ : ℕ => 0) i (g i + 1) ∈ spikeFamily ∧
      g i < Function.update (fun _ : ℕ => 0) i (g i + 1) i := by
    exact ⟨⟨(i, g i + 1), rfl⟩, by simp⟩
  have hpointwise : ¬ ∃ g : ℕ → ℕ, ∀ f ∈ spikeFamily, ∀ n : ℕ, f n ≤ g n := by
    rintro ⟨g, hg⟩
    exact (hwitness g 0).2.not_ge (hg _ (hwitness g 0).1 0)
  have hone : ∀ f ∈ spikeFamily, ¬ (fun _ : ℕ => 1) ≤ᶠ[atTop] f := by
    intro f hf hh
    obtain ⟨n, hn⟩ := (hh.and (heventual f hf)).exists
    dsimp at hn
    omega
  refine ⟨⟨fun _ => 0, heventual⟩, heventual, htail, hwitness, hpointwise, hone, ?_⟩
  intro hD
  obtain ⟨f, hf, hh⟩ := hD (fun _ => 1)
  exact hone f hf hh

end Lemmatheca.Entry.BoundingAndDominatingFamilies
