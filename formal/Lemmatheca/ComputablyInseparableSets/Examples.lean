import Lemmatheca.ComputablyInseparableSets.NegativeSearch

namespace Lemmatheca.Entry.ComputablyInseparableSets

open Lemmatheca.ComputabilityTheory.ComputableSeparation
open Lemmatheca.ComputabilityTheory.UniversalComputation


private theorem computable_and {P Q : ℕ → Prop}
    (hP : ComputablePred P) (hQ : ComputablePred Q) :
    ComputablePred (fun x => P x ∧ Q x) := by
  classical
  exact ((Primrec.and.to_comp.comp hP.decide hQ.decide).of_eq fun x => by simp).computablePred

private theorem computable_or {P Q : ℕ → Prop}
    (hP : ComputablePred P) (hQ : ComputablePred Q) :
    ComputablePred (fun x => P x ∨ Q x) := by
  classical
  exact ((Primrec.or.to_comp.comp hP.decide hQ.decide).of_eq fun x => by simp).computablePred

theorem residue_description :
    {x : ℕ | ∃ n, x = 4 * n} = {x | x % 4 = 0} ∧
      {x : ℕ | ∃ n, x = 4 * n + 2} = {x | x % 4 = 2} := by
  constructor
  · ext x
    constructor
    · rintro ⟨n, rfl⟩
      change (4 * n) % 4 = 0
      omega
    · intro hx
      change x % 4 = 0 at hx
      exact ⟨x / 4, by omega⟩
  · ext x
    constructor
    · rintro ⟨n, rfl⟩
      change (4 * n + 2) % 4 = 2
      omega
    · intro hx
      change x % 4 = 2 at hx
      exact ⟨x / 4, by omega⟩

theorem residue_separator :
    ComputablePred (fun x : ℕ => x % 4 = 0) ∧
      Separator {x | x % 4 = 0} {x | x % 4 = 2} {x | x % 4 = 0} := by
  refine ⟨(Primrec.eq.comp (Primrec.nat_mod.comp Primrec.id (Primrec.const 4))
    (Primrec.const 0)).computablePred, Set.Subset.rfl, ?_⟩
  exact Set.disjoint_left.mpr fun _ h0 h2 => by
    change _ % 4 = 0 at h0
    change _ % 4 = 2 at h2
    omega

theorem evens_not_separator :
    ¬ Separator {x : ℕ | x % 4 = 0} {x | x % 4 = 2} {x | x % 2 = 0} := by
  intro h
  exact Set.disjoint_left.mp h.2 (by decide : 2 ∈ {x : ℕ | x % 2 = 0})
    (by decide : 2 ∈ {x : ℕ | x % 4 = 2})

theorem all_residue_separators (C : Set ℕ) :
    Separator {x | x % 4 = 0} {x | x % 4 = 2} C ↔
      ∃ D : Set ℕ, D ⊆ {x | x % 2 = 1} ∧ C = {x | x % 4 = 0} ∪ D := by
  constructor
  · intro h
    refine ⟨C ∩ {x | x % 2 = 1}, fun _ hx => hx.2, ?_⟩
    ext x
    constructor
    · intro hx
      by_cases h0 : x % 4 = 0
      · exact Or.inl h0
      · have h2 : x % 4 ≠ 2 := fun hz => Set.disjoint_left.mp h.2 hx hz
        exact Or.inr ⟨hx, show x % 2 = 1 from by omega⟩
    · rintro (h0 | ⟨hc, _⟩)
      · exact h.1 h0
      · exact hc
  · rintro ⟨D, hD, rfl⟩
    refine ⟨fun _ hx => Or.inl hx, Set.disjoint_left.mpr ?_⟩
    intro x hc h2
    rcases hc with h0 | hd
    · change x % 4 = 0 at h0
      change x % 4 = 2 at h2
      omega
    · have ho := hD hd
      change x % 2 = 1 at ho
      change x % 4 = 2 at h2
      omega

theorem decidable_odd_choices (D : Set ℕ) (hD : D ⊆ {x | x % 2 = 1}) :
    ComputablePred (fun x => x ∈ {n | n % 4 = 0} ∪ D) ↔
      ComputablePred (fun x => x ∈ D) := by
  have hmod := (Primrec.eq.comp
    (Primrec.nat_mod.comp Primrec.id (Primrec.const 4)) (Primrec.const 0)).computablePred
  have hodd := (Primrec.eq.comp
    (Primrec.nat_mod.comp Primrec.id (Primrec.const 2)) (Primrec.const 1)).computablePred
  constructor
  · intro hc
    apply (computable_and hc hodd).of_eq
    intro x
    constructor
    · rintro ⟨h, ho⟩
      rcases h with h0 | hd
      · change x % 4 = 0 at h0
        change x % 2 = 1 at ho
        omega
      · exact hd
    · intro hd
      exact ⟨Or.inr hd, hD hd⟩
  · intro hd
    exact computable_or hmod hd

theorem constant_two_outside :
    ∃ q, (∀ x, phi q x = Part.some 2) ∧ q ∉ diagonalOutput 0 ∪ diagonalOutput 1 := by
  obtain ⟨q, hq⟩ := phi_complete (Nat.Partrec.of_primrec (Nat.Primrec.const 2))
  exact ⟨q, fun x => congrFun hq x, by simp [diagonalOutput, hq]⟩

theorem nowhere_defined_outside :
    ∃ q, (∀ x, phi q x = Part.none) ∧ q ∉ diagonalOutput 0 ∪ diagonalOutput 1 := by
  obtain ⟨q, hq⟩ := phi_complete Nat.Partrec.none
  exact ⟨q, fun x => congrFun hq x, by simp [diagonalOutput, hq]⟩

def instantLeft (x _t : ℕ) : Prop := x ≠ 0
def delayedLeft (x t : ℕ) : Prop := x ≠ 0 ∧ 1 ≤ t
def instantRight (x _t : ℕ) : Prop := x ≠ 2

theorem fixture_certificates :
    PrimrecPred (fun p : ℕ × ℕ => instantLeft p.1 p.2) ∧
    PrimrecPred (fun p : ℕ × ℕ => delayedLeft p.1 p.2) ∧
    PrimrecPred (fun p : ℕ × ℕ => instantRight p.1 p.2) ∧
    (∀ x, x ∉ ({0} : Set ℕ) ↔ ∃ t, instantLeft x t) ∧
    (∀ x, x ∉ ({0} : Set ℕ) ↔ ∃ t, delayedLeft x t) ∧
    (∀ x, x ∉ ({2} : Set ℕ) ↔ ∃ t, instantRight x t) := by
  have h0 : PrimrecPred (fun p : ℕ × ℕ => p.1 ≠ 0) :=
    (Primrec.eq.comp Primrec.fst (Primrec.const 0)).not
  have h1 : PrimrecPred (fun p : ℕ × ℕ => 1 ≤ p.2) :=
    Primrec.nat_le.comp (Primrec.const 1) Primrec.snd
  have h2 : PrimrecPred (fun p : ℕ × ℕ => p.1 ≠ 2) :=
    (Primrec.eq.comp Primrec.fst (Primrec.const 2)).not
  refine ⟨h0, h0.and h1, h2, ?_, ?_, ?_⟩
  · intro x
    simp [instantLeft]
  · intro x
    simp only [Set.mem_singleton_iff, delayedLeft]
    exact ⟨fun hx => ⟨1, hx, le_rfl⟩, fun ⟨_, hx, _⟩ => hx⟩
  · intro x
    simp [instantRight]

theorem instant_cover : ∀ x, ∃ t, instantLeft x t ∨ instantRight x t := by
  intro x
  by_cases h : x = 0
  · exact ⟨0, Or.inr (by simp [instantRight, h])⟩
  · exact ⟨0, Or.inl h⟩

theorem delayed_cover : ∀ x, ∃ t, delayedLeft x t ∨ instantRight x t := by
  intro x
  by_cases h : x = 0
  · exact ⟨0, Or.inr (by simp [instantRight, h])⟩
  · exact ⟨1, Or.inl ⟨h, le_rfl⟩⟩

theorem race_fixture_values :
    raceTotal instantLeft instantRight instant_cover 0 = 1 ∧
    raceTotal instantLeft instantRight instant_cover 1 = 0 ∧
    raceTotal instantLeft instantRight instant_cover 2 = 0 ∧
    raceTotal delayedLeft instantRight delayed_cover 0 = 1 ∧
    raceTotal delayedLeft instantRight delayed_cover 1 = 1 ∧
    raceTotal delayedLeft instantRight delayed_cover 2 = 0 := by
  classical
  have atStage (R S : ℕ → ℕ → Prop) (hc : ∀ x, ∃ t, R x t ∨ S x t)
      (x t : ℕ) (ht : t ∈ raceStage R S x) :
      raceTotal R S hc x = if R x t then 0 else 1 := by
    have h := negativeRace_at_stage R S x t ht
    rw [negativeRace_total_value R S hc] at h
    exact Part.some_injective h
  have stage0 (x : ℕ) : 0 ∈ raceStage instantLeft instantRight x := by
    apply (raceStage_spec _ _ _ _).mpr
    refine ⟨?_, fun i hi => by omega⟩
    simp only [instantLeft, instantRight]
    omega
  have delay0 : 0 ∈ raceStage delayedLeft instantRight 0 := by
    apply (raceStage_spec _ _ _ _).mpr
    exact ⟨Or.inr (by simp [instantRight]), fun i hi => by omega⟩
  have delay1 : 0 ∈ raceStage delayedLeft instantRight 1 := by
    apply (raceStage_spec _ _ _ _).mpr
    exact ⟨Or.inr (by simp [instantRight]), fun i hi => by omega⟩
  have delay2 : 1 ∈ raceStage delayedLeft instantRight 2 := by
    apply (raceStage_spec _ _ _ _).mpr
    refine ⟨Or.inl (by simp [delayedLeft]), ?_⟩
    intro i hi
    have he : i = 0 := by omega
    simp [he, delayedLeft, instantRight]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [instantLeft] using atStage _ _ instant_cover 0 0 (stage0 0)
  · simpa [instantLeft] using atStage _ _ instant_cover 1 0 (stage0 1)
  · simpa [instantLeft] using atStage _ _ instant_cover 2 0 (stage0 2)
  · simpa [delayedLeft] using atStage _ _ delayed_cover 0 0 delay0
  · simpa [delayedLeft] using atStage _ _ delayed_cover 1 0 delay1
  · simpa [delayedLeft] using atStage _ _ delayed_cover 2 1 delay2


end Lemmatheca.Entry.ComputablyInseparableSets
