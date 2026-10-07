import Lemmatheca.SetTheory.PressingDown
import Lemmatheca.SetTheory.FinitePartialMaps
import Mathlib.SetTheory.Ordinal.Arithmetic

namespace Lemmatheca.Entry.PressingDownAndDeltaSystems

open Set Cardinal Ordinal
open Lemmatheca.SetTheory.PressingDown Lemmatheca.SetTheory.DeltaSystems
open Lemmatheca.SetTheory.FinitePartialMaps

def rootedPairs : Set (Set ℕ) := {a | ∃ n > 0, a = {0, n}}

theorem rooted_pairs_specification : IsDeltaSystem rootedPairs {0} ∧ rootedPairs.Infinite := by
  constructor
  · rintro a ⟨n, hn, rfl⟩ b ⟨m, hm, rfl⟩ hab
    have hnm : n ≠ m := fun h => hab (by rw [h])
    ext x
    simp only [mem_inter_iff, mem_insert_iff, mem_singleton_iff]
    omega
  · have hinj : Function.Injective (fun n : ℕ => ({0, n + 1} : Set ℕ)) := by
      intro n m h
      change ({0, n + 1} : Set ℕ) = {0, m + 1} at h
      have hmem : n + 1 ∈ ({0, m + 1} : Set ℕ) := by rw [← h]; simp
      simp only [mem_insert_iff, mem_singleton_iff] at hmem
      omega
    apply (Set.infinite_range_of_injective hinj).mono
    rintro a ⟨n, rfl⟩
    exact ⟨n + 1, by omega, rfl⟩

theorem omega_regressive_counterexample :
    IsStationary (Ioi (0 : ℕ)) ∧ RegressiveOn (Ioi 0) Nat.pred ∧
      ∀ n, ¬ IsStationary (Ioi 0 ∩ Nat.pred ⁻¹' {n}) := by
  refine ⟨?_, ?_, ?_⟩
  · intro C hC
    obtain ⟨n, hn, hn0⟩ := (Lemmatheca.SetTheory.Clubs.nat_club_iff_infinite C).mp hC |>.exists_gt 0
    exact ⟨n, hn0, hn⟩
  · intro n hn
    exact Nat.pred_lt hn.ne'
  · intro n h
    obtain ⟨m, hm, hmn⟩ := h (Lemmatheca.SetTheory.Clubs.tail_club (n + 1))
    have hm' : m.pred = n := hm.2
    rw [Nat.pred_eq_sub_one] at hm'
    have hmn' : n + 1 < m := hmn
    omega

def naturalInitialSegments : Set (Set ℕ) := Set.range (fun n : ℕ => Iio n)

theorem natural_initial_segments_specification :
    naturalInitialSegments.Countable ∧ naturalInitialSegments.Infinite ∧
      (∀ a ∈ naturalInitialSegments, a.Finite) ∧
      ∀ B ⊆ naturalInitialSegments, ∀ r, IsDeltaSystem B r → B.Finite ∧ B.ncard ≤ 2 := by
  have hinj : Function.Injective (fun n : ℕ => Iio n) := by
    intro n m h
    exact Set.Iio_inj.mp h
  refine ⟨Set.countable_range _, Set.infinite_range_of_injective hinj, ?_, ?_⟩
  · rintro a ⟨n, rfl⟩
    exact Set.finite_Iio n
  · intro B hB r hdelta
    exact initial_segment_delta_small hB hdelta

def countableInfiniteInitialSegments : Set (Set Ordinal.{0}) :=
  {a | ∃ o : Ordinal.{0}, omega0 ≤ o ∧ o < omega 1 ∧ a = Iio o}

theorem countable_infinite_initial_segments_specification :
    ¬ countableInfiniteInitialSegments.Countable ∧
      #countableInfiniteInitialSegments = Cardinal.lift.{1} (ℵ₁ : Cardinal.{0}) ∧
      (∀ a ∈ countableInfiniteInitialSegments, a.Countable ∧ a.Infinite) ∧
      ∀ B ⊆ countableInfiniteInitialSegments, ∀ r, IsDeltaSystem B r → B.Finite ∧ B.ncard ≤ 2 := by
  have hinj : Function.Injective (fun o : Ordinal.{0} => Iio o) := by
    intro a b h
    exact Set.Iio_inj.mp h
  have hwhole : #(Iio (omega 1 : Ordinal.{0})) = Cardinal.lift.{1} (ℵ₁ : Cardinal.{0}) := by
    rw [Cardinal.mk_Iio_ordinal, Ordinal.card_omega]
  have hsmall : #(Iio (omega0 : Ordinal.{0})) < #(Iio (omega 1 : Ordinal.{0})) := by
    rw [Cardinal.mk_Iio_ordinal, Ordinal.card_omega0, hwhole]
    exact Cardinal.lift_lt.mpr Cardinal.aleph0_lt_aleph_one
  have hwholeInf : (Iio (omega 1 : Ordinal.{0})).Infinite := by
    apply Cardinal.aleph0_le_mk_set.mp
    rw [hwhole]
    simp
  have hinterval : #(Ico (omega0 : Ordinal.{0}) (omega 1)) =
      Cardinal.lift.{1} (ℵ₁ : Cardinal.{0}) := by
    rw [← Set.Iio_sdiff_Iio]
    exact (Cardinal.mk_sdiff_eq_left hwholeInf hsmall).trans hwhole
  have heq : countableInfiniteInitialSegments =
      (fun o : Ordinal.{0} => Iio o) '' Ico omega0 (omega 1) := by
    ext a
    constructor
    · rintro ⟨o, ho0, ho1, rfl⟩
      exact ⟨o, ⟨ho0, ho1⟩, rfl⟩
    · rintro ⟨o, ⟨ho0, ho1⟩, rfl⟩
      exact ⟨o, ho0, ho1, rfl⟩
  have hcard : #countableInfiniteInitialSegments =
      Cardinal.lift.{1} (ℵ₁ : Cardinal.{0}) := by
    rw [heq, Cardinal.mk_image_eq hinj]
    exact hinterval
  refine ⟨?_, hcard, ?_, ?_⟩
  · intro h
    have hle := Cardinal.le_aleph0_iff_set_countable.mpr h
    rw [hcard] at hle
    have hlt : (ℵ₀ : Cardinal.{1}) < Cardinal.lift.{1} (ℵ₁ : Cardinal.{0}) := by
      simp
    exact hlt.not_ge hle
  · rintro a ⟨o, ho0, ho1, rfl⟩
    refine ⟨Cardinal.countable_Iio_of_lt_omega_one ho1, ?_⟩
    have hinf : (Iio (omega0 : Ordinal.{0})).Infinite := by
      apply Cardinal.aleph0_le_mk_set.mp
      simp only [Cardinal.mk_Iio_ordinal, Ordinal.card_omega0, Cardinal.lift_aleph0]
      exact le_rfl
    exact hinf.mono (fun x hx => hx.trans_le ho0)
  · intro B hB r hdelta
    apply initial_segment_delta_small (r := r) (hdelta := hdelta)
    intro a ha
    obtain ⟨o, _, _, rfl⟩ := hB ha
    exact ⟨o, rfl⟩

noncomputable def conflictLeft : BinaryMap (Fin 3) := by
  classical
  exact Finmap.insert 0 false (Finmap.singleton 1 false)

noncomputable def conflictRight : BinaryMap (Fin 3) := by
  classical
  exact Finmap.insert 0 true (Finmap.singleton 2 false)

theorem common_root_incompatible_specification :
    (conflictLeft.keys : Set (Fin 3)) = {0, 1} ∧
      (conflictRight.keys : Set (Fin 3)) = {0, 2} ∧
      IsDeltaSystem ({(conflictLeft.keys : Set (Fin 3)), (conflictRight.keys : Set (Fin 3))}) {0} ∧
      ¬ Compatible conflictLeft conflictRight := by
  classical
  have hl : (conflictLeft.keys : Set (Fin 3)) = {0, 1} := by
    ext x
    simp [conflictLeft, Finmap.mem_keys, Finmap.mem_insert, Finmap.mem_singleton]
  have hr : (conflictRight.keys : Set (Fin 3)) = {0, 2} := by
    ext x
    simp [conflictRight, Finmap.mem_keys, Finmap.mem_insert, Finmap.mem_singleton]
  refine ⟨hl, hr, ?_, ?_⟩
  · rw [hl, hr]
    intro a ha b hb hab
    simp only [mem_insert_iff, mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · contradiction
    · ext x
      simp only [mem_inter_iff, mem_insert_iff, mem_singleton_iff]
      have hx : x.val < 3 := x.isLt
      change ((x = 0 ∨ x = 1) ∧ (x = 0 ∨ x = 2)) ↔ x = 0
      omega
    · rw [inter_comm]
      ext x
      simp only [mem_inter_iff, mem_insert_iff, mem_singleton_iff]
      omega
    · contradiction
  · intro h
    have heq := (compatible_iff_agree conflictLeft conflictRight).mp h 0 false true
      (show (0, false) ∈ graph conflictLeft by
        change (⟨0, false⟩ : Sigma (fun _ : Fin 3 => Bool)) ∈ conflictLeft.entries
        exact Finmap.lookup_eq_some_iff.mp (by simp [conflictLeft]))
      (show (0, true) ∈ graph conflictRight by
        change (⟨0, true⟩ : Sigma (fun _ : Fin 3 => Bool)) ∈ conflictRight.entries
        exact Finmap.lookup_eq_some_iff.mp (by simp [conflictRight]))
    contradiction

end Lemmatheca.Entry.PressingDownAndDeltaSystems
