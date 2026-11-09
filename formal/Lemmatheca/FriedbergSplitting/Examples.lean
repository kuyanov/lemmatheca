import Lemmatheca.FriedbergSplitting.Verification
import Lemmatheca.FriedbergSplitting.DisjointUnion
import Lemmatheca.SimpleSets.Immunity

/-! Finite inputs and disjoint enumerable copies of the same noncomputable degree. -/
namespace Lemmatheca.Entry.FriedbergSplitting

open Lemmatheca.ComputabilityTheory
open FriedbergSplitting EffectiveEnumerations UniversalComputation TuringDegrees

noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem finite_input (a : ℕ) (ha : (indexSet a).Finite) :
    (∃ t, ∀ s ≥ t, ¬ HasArrival a s) ∧
      ∀ i < 2, (piece a i).Finite ∧ ComputablePred (piece a i) := by
  obtain ⟨t, ht⟩ := finite_global_stage (indexSet a) (processedSet a)
    (scheduler_monotone a) (scheduler_exhaustive a) ha
  refine ⟨⟨t, ?_⟩, ?_⟩
  · intro s hs harr
    have hm := (arrival_data a s).2.2.1 harr
    have hx : arrival a s ∈ indexSet a := (stage_union a _).mpr ⟨s + 1, hm.1⟩
    exact hm.2.1 (by rw [ht s hs]; exact hx)
  · intro i hi
    have hsub : piece a i ⊆ indexSet a := by
      intro x hx
      rw [← (routed_partition a).2.2.2]
      rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
      · exact Or.inl hx
      · exact Or.inr hx
    have hf := ha.subset hsub
    exact ⟨hf, SimpleSets.finite_decidable hf⟩

theorem empty_input (a : ℕ) (ha : indexSet a = ∅) :
    (∀ s, ¬ HasArrival a s) ∧ ∀ i < 2, piece a i = ∅ := by
  refine ⟨?_, ?_⟩
  · intro s hs
    have hx := (arrival_data a s).2.2.1 hs |>.1
    have hm := (stage_union a _).mpr ⟨s + 1, hx⟩
    simp [ha] at hm
  · intro i hi
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hm : x ∈ indexSet a := by
      rw [← (routed_partition a).2.2.2]
      rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
      · exact Or.inl hx
      · exact Or.inr hx
    simp [ha] at hm

def tagCopy (H : Set ℕ) (i : ℕ) : Set ℕ := (fun x => 2 * x + i) '' H

theorem tagged_example (H : Set ℕ) (hH : REPred H) (hn : ¬ ComputablePred H) :
    REPred (tagCopy H 0) ∧ REPred (tagCopy H 1) ∧
      Disjoint (tagCopy H 0) (tagCopy H 1) ∧
      Equivalent (tagCopy H 0) H ∧ Equivalent (tagCopy H 1) H ∧
      ¬ ComputablePred (tagCopy H 0) ∧ ¬ ComputablePred (tagCopy H 1) := by
  have he0 : tagCopy H 0 = join H ∅ := by simp [tagCopy, join]
  have he1 : tagCopy H 1 = join ∅ H := by simp [tagCopy, join]
  have hc0 : REPred (tagCopy H 0) := by
    exact (enumerable_image hH ((Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id) (Primrec.const 0)).to_comp)).of_eq (fun _ => Iff.rfl)
  have hc1 : REPred (tagCopy H 1) := by
    exact (enumerable_image hH ((Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id) (Primrec.const 1)).to_comp)).of_eq (fun _ => Iff.rfl)
  have hd : Disjoint (tagCopy H 0) (tagCopy H 1) := by
    apply Set.disjoint_left.mpr
    rintro z ⟨x, _, hx⟩ ⟨y, _, hy⟩
    dsimp at hx hy
    omega
  have hz : Reducible ∅ H := by
    obtain ⟨r, _, hr⟩ := computable_uniform ∅
      (show ComputablePred (fun n : ℕ => n ∈ (∅ : Set ℕ)) from ⟨inferInstance, Computable.const false⟩)
    exact ⟨OracleComputation.embed r, hr H⟩
  have h0 : Equivalent (tagCopy H 0) H := by
    rw [he0]
    exact ⟨(join_reducible_iff _ _ _).mpr ⟨reducible_refl H, hz⟩,
      manyOne_imp_reducible ⟨_, (join_even_reduction H ∅).1.to_comp, (join_even_reduction H ∅).2⟩⟩
  have h1 : Equivalent (tagCopy H 1) H := by
    rw [he1]
    exact ⟨(join_reducible_iff _ _ _).mpr ⟨hz, reducible_refl H⟩,
      manyOne_imp_reducible ⟨_, (join_odd_reduction ∅ H).1.to_comp, (join_odd_reduction ∅ H).2⟩⟩
  exact ⟨hc0, hc1, hd, h0, h1,
    fun hc => hn (computable_of_reducible h0.2 hc),
    fun hc => hn (computable_of_reducible h1.2 hc)⟩

end
end Lemmatheca.Entry.FriedbergSplitting
