import Lemmatheca.SetTheory.FiltersAndUltrafilters

/-! Particular examples and counterexamples for the human entry. -/

namespace Lemmatheca.Entry.FiltersAndUltrafilters
open Lemmatheca.SetTheory.FiltersAndUltrafilters
open Set Filter
universe u

theorem cofinite_parity :
    {n : ℕ | n % 2 = 0} ∉ (cofinite : Filter ℕ) ∧
    {n : ℕ | n % 2 = 1} ∉ (cofinite : Filter ℕ) := by
  have hinf (r : ℕ) (hr : r < 2) : Set.Infinite {n : ℕ | n % 2 = r} := by
    apply (Set.infinite_range_of_injective (f := fun n : ℕ => 2 * n + r)
      (fun a b h => by dsimp at h; omega)).mono
    rintro _ ⟨n, rfl⟩
    simp [Nat.add_mod, hr]
  constructor
  · rw [mem_cofinite]
    intro h
    exact (hinf 1 (by omega)).not_finite (h.subset (by intro n hn; simp only [mem_ofPred_eq, mem_compl_iff] at *; omega))
  · rw [mem_cofinite]
    intro h
    exact (hinf 0 (by omega)).not_finite (h.subset (by intro n hn; simp only [mem_ofPred_eq, mem_compl_iff] at *; omega))

theorem parity_extensions : ∃ U V : Ultrafilter ℕ,
    (U : Filter ℕ) ≤ cofinite ∧ (V : Filter ℕ) ≤ cofinite ∧
    {n : ℕ | n % 2 = 0} ∈ U ∧ {n : ℕ | n % 2 = 1} ∈ V ∧ U ≠ V := by
  have hinf (r : ℕ) (hr : r < 2) : Set.Infinite {n : ℕ | n % 2 = r} := by
    apply (Set.infinite_range_of_injective (f := fun n : ℕ => 2 * n + r)
      (fun a b h => by dsimp at h; omega)).mono
    rintro _ ⟨n, rfl⟩
    simp [Nat.add_mod, hr]
  have he : NeBot ((cofinite : Filter ℕ) ⊓ principal {n | n % 2 = 0}) :=
    cofinite_inf_principal_neBot_iff.mpr (hinf 0 (by omega))
  have ho : NeBot ((cofinite : Filter ℕ) ⊓ principal {n | n % 2 = 1}) :=
    cofinite_inf_principal_neBot_iff.mpr (hinf 1 (by omega))
  obtain ⟨U, hU⟩ := Ultrafilter.exists_le ((cofinite : Filter ℕ) ⊓ principal {n | n % 2 = 0})
  obtain ⟨V, hV⟩ := Ultrafilter.exists_le ((cofinite : Filter ℕ) ⊓ principal {n | n % 2 = 1})
  have hUm := le_principal_iff.mp (hU.trans inf_le_right)
  have hVm := le_principal_iff.mp (hV.trans inf_le_right)
  refine ⟨U, V, hU.trans inf_le_left, hV.trans inf_le_left, hUm, hVm, ?_⟩
  intro huv
  subst V
  have hempty : ({n : ℕ | n % 2 = 0} ∩ {n : ℕ | n % 2 = 1}) = ∅ := by
    ext n
    simp only [mem_inter_iff, mem_ofPred_eq, mem_empty_iff_false, iff_false]
    omega
  exact Filter.empty_notMem (U : Filter ℕ) (hempty ▸ inter_mem hUm hVm)

end Lemmatheca.Entry.FiltersAndUltrafilters
