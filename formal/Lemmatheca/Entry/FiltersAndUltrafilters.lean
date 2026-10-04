import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Order.Filter.Bases.Finite
import Mathlib.Order.Filter.Cofinite

namespace Lemmatheca.Entry.FiltersAndUltrafilters
open Set Filter
universe u

def IsPrincipal {α : Type u} (F : Filter α) : Prop :=
  ∃ S : Set α, S.Nonempty ∧ F = principal S

def HasFiniteIntersectionProperty {α : Type u} (B : Set (Set α)) : Prop :=
  ∀ t : Set (Set α), t ⊆ B → t.Finite → (⋂₀ t).Nonempty

theorem tails_example :
    (∀ n : ℕ, Set.Ici n ∈ (cofinite : Filter ℕ)) ∧
    (∀ t : Finset ℕ, (⋂ n ∈ t, Set.Ici n) = Set.Ici (t.sup id)) ∧
    (⋂ n : ℕ, Set.Ici n) = ∅ := by
  constructor
  · intro n
    rw [Nat.cofinite_eq_atTop]
    exact Ici_mem_atTop n
  constructor
  · intro t
    ext m
    simp only [mem_iInter, mem_Ici, Finset.sup_le_iff]
    rfl
  · ext m
    simp only [mem_iInter, mem_Ici, mem_empty_iff_false, iff_false]
    exact fun h => Nat.not_succ_le_self m (h (m + 1))

theorem tails_generate : generate (Set.range (fun n : ℕ => Set.Ici n)) =
    (cofinite : Filter ℕ) := by
  rw [Nat.cofinite_eq_atTop, atTop_eq_generate_Ici]

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

theorem finite_partition {α ι : Type u} [Finite ι] (U : Ultrafilter α)
    (A : ι → Set α) (hc : (⋃ i, A i) = univ)
    (hd : Pairwise (fun i j => Disjoint (A i) (A j))) :
    ∃! i, A i ∈ U := by
  have hmem : (⋃ i ∈ (univ : Set ι), A i) ∈ U := by
    simp only [Set.mem_univ, iUnion_true]
    change (⋃ i, A i) ∈ (U : Filter α)
    rw [hc]
    exact univ_mem
  obtain ⟨i, _, hi⟩ := (U.finite_biUnion_mem_iff Set.finite_univ).mp hmem
  refine ⟨i, hi, ?_⟩
  intro j hj
  by_contra hji
  have hempty : A j ∩ A i = ∅ := (Set.disjoint_iff_inter_eq_empty.mp (hd hji))
  exact Filter.empty_notMem (U : Filter α) (hempty ▸ inter_mem hj hi)

theorem principal_ultrafilter_iff {α : Type u} (U : Ultrafilter α) :
    IsPrincipal (U : Filter α) ↔ ∃ x : α, U = pure x := by
  constructor
  · rintro ⟨S, ⟨x, hx⟩, hS⟩
    refine ⟨x, ?_⟩
    apply Ultrafilter.coe_injective
    exact (U.unique (g := (pure x : Filter α)) (by
      rw [hS, le_principal_iff]
      exact mem_pure.mpr hx)).symm
  · rintro ⟨x, rfl⟩
    exact ⟨{x}, Set.singleton_nonempty x, by ext s; simp⟩

theorem nonprincipal_iff_cofinite {α : Type u} [Infinite α] (U : Ultrafilter α) :
    ¬ IsPrincipal (U : Filter α) ↔ (U : Filter α) ≤ cofinite := by
  constructor
  · intro h
    exact (U.le_cofinite_or_eq_pure).resolve_right (fun hp => h ((principal_ultrafilter_iff U).mpr hp))
  · intro h hp
    obtain ⟨x, rfl⟩ := (principal_ultrafilter_iff U).mp hp
    have hx : ({x}ᶜ : Set α) ∈ (pure x : Filter α) := h (Set.finite_singleton x).compl_mem_cofinite
    simp at hx

theorem finite_changes {α : Type u} (U : Ultrafilter α)
    (hU : (U : Filter α) ≤ cofinite) (A B : Set α)
    (h : ((A \ B) ∪ (B \ A)).Finite) : A ∈ U ↔ B ∈ U := by
  have hD : ((A \ B) ∪ (B \ A))ᶜ ∈ (U : Filter α) := hU h.compl_mem_cofinite
  constructor
  · intro hA
    apply mem_of_superset (inter_mem hA hD)
    intro x hx
    simp only [mem_inter_iff, mem_compl_iff, mem_union, Set.mem_sdiff] at hx
    tauto
  · intro hB
    apply mem_of_superset (inter_mem hB hD)
    intro x hx
    simp only [mem_inter_iff, mem_compl_iff, mem_union, Set.mem_sdiff] at hx
    tauto

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
