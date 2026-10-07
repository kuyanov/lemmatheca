import Lemmatheca.SetTheory.FiniteErrors

/-! Particular finite-error counterexamples and tail witnesses. -/

namespace Lemmatheca.Entry.FiniteErrorsAndCountableDiagonalization

open Set Filter Lemmatheca.SetTheory.FiniteErrors

theorem almost_subset_not_antisymm :
    let E : Set ℕ := {n | n % 2 = 0}
    E ≠ insert 1 E ∧ E ≤ᶠ[cofinite] insert 1 E ∧ insert 1 E ≤ᶠ[cofinite] E := by
  dsimp
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have : 1 ∈ ({n : ℕ | n % 2 = 0} : Set ℕ) := h.symm ▸ mem_insert _ _
    norm_num at this
  · exact Filter.Eventually.of_forall fun n hn => mem_insert_of_mem _ hn
  · apply (almostSubset_iff_finite_sdiff _ _).mpr
    apply (finite_singleton 1).subset
    intro n hn
    rcases hn.1 with rfl | h
    · rfl
    · exact (hn.2 h).elim

theorem tails_pseudointersection :
    IsPseudointersection (Set.range (fun n : ℕ => Set.Ici n)) Set.univ ∧
    ∀ n : ℕ, Set.univ \ Set.Ici n = Set.Iio n := by
  have hd (n : ℕ) : univ \ Ici n = Iio n := by ext m; simp
  refine ⟨⟨infinite_univ, ?_⟩, hd⟩
  rintro S ⟨n, rfl⟩
  apply (almostSubset_iff_finite_sdiff _ _).mpr
  rw [hd]
  exact finite_Iio n

theorem finite_intersections_insufficient :
    let E : Set ℕ := {n | n % 2 = 0}
    let O : Set ℕ := {n | n % 2 = 1}
    Lemmatheca.SetTheory.FiltersAndUltrafilters.HasFiniteIntersectionProperty {insert 1 E, O} ∧
    (∀ S ∈ ({insert 1 E, O} : Set (Set ℕ)), S.Infinite) ∧
    insert 1 E ∩ O = {1} ∧
    ¬ ∃ B, IsPseudointersection {insert 1 E, O} B := by
  classical
  dsimp
  let E : Set ℕ := {n | n % 2 = 0}
  let O : Set ℕ := {n | n % 2 = 1}
  have hE : E.Infinite := parity_partition.1
  have hO : O.Infinite := parity_partition.2.1
  have hinter : insert 1 E ∩ O = {1} := by
    ext n
    simp only [mem_inter_iff, mem_insert_iff, mem_ofPred_eq, mem_singleton_iff, E, O]
    omega
  refine ⟨?_, ?_, hinter, ?_⟩
  · intro F hF hfin
    refine ⟨1, ?_⟩
    intro S hS
    have := hF hS
    simp only [mem_insert_iff, mem_singleton_iff] at this
    rcases this with rfl | rfl <;> simp
  · intro S hS
    simp only [mem_insert_iff, mem_singleton_iff] at hS
    rcases hS with rfl | rfl
    · exact hE.mono (subset_insert _ _)
    · exact hO
  · rintro ⟨B, hB⟩
    have hi := hB.strongFiniteIntersections {insert 1 E, O} Subset.rfl (by simp)
    rw [sInter_pair, hinter] at hi
    exact hi (finite_singleton 1)

theorem eventuallyLE_not_antisymm :
    ∃ f g : ℕ → ℕ, f ≠ g ∧ f =ᶠ[cofinite] g ∧
      f ≤ᶠ[atTop] g ∧ g ≤ᶠ[atTop] f := by
  let f : ℕ → ℕ := fun _ => 0
  let g : ℕ → ℕ := fun n => if n = 0 then 1 else 0
  have he : f =ᶠ[atTop] g := eventually_atTop.mpr ⟨1, fun n hn => by
    simp [f, g, show n ≠ 0 by omega]⟩
  refine ⟨f, g, ?_, ?_, he.le, he.symm.le⟩
  · intro h
    have := congrFun h 0
    norm_num [f, g] at this
  · rwa [Nat.cofinite_eq_atTop]

theorem constant_bound_example :
    (¬ ∃ g : ℕ → ℕ, ∀ i n : ℕ, i ≤ g n) ∧
    (∀ i n : ℕ, i ≤ n → i < n + 1) ∧
    (¬ ∃ N : ℕ, ∀ i n : ℕ, N ≤ n → i < n + 1) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨g, hg⟩
    have := hg (g 0 + 1) 0
    omega
  · intro i n hn; omega
  · rintro ⟨N, hN⟩
    have := hN (N + 1) N (le_refl _)
    omega

end Lemmatheca.Entry.FiniteErrorsAndCountableDiagonalization
