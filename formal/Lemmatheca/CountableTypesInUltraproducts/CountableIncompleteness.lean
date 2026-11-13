import Lemmatheca.FiltersAndUltrafilters.FiltersAndUltrafilters

namespace Lemmatheca.ModelTheory.Ultraproducts.CountableTypes

open Filter Set
universe w

/-- A normalized decreasing sequence of large sets with empty intersection. -/
structure IncompletenessWitness {I : Type w} (U : Ultrafilter I) where
  sets : ℕ → Set I
  zero : sets 0 = univ
  decreasing : Antitone sets
  large : ∀ n, sets n ∈ U
  empty : (⋂ n, sets n) = ∅

/-- Countable incompleteness concerns this ultrafilter, not the factor structures. -/
def CountablyIncomplete {I : Type w} (U : Ultrafilter I) : Prop :=
  Nonempty (IncompletenessWitness U)

theorem normalize {I : Type w} (U : Ultrafilter I) (E : ℕ → Set I)
    (hE : ∀ n, E n ∈ U) (hempty : (⋂ n, E n) = ∅) :
    ∃ X : IncompletenessWitness U, ∀ n, X.sets n = ⋂ k ∈ Finset.range n, E k := by
  classical
  let X : ℕ → Set I := fun n => ⋂ k ∈ Finset.range n, E k
  refine ⟨⟨X, by simp [X], ?_, ?_, ?_⟩, fun _ => rfl⟩
  · intro n m hnm i hi
    simp only [X, mem_iInter] at hi ⊢
    intro k hk
    exact hi k (Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hk) hnm))
  · intro n
    exact (Filter.biInter_finset_mem (Finset.range n)).mpr (fun k _ => hE k)
  · apply Set.eq_empty_iff_forall_notMem.mpr
    intro i hi
    have h : i ∈ ⋂ n, E n := by
      simp only [mem_iInter] at hi ⊢
      intro n
      have hh := hi (n + 1)
      change i ∈ ⋂ k ∈ Finset.range (n + 1), E k at hh
      exact mem_iInter.mp (mem_iInter.mp hh n) (by simp)
    rw [hempty] at h
    exact h

theorem nonprincipal_nat (U : Ultrafilter ℕ)
    (hU : ¬Lemmatheca.SetTheory.FiltersAndUltrafilters.IsPrincipal (U : Filter ℕ)) :
    ∃ X : IncompletenessWitness U, ∀ n, X.sets n = Ici n := by
  have hcof :=
    (Lemmatheca.SetTheory.FiltersAndUltrafilters.nonprincipal_iff_cofinite U).mp hU
  refine ⟨⟨fun n => Ici n, ?_, ?_, ?_, ?_⟩, fun _ => rfl⟩
  · ext i
    simp
  · intro n m hnm i hi
    exact hnm.trans hi
  · intro n
    exact hcof (Lemmatheca.SetTheory.FiltersAndUltrafilters.tails_example.1 n)
  · exact Lemmatheca.SetTheory.FiltersAndUltrafilters.tails_example.2.2

theorem principal_not_incomplete {I : Type w} (i₀ : I) :
    ¬CountablyIncomplete (pure i₀ : Ultrafilter I) := by
  rintro ⟨X⟩
  have hi : i₀ ∈ ⋂ n, X.sets n := by
    simp only [mem_iInter]
    intro n
    have h := X.large n
    simpa using h
  rw [X.empty] at hi
  exact hi

/-- First index at which a coordinate leaves a decreasing sequence. -/
noncomputable def exitBound {I : Type w} (Y : ℕ → Set I)
    (hempty : (⋂ n, Y n) = ∅) (i : I) : ℕ := by
  classical
  exact Nat.find (show ∃ n, i ∉ Y n from by
    by_contra h
    have hi : i ∈ ⋂ n, Y n := by simpa only [mem_iInter, not_exists, not_not] using h
    rw [hempty] at hi
    exact hi)

/-- The largest surviving index, searched below the specified first exit. -/
noncomputable def cutoff {I : Type w} (Y : ℕ → Set I)
    (hempty : (⋂ n, Y n) = ∅) (i : I) : ℕ := by
  classical
  exact Nat.findGreatest (fun n => i ∈ Y n) (exitBound Y hempty i)

theorem cutoff_maximum {I : Type w} (Y : ℕ → Set I)
    (hzero : Y 0 = univ) (hanti : Antitone Y) (hempty : (⋂ n, Y n) = ∅) (i : I) :
    i ∈ Y (cutoff Y hempty i) ∧ ∀ n, i ∈ Y n ↔ n ≤ cutoff Y hempty i := by
  classical
  have hexit : i ∉ Y (exitBound Y hempty i) := by
    unfold exitBound
    exact Nat.find_spec (p := fun n => i ∉ Y n) _
  have hmem : i ∈ Y (cutoff Y hempty i) := by
    unfold cutoff
    apply Nat.findGreatest_spec (P := fun n => i ∈ Y n) (m := 0) (Nat.zero_le _)
    rw [hzero]
    trivial
  refine ⟨hmem, fun n => ⟨?_, ?_⟩⟩
  · intro hn
    have hbound : n ≤ exitBound Y hempty i := by
      by_contra hh
      exact hexit (hanti (by omega) hn)
    by_contra hh
    exact Nat.findGreatest_is_greatest (by simpa [cutoff] using (show cutoff Y hempty i < n by omega)) hbound hn
  · intro hn
    exact hanti hn hmem

end Lemmatheca.ModelTheory.Ultraproducts.CountableTypes
