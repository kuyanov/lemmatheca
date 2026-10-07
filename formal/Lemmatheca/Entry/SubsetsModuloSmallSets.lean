import Lemmatheca.SetTheory.SubsetsModuloSmallSets

namespace Lemmatheca.Entry.SubsetsModuloSmallSets

open Set Filter
open scoped Classical symmDiff
open Lemmatheca.SetTheory.SubsetsModuloSmallSets

def smallCollection : Set (Set (Fin 2)) := {∅, {0}, {1}}

theorem smallCollection_counterexample :
    (∅ : Set (Fin 2)) ∈ smallCollection ∧ IsLowerSet smallCollection ∧
      ({0} : Set (Fin 2)) ∆ ∅ ∈ smallCollection ∧
      (∅ : Set (Fin 2)) ∆ {1} ∈ smallCollection ∧
      (({0} : Set (Fin 2)) ∆ {1}) = Set.univ ∧
      (Set.univ : Set (Fin 2)) ∉ smallCollection ∧
      ¬ IsTrans (Set (Fin 2)) (fun A B => A ∆ B ∈ smallCollection) := by
  have he : (∅ : Set (Fin 2)) ∈ smallCollection := by simp [smallCollection]
  have hzero : ({0} : Set (Fin 2)) ∆ ∅ ∈ smallCollection := by simp [smallCollection]
  have hone : (∅ : Set (Fin 2)) ∆ {1} ∈ smallCollection := by simp [smallCollection]
  have hfull : (({0} : Set (Fin 2)) ∆ {1}) = Set.univ := by
    ext x
    fin_cases x <;> simp [Set.symmDiff_def]
  have hnot : (Set.univ : Set (Fin 2)) ∉ smallCollection := by
    intro h
    simp only [smallCollection, Set.mem_insert_iff, Set.mem_singleton_iff] at h
    rcases h with h | h | h
    · have hh := congrArg (fun S : Set (Fin 2) => (0 : Fin 2) ∈ S) h
      simp at hh
    · have hh := congrArg (fun S : Set (Fin 2) => (1 : Fin 2) ∈ S) h
      simp at hh
    · have hh := congrArg (fun S : Set (Fin 2) => (0 : Fin 2) ∈ S) h
      simp at hh
  refine ⟨he, ?_, hzero, hone, hfull, hnot, ?_⟩
  · intro T S hST hT
    simp only [smallCollection, Set.mem_insert_iff, Set.mem_singleton_iff] at hT ⊢
    rcases hT with rfl | rfl | rfl
    · exact Or.inl (Set.subset_empty_iff.mp hST)
    · rcases Set.subset_singleton_iff_eq.mp hST with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · rcases Set.subset_singleton_iff_eq.mp hST with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
  · intro htrans
    exact hnot (hfull ▸ htrans.trans {0} ∅ {1} hzero hone)

def evenSet : Set ℕ := {n | n % 2 = 0}
def oddSet : Set ℕ := {n | n % 2 = 1}

theorem even_class_intermediate :
    mk (finiteIdeal ℕ) evenSet ≠ ⊥ ∧ mk (finiteIdeal ℕ) evenSet ≠ ⊤ := by
  have he : evenSet.Infinite := Lemmatheca.SetTheory.FiniteErrors.parity_partition.1
  have ho : oddSet.Infinite := Lemmatheca.SetTheory.FiniteErrors.parity_partition.2.1
  have hcompl : evenSetᶜ = oddSet := by
    ext n
    simp only [evenSet, oddSet, Set.mem_compl_iff, Set.mem_ofPred_eq]
    omega
  refine ⟨(finite_quotient_nonzero_iff evenSet).mpr he, ?_⟩
  intro h
  have hf := (quotient_one_iff (finiteIdeal ℕ) evenSet).mp h
  change evenSetᶜ.Finite at hf
  exact ho (hcompl ▸ hf)

theorem parity_representatives_example :
    mk (finiteIdeal ℕ) evenSet = mk (finiteIdeal ℕ) (evenSet ∪ {1}) ∧
      evenSet ∩ oddSet = ∅ ∧ (evenSet ∪ {1}) ∩ oddSet = {1} ∧
      mk (finiteIdeal ℕ) evenSet ⊓ mk (finiteIdeal ℕ) oddSet = ⊥ ∧
      mk (finiteIdeal ℕ) (evenSet ∪ {1}) ⊓ mk (finiteIdeal ℕ) oddSet = ⊥ := by
  have heq : mk (finiteIdeal ℕ) evenSet = mk (finiteIdeal ℕ) (evenSet ∪ {1}) := by
    apply (finite_quotient_eq_iff _ _).mpr
    filter_upwards [(Set.finite_singleton (1 : ℕ)).compl_mem_cofinite] with n hn
    have hn1 : n ≠ 1 := by simpa using hn
    simp [hn1]
  have hdis : evenSet ∩ oddSet = ∅ :=
    Lemmatheca.SetTheory.FiniteErrors.parity_partition.2.2.1
  have hnew : (evenSet ∪ {1}) ∩ oddSet = {1} := by
    ext n
    simp only [Set.mem_inter_iff, Set.mem_union, Set.mem_singleton_iff,
      evenSet, oddSet, Set.mem_ofPred_eq]
    omega
  refine ⟨heq, hdis, hnew, ?_, ?_⟩
  · apply (finite_quotient_zero_meet_iff evenSet oddSet).mpr
    rw [hdis]
    exact Set.finite_empty
  · apply (finite_quotient_zero_meet_iff (evenSet ∪ {1}) oddSet).mpr
    rw [hnew]
    exact Set.finite_singleton 1

theorem tail_intersection_counterexample :
    (∀ n : ℕ, mk (finiteIdeal ℕ) (Set.Ici n) = (⊤ : FiniteQuotient)) ∧
      (⋂ n : ℕ, Set.Ici n) = ∅ ∧
      (∀ n : ℕ, mk (finiteIdeal ℕ) (Set.Ici n) = mk (finiteIdeal ℕ) Set.univ) ∧
      mk (finiteIdeal ℕ) (⋂ n : ℕ, Set.Ici n) ≠
        mk (finiteIdeal ℕ) (⋂ _ : ℕ, (Set.univ : Set ℕ)) ∧
      (⊤ : FiniteQuotient) ≠ ⊥ ∧
      IsGLB (Set.range (fun n : ℕ => mk (finiteIdeal ℕ) (Set.Ici n))) ⊤ := by
  have htail (n : ℕ) : mk (finiteIdeal ℕ) (Set.Ici n) = (⊤ : FiniteQuotient) := by
    apply (quotient_one_iff _ _).mpr
    change (Set.Ici n)ᶜ.Finite
    simpa only [Set.compl_Ici] using Set.finite_Iio n
  have hinter : (⋂ n : ℕ, Set.Ici n) = ∅ :=
    Lemmatheca.SetTheory.FiltersAndUltrafilters.tails_example.2.2
  have huniv : mk (finiteIdeal ℕ) Set.univ = (⊤ : FiniteQuotient) :=
    (quotient_operations (finiteIdeal ℕ) ∅ ∅).2.2.2.2.symm
  have hempty : mk (finiteIdeal ℕ) ∅ = (⊥ : FiniteQuotient) :=
    (quotient_operations (finiteIdeal ℕ) ∅ ∅).2.2.2.1.symm
  refine ⟨htail, hinter, fun n => (htail n).trans huniv.symm, ?_, top_ne_bot, ?_⟩
  · simpa only [hinter, Set.iInter_const, hempty, huniv] using
      (bot_ne_top : (⊥ : FiniteQuotient) ≠ ⊤)
  · refine ⟨?_, ?_⟩
    · rintro q ⟨n, rfl⟩
      dsimp
      rw [htail n]
    · intro q _
      exact le_top

end Lemmatheca.Entry.SubsetsModuloSmallSets
