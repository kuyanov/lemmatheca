import Lemmatheca.IndicesOfComputableEnumerableSets.Indices
import Lemmatheca.IndicesOfComputableEnumerableSets.Decoder

/-! The specified ordinary index map and both complete third-level classifications. -/
namespace Lemmatheca.ComputabilityTheory.ComputableDomainIndices
open EffectiveEnumerations UniversalComputation ArithmeticalHierarchy

theorem tagged_output_degree (g : ℕ → ℕ → ℕ) (hg : Primrec₂ g) (x : ℕ)
    (hrows : ∀ i, (indexSet (g x i)).Finite) :
    TuringDegrees.Equivalent (taggedOutput g hg x) haltingDiagonal := by
  have hce : REPred (taggedOutput g hg x) := by
    change REPred (ThirdLevelIndexSets.output (taggedSchedule g hg) x)
    rw [← ThirdLevelIndexSets.index_domain (taggedSchedule g hg) x]
    exact (phi_recursive.comp (Computable.const _) Computable.id).dom_re
  exact ⟨TuringDegrees.manyOne_imp_reducible
      (ProductiveAndCreativeSets.creative_complete ProductiveAndCreativeSets.diagonal_creative hce),
    ⟨decoderCode g hg x, decoder_reduces g hg x hrows⟩⟩

theorem tagged_output_not_computable (g : ℕ → ℕ → ℕ) (hg : Primrec₂ g) (x : ℕ)
    (hrows : ∀ i, (indexSet (g x i)).Finite) :
    ¬ ComputablePred (taggedOutput g hg x) := by
  intro hc
  exact haltingDiagonal_undecidable (TuringDegrees.computable_of_reducible
    (tagged_output_degree g hg x hrows).2 hc)

theorem two_outcome_reduction (A : Set ℕ) (g : ℕ → ℕ → ℕ) (hg : Primrec₂ g)
    (hrows : ∀ x, x ∈ A ↔ ∃ y, (indexSet (g x y)).Infinite) (x : ℕ) :
    (x ∈ A → (indexSet (taggedIndex g hg x))ᶜ.Finite) ∧
      (x ∉ A → TuringDegrees.Equivalent (indexSet (taggedIndex g hg x)) haltingDiagonal) := by
  classical
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := (hrows x).mp hx
    change ((indexSet (ThirdLevelIndexSets.index (taggedSchedule g hg) x))ᶜ).Finite
    rw [ThirdLevelIndexSets.index_domain]
    exact tagged_output_cofinite g hg x y hy
  · intro hx
    have hr : ∀ i, (indexSet (g x i)).Finite := by
      have hn : ¬ ∃ i, (indexSet (g x i)).Infinite := fun h => hx ((hrows x).mpr h)
      simpa only [not_exists, Set.Infinite, not_not] using hn
    change TuringDegrees.Equivalent
      (indexSet (ThirdLevelIndexSets.index (taggedSchedule g hg) x)) haltingDiagonal
    rw [ThirdLevelIndexSets.index_domain]
    exact tagged_output_degree g hg x hr

theorem tagged_index_reduction (A : Set ℕ) (g : ℕ → ℕ → ℕ) (hg : Primrec₂ g)
    (hrows : ∀ x, x ∈ A ↔ ∃ y, (indexSet (g x y)).Infinite) (x : ℕ) :
    x ∈ A ↔ taggedIndex g hg x ∈ ComputableIndices := by
  classical
  constructor
  · intro hx
    exact cofinite_subset_computable ((two_outcome_reduction A g hg hrows x).1 hx)
  · intro hc
    by_contra hx
    have hd := (two_outcome_reduction A g hg hrows x).2 hx
    exact haltingDiagonal_undecidable (TuringDegrees.computable_of_reducible hd.2 hc)

theorem computable_primitive_hardness (A : Set ℕ) (hA : Sigma ∅ 3 A) :
    ∃ g : ℕ → ℕ → ℕ, ∃ hg : Primrec₂ g,
      (∀ x, x ∈ A ↔ ∃ y, (indexSet (g x y)).Infinite) ∧
        Primrec (taggedIndex g hg) ∧
          ∀ x, x ∈ A ↔ taggedIndex g hg x ∈ ComputableIndices := by
  obtain ⟨g, hg, he⟩ := ThirdLevelIndexSets.uniform_infinite_rows A hA
  exact ⟨g, hg, he, ThirdLevelIndexSets.index_primitive (taggedSchedule g hg),
    tagged_index_reduction A g hg he⟩

theorem computable_complete : PostsTheorem.SigmaComplete ∅ 3 ComputableIndices := by
  refine ⟨computable_sigma_three, fun A hA => ?_⟩
  obtain ⟨g, hg, _, hp, he⟩ := computable_primitive_hardness A hA
  exact ⟨taggedIndex g hg, hp.to_comp, he⟩

theorem noncomputable_primitive_hardness (A : Set ℕ) (hA : Pi ∅ 3 A) :
    ∃ g : ℕ → ℕ → ℕ, ∃ hg : Primrec₂ g,
      Primrec (taggedIndex g hg) ∧
        ∀ x, x ∈ A ↔ taggedIndex g hg x ∈ NoncomputableIndices := by
  classical
  have hc : Sigma ∅ 3 (Aᶜ : Set ℕ) := (level_complement ∅ 3 false A).mp hA
  obtain ⟨g, hg, _, hp, he⟩ := computable_primitive_hardness Aᶜ hc
  refine ⟨g, hg, hp, fun x => ?_⟩
  simpa only [NoncomputableIndices, Set.mem_compl_iff, not_not] using not_congr (he x)

theorem noncomputable_complete : Pi ∅ 3 NoncomputableIndices ∧
    ∀ A : Set ℕ, Pi ∅ 3 A → ManyOneReducible A NoncomputableIndices := by
  refine ⟨noncomputable_pi_three, fun A hA => ?_⟩
  obtain ⟨g, hg, hp, he⟩ := noncomputable_primitive_hardness A hA
  exact ⟨taggedIndex g hg, hp.to_comp, he⟩

end Lemmatheca.ComputabilityTheory.ComputableDomainIndices
