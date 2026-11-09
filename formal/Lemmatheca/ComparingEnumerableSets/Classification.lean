import Lemmatheca.ComparingEnumerableSets.Relations
import Lemmatheca.IndexSetCompleteness.Classification

/-! The specified whole-domain map and its exact completeness consequences. -/
namespace Lemmatheca.ComputabilityTheory.ComparingEnumerableSets

open EffectiveEnumerations ArithmeticalHierarchy UniversalComputation
open IndexSetCompleteness

local notation "TOT" => Lemmatheca.Entry.ArithmeticalHierarchy.Totality

def wholeIndex : ℕ := Encodable.encode (Nat.Partrec.Code.const 0)

theorem whole_index_output (x : ℕ) : phi wholeIndex x = Part.some 0 := by
  simp [phi, wholeIndex, Nat.Partrec.Code.eval_const]

theorem whole_index_domain : indexSet wholeIndex = Set.univ := by
  ext x
  change (phi wholeIndex x).Dom ↔ True
  rw [whole_index_output]
  simp

def wholeDomainMap (e : ℕ) : ℕ := Nat.pair wholeIndex e

theorem whole_domain_map_primitive : Primrec wholeDomainMap := by
  exact Primrec₂.natPair.comp (Primrec.const wholeIndex) Primrec.id

theorem whole_domain_comparisons (e : ℕ) :
    (wholeDomainMap e ∈ Inclusion ↔ e ∈ TOT) ∧
      (wholeDomainMap e ∈ Equality ↔ e ∈ TOT) := by
  constructor
  · rw [wholeDomainMap, (coded_comparisons wholeIndex e).1, whole_index_domain]
    change Set.univ ⊆ indexSet e ↔ ∀ x, (phi e x).Dom
    exact ⟨fun h x => h (Set.mem_univ x), fun h x _ => h x⟩
  · rw [wholeDomainMap, (coded_comparisons wholeIndex e).2, whole_index_domain]
    change Set.univ = indexSet e ↔ ∀ x, (phi e x).Dom
    constructor
    · intro h x
      have : x ∈ indexSet e := h ▸ Set.mem_univ x
      exact this
    · intro h
      exact (Set.eq_univ_of_forall h).symm

noncomputable def comparisonMap (r : Matrix) (hr : MatrixComputable r) (x : ℕ) : ℕ :=
  wholeDomainMap (totalMap r hr x)

theorem comparison_map_primitive (r : Matrix) (hr : MatrixComputable r) :
    Primrec (comparisonMap r hr) := by
  exact whole_domain_map_primitive.comp (totalMap_primitive r hr)

theorem comparison_primitive_hardness (A : Set ℕ) (hA : Pi ∅ 2 A) :
    ∃ r : Matrix, ∃ hr : MatrixComputable r,
      Primrec (comparisonMap r hr) ∧
        ∀ x, (x ∈ A ↔ comparisonMap r hr x ∈ Inclusion) ∧
          (x ∈ A ↔ comparisonMap r hr x ∈ Equality) := by
  obtain ⟨r, hr, _, he⟩ := totality_primitive_hardness A hA
  refine ⟨r, hr, comparison_map_primitive r hr, fun x => ?_⟩
  exact ⟨(he x).trans (whole_domain_comparisons (totalMap r hr x)).1.symm,
    (he x).trans (whole_domain_comparisons (totalMap r hr x)).2.symm⟩

theorem comparison_completeness : PiComplete Inclusion ∧ PiComplete Equality := by
  constructor
  · refine ⟨inclusion_pi_two, fun A hA => ?_⟩
    obtain ⟨r, hr, hp, he⟩ := comparison_primitive_hardness A hA
    exact ⟨comparisonMap r hr, hp.to_comp, fun x => (he x).1⟩
  · refine ⟨equality_pi_two, fun A hA => ?_⟩
    obtain ⟨r, hr, hp, he⟩ := comparison_primitive_hardness A hA
    exact ⟨comparisonMap r hr, hp.to_comp, fun x => (he x).2⟩

theorem negative_primitive_hardness (A : Set ℕ) (hA : Sigma ∅ 2 A) :
    ∃ r : Matrix, ∃ hr : MatrixComputable r,
      Primrec (comparisonMap r hr) ∧
        ∀ x, (x ∈ A ↔ comparisonMap r hr x ∈ Noninclusion) ∧
          (x ∈ A ↔ comparisonMap r hr x ∈ Inequality) := by
  classical
  have hc : Pi ∅ 2 (Aᶜ : Set ℕ) := (level_complement ∅ 2 true A).mp hA
  obtain ⟨r, hr, hp, he⟩ := comparison_primitive_hardness Aᶜ hc
  refine ⟨r, hr, hp, fun x => ?_⟩
  constructor
  · simpa only [Noninclusion, Set.mem_compl_iff, not_not] using not_congr (he x).1
  · simpa only [Inequality, Set.mem_compl_iff, not_not] using not_congr (he x).2

theorem negative_completeness :
    PostsTheorem.SigmaComplete ∅ 2 Noninclusion ∧
      PostsTheorem.SigmaComplete ∅ 2 Inequality := by
  constructor
  · refine ⟨negative_sigma_two.1, fun A hA => ?_⟩
    obtain ⟨r, hr, hp, he⟩ := negative_primitive_hardness A hA
    exact ⟨comparisonMap r hr, hp.to_comp, fun x => (he x).1⟩
  · refine ⟨negative_sigma_two.2, fun A hA => ?_⟩
    obtain ⟨r, hr, hp, he⟩ := negative_primitive_hardness A hA
    exact ⟨comparisonMap r hr, hp.to_comp, fun x => (he x).2⟩

theorem exact_levels :
    ¬ Sigma ∅ 2 Inclusion ∧ ¬ Sigma ∅ 2 Equality ∧
      ¬ Pi ∅ 2 Noninclusion ∧ ¬ Pi ∅ 2 Inequality := by
  have hn (H : Set ℕ) (hH : PiComplete H) : ¬ Sigma ∅ 2 H := by
    intro hs
    apply (PostsTheorem.polarity_incomparable ∅ 2 (by decide)).2
    intro A hA
    exact manyOne_preimage ∅ 2 true A H (hH.2 A hA) hs
  exact ⟨hn Inclusion comparison_completeness.1, hn Equality comparison_completeness.2,
    (PostsTheorem.complete_boundaries ∅ 2 (by decide) Noninclusion negative_completeness.1).1,
    (PostsTheorem.complete_boundaries ∅ 2 (by decide) Inequality negative_completeness.2).1⟩

theorem first_level_exclusions (H : Set ℕ)
    (hH : H = Inclusion ∨ H = Equality ∨ H = Noninclusion ∨ H = Inequality) :
    (¬ REPred H) ∧ (¬ REPred (fun x => x ∉ H)) ∧ (¬ ComputablePred H) := by
  have hn : (¬ Sigma ∅ 2 H) ∨ (¬ Pi ∅ 2 H) := by
    rcases hH with rfl | rfl | rfl | rfl
    · exact Or.inl exact_levels.1
    · exact Or.inl exact_levels.2.1
    · exact Or.inr exact_levels.2.2.1
    · exact Or.inr exact_levels.2.2.2
  have hr : ¬ REPred H := by
    intro h
    have hs := (ordinary_sigma_one_iff_re H).mpr h
    rcases hn with hn | hn
    · exact hn (level_padding ∅ 1 true true H hs)
    · exact hn (level_padding ∅ 1 true false H hs)
  have hc : ¬ REPred (fun x => x ∉ H) := by
    intro h
    have hs := (ordinary_sigma_one_iff_re (fun x => x ∉ H)).mpr h
    have hp : Pi ∅ 1 H := (level_complement ∅ 1 false H).mpr hs
    rcases hn with hn | hn
    · exact hn (level_padding ∅ 1 false true H hp)
    · exact hn (level_padding ∅ 1 false false H hp)
  exact ⟨hr, hc, fun h => hr h.to_re⟩

end Lemmatheca.ComputabilityTheory.ComparingEnumerableSets
