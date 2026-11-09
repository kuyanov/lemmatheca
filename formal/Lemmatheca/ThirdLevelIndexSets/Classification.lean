import Lemmatheca.ThirdLevelIndexSets.Rows

/-! The actual third-level index sets, normal form and specified reduction family. -/
namespace Lemmatheca.ComputabilityTheory.ThirdLevelIndexSets
open EffectiveEnumerations ArithmeticalHierarchy UniversalComputation

def CofiniteIndices : Set ℕ := {e | ((indexSet e)ᶜ).Finite}
def Coinfinite (D : Set ℕ) : Prop := Dᶜ.Infinite

def CoinfiniteIndices : Set ℕ := {e | Coinfinite (indexSet e)}

theorem coinfinite_complement : CoinfiniteIndices = CofiniteIndicesᶜ := by
  rfl

def cofiniteMatrix (e a n s : ℕ) : Prop := n < a ∨ n ∈ stage e s

theorem cofinite_matrix_primitive :
    PrimrecPred (fun v : Tuple 4 => cofiniteMatrix (v 0) (v 1) (v 2) (v 3)) := by
  have hv (i : Fin 4) : Primrec (fun v : Tuple 4 => v i) :=
    Primrec.fin_app.comp Primrec.id (Primrec.const i)
  exact (Primrec.nat_lt.comp (hv 2) (hv 1)).or
    (EffectiveEnumerations.stage_predicate_primitive.comp (((hv 0).pair (hv 3)).pair (hv 2)))

theorem cofinite_normal_form (e : ℕ) :
    e ∈ CofiniteIndices ↔ ∃ a, ∀ n, ∃ s, cofiniteMatrix e a n s := by
  classical
  constructor
  · intro hf
    obtain ⟨a,ha⟩ := Set.Finite.bddAbove hf
    refine ⟨a+1,fun n => ?_⟩
    by_cases hn : n < a+1
    · exact ⟨0,Or.inl hn⟩
    · have hm : n ∈ indexSet e := by
        by_contra hnot
        have := ha hnot
        omega
      obtain ⟨s,hs⟩ := (stage_union e n).mp hm
      exact ⟨s,Or.inr hs⟩
  · rintro ⟨a,ha⟩
    apply (Set.finite_Iio a).subset
    intro n hn
    obtain ⟨s,hs⟩ := ha n
    rcases hs with hs | hs
    · exact hs
    · exact False.elim (hn ((stage_union e n).mpr ⟨s,hs⟩))

theorem cofinite_sigma_three : Sigma ∅ 3 CofiniteIndices := by
  apply (unary_finite_bridge ∅ 3 true _).mp
  apply (finite_matrix_normal_form ∅ 3 true _).mpr
  refine ⟨fun v => cofiniteMatrix (v 0) (v 1) (v 2) (v 3),
    (finite_decidable_empty_iff _).mpr cofinite_matrix_primitive.computablePred, ?_⟩
  intro x
  change (x 0 ∈ CofiniteIndices ↔ ∃ a, ∀ n, ∃ s, cofiniteMatrix (x 0) a n s)
  exact cofinite_normal_form (x 0)

theorem coinfinite_pi_three : Pi ∅ 3 CoinfiniteIndices := by
  rw [coinfinite_complement]
  exact (level_complement ∅ 3 true CofiniteIndices).mp cofinite_sigma_three

theorem cofinite_primitive_hardness (A : Set ℕ) (hA : Sigma ∅ 3 A) :
    ∃ g : ℕ → ℕ → ℕ, ∃ hg : Primrec₂ g,
      Primrec (rowIndex g hg) ∧ ∀ x, x ∈ A ↔ rowIndex g hg x ∈ CofiniteIndices := by
  obtain ⟨g,hg,he⟩ := uniform_infinite_rows A hA
  refine ⟨g,hg,index_primitive (rowSchedule g hg),fun x => ?_⟩
  change x ∈ A ↔ ((indexSet (index (rowSchedule g hg) x))ᶜ).Finite
  rw [index_domain, row_output_cofinite_iff]
  exact he x

theorem cofinite_complete : PostsTheorem.SigmaComplete ∅ 3 CofiniteIndices := by
  refine ⟨cofinite_sigma_three,fun A hA => ?_⟩
  obtain ⟨g,hg,hp,he⟩ := cofinite_primitive_hardness A hA
  exact ⟨rowIndex g hg,hp.to_comp,he⟩

theorem coinfinite_primitive_hardness (A : Set ℕ) (hA : Pi ∅ 3 A) :
    ∃ g : ℕ → ℕ → ℕ, ∃ hg : Primrec₂ g,
      Primrec (rowIndex g hg) ∧ ∀ x, x ∈ A ↔ rowIndex g hg x ∈ CoinfiniteIndices := by
  have hc : Sigma ∅ 3 (Aᶜ : Set ℕ) := (level_complement ∅ 3 false A).mp hA
  obtain ⟨g,hg,hp,he⟩ := cofinite_primitive_hardness Aᶜ hc
  refine ⟨g,hg,hp,fun x => ?_⟩
  rw [coinfinite_complement]
  simpa only [Set.mem_compl_iff, not_not] using not_congr (he x)

theorem coinfinite_complete : Pi ∅ 3 CoinfiniteIndices ∧
    ∀ A : Set ℕ, Pi ∅ 3 A → ManyOneReducible A CoinfiniteIndices := by
  refine ⟨coinfinite_pi_three,fun A hA => ?_⟩
  obtain ⟨g,hg,hp,he⟩ := coinfinite_primitive_hardness A hA
  exact ⟨rowIndex g hg,hp.to_comp,he⟩

end Lemmatheca.ComputabilityTheory.ThirdLevelIndexSets
