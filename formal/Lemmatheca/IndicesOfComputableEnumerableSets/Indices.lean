import Lemmatheca.ThirdLevelIndexSets.Classification
import Lemmatheca.SimpleSets.Immunity

/-! The actual computable-domain index property and its complement-index normal form. -/
namespace Lemmatheca.ComputabilityTheory.ComputableDomainIndices
open EffectiveEnumerations ArithmeticalHierarchy

noncomputable def ComputableIndices : Set ℕ := {e | ComputablePred (indexSet e)}

noncomputable def NoncomputableIndices : Set ℕ := ComputableIndicesᶜ

theorem complement_index_certificate (e : ℕ) :
    e ∈ ComputableIndices ↔ ∃ d,
      indexSet e ∩ indexSet d = ∅ ∧ indexSet e ∪ indexSet d = Set.univ := by
  classical
  constructor
  · intro he
    obtain ⟨d,hd⟩ := (UniversalComputation.enumerable_iff_index (fun x => x ∉ indexSet e)).mp
      he.not.to_re
    refine ⟨d, ?_, ?_⟩
    · ext x
      simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
      exact fun hx => ((hd x).mpr hx.2) hx.1
    · ext x
      simp only [Set.mem_union, Set.mem_univ, iff_true]
      by_cases hx : x ∈ indexSet e
      · exact Or.inl hx
      · exact Or.inr ((hd x).mp hx)
  · rintro ⟨d,hdisj,hcover⟩
    apply ComputablePred.computable_iff_re_compl_re'.mpr
    have hre (j : ℕ) : REPred (indexSet j) :=
      (UniversalComputation.enumerable_iff_index (indexSet j)).mpr ⟨j,fun _ => Iff.rfl⟩
    refine ⟨hre e, (hre d).of_eq fun x => ?_⟩
    constructor
    · intro hx he
      have : x ∈ indexSet e ∩ indexSet d := ⟨he,hx⟩
      simp [hdisj] at this
    · intro hx
      have : x ∈ indexSet e ∪ indexSet d := by rw [hcover]; trivial
      exact this.resolve_left hx

def complementMatrix (e d x s t : ℕ) : Prop :=
  (x ∈ stage e t ∨ x ∈ stage d t) ∧ ¬(x ∈ stage e s ∧ x ∈ stage d s)

theorem complement_matrix_primitive :
    PrimrecPred (fun v : Tuple 5 =>
      complementMatrix (v 0) (v 1) (v 2) (v 3) (v 4)) := by
  have hv (i : Fin 5) : Primrec (fun v : Tuple 5 => v i) :=
    Primrec.fin_app.comp Primrec.id (Primrec.const i)
  have hm (i j : Fin 5) : PrimrecPred (fun v : Tuple 5 => v 2 ∈ stage (v i) (v j)) :=
    stage_predicate_primitive.comp (((hv i).pair (hv j)).pair (hv 2))
  exact ((hm 0 4).or (hm 1 4)).and ((hm 0 3).and (hm 1 3)).not

theorem computable_normal_form (e : ℕ) :
    e ∈ ComputableIndices ↔ ∃ d, ∀ x s, ∃ t, complementMatrix e d x s t := by
  rw [complement_index_certificate]
  constructor
  · rintro ⟨d,hdisj,hcover⟩
    refine ⟨d,fun x s => ?_⟩
    have hn : ¬(x ∈ stage e s ∧ x ∈ stage d s) := by
      rintro ⟨he,hd⟩
      have : x ∈ indexSet e ∩ indexSet d :=
        ⟨(stage_union e x).mpr ⟨s,he⟩,(stage_union d x).mpr ⟨s,hd⟩⟩
      simp [hdisj] at this
    have hx : x ∈ indexSet e ∪ indexSet d := by rw [hcover]; trivial
    rcases hx with he | hd
    · obtain ⟨t,ht⟩ := (stage_union e x).mp he
      exact ⟨t,Or.inl ht,hn⟩
    · obtain ⟨t,ht⟩ := (stage_union d x).mp hd
      exact ⟨t,Or.inr ht,hn⟩
  · rintro ⟨d,hd⟩
    refine ⟨d, ?_, ?_⟩
    · ext x
      simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
      rintro ⟨he,hde⟩
      obtain ⟨s,hs⟩ := (stage_union e x).mp he
      obtain ⟨u,hu⟩ := (stage_union d x).mp hde
      obtain ⟨t,_,ht⟩ := hd x (max s u)
      exact ht ⟨stage_monotone e (le_max_left s u) hs,
        stage_monotone d (le_max_right s u) hu⟩
    · ext x
      simp only [Set.mem_union, Set.mem_univ, iff_true]
      obtain ⟨t,ht,_⟩ := hd x 0
      exact ht.imp (fun h => (stage_union e x).mpr ⟨t,h⟩)
        (fun h => (stage_union d x).mpr ⟨t,h⟩)

theorem computable_sigma_three : Sigma ∅ 3 ComputableIndices := by
  have hv (i : Fin 4) : Primrec (fun v : Tuple 4 => v i) :=
    Primrec.fin_app.comp Primrec.id (Primrec.const i)
  let R : Tuple 4 → Prop := fun v =>
    complementMatrix (v 0) (v 1) (v 2).unpair.1 (v 2).unpair.2 (v 3)
  have hf : Primrec (fun v : Tuple 4 =>
      (![v 0, v 1, (v 2).unpair.1, (v 2).unpair.2, v 3] : Tuple 5)) := by
    have he : ∀ i : Fin 5, Primrec (fun v : Tuple 4 =>
        (![v 0, v 1, (v 2).unpair.1, (v 2).unpair.2, v 3] : Tuple 5) i) := by
      intro i
      fin_cases i
      · exact hv 0
      · exact hv 1
      · exact Primrec.fst.comp (Primrec.unpair.comp (hv 2))
      · exact Primrec.snd.comp (Primrec.unpair.comp (hv 2))
      · exact hv 3
    exact Primrec.fin_curry.mpr (Primrec.fin_curry₁.mpr he).swap
  have hm : PrimrecPred R := complement_matrix_primitive.comp hf
  apply (unary_finite_bridge ∅ 3 true _).mp
  apply (finite_matrix_normal_form ∅ 3 true _).mpr
  refine ⟨R,(finite_decidable_empty_iff _).mpr hm.computablePred, ?_⟩
  intro x
  change (x 0 ∈ ComputableIndices ↔ ∃ d, ∀ p : ℕ, ∃ t,
    complementMatrix (x 0) d p.unpair.1 p.unpair.2 t)
  rw [computable_normal_form]
  constructor
  · rintro ⟨d,hd⟩
    exact ⟨d,fun p => hd p.unpair.1 p.unpair.2⟩
  · rintro ⟨d,hd⟩
    exact ⟨d,fun a s => by simpa only [Nat.unpair_pair] using hd (Nat.pair a s)⟩

theorem noncomputable_pi_three : Pi ∅ 3 NoncomputableIndices := by
  exact (level_complement ∅ 3 true ComputableIndices).mp computable_sigma_three

theorem cofinite_subset_computable :
    ThirdLevelIndexSets.CofiniteIndices ⊆ ComputableIndices := by
  intro e he
  have hc : ComputablePred (fun x => x ∉ (indexSet e)ᶜ) :=
    (SimpleSets.finite_decidable he).not
  exact hc.of_eq (fun x => not_not)

end Lemmatheca.ComputabilityTheory.ComputableDomainIndices
