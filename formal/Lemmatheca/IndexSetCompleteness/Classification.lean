import Lemmatheca.IndexSetCompleteness.Searches
import Lemmatheca.PostsTheorem.Hierarchy

/-! Exact classifications in the established computable-matrix hierarchy. -/
namespace Lemmatheca.ComputabilityTheory.IndexSetCompleteness

open ArithmeticalHierarchy

local notation "TOT" => Lemmatheca.Entry.ArithmeticalHierarchy.Totality
local notation "FIN" => Lemmatheca.Entry.ArithmeticalHierarchy.Finiteness

def Infinitude : Set ℕ := {e | (EffectiveEnumerations.indexSet e).Infinite}

noncomputable def PiComplete (H : Set ℕ) : Prop :=
  Pi ∅ 2 H ∧ ∀ A : Set ℕ, Pi ∅ 2 A → ManyOneReducible A H

theorem infinitude_complement : Infinitude = FINᶜ := by
  ext e
  rfl

theorem totality_subset_infinitude : TOT ⊆ Infinitude := by
  intro e he
  have hd : EffectiveEnumerations.indexSet e = Set.univ :=
    Set.eq_univ_of_forall he
  change (EffectiveEnumerations.indexSet e).Infinite
  rw [hd]
  exact Set.infinite_univ

theorem infinitude_pi_two : Pi ∅ 2 Infinitude := by
  rw [infinitude_complement]
  exact (level_complement ∅ 2 true FIN).mp
    Lemmatheca.Entry.ArithmeticalHierarchy.finiteness_sigma_two

private theorem triple_primitive :
    Primrec (fun p : (ℕ × ℕ) × ℕ => (![p.1.1,p.1.2,p.2] : Tuple 3)) := by
  apply Primrec.fin_curry.mpr
  apply Primrec₂.swap
  apply Primrec.fin_curry₁.mpr
  intro i
  fin_cases i
  · exact Primrec.fst.comp Primrec.fst
  · exact Primrec.snd.comp Primrec.fst
  · exact Primrec.snd

theorem pi_two_matrix (A : Set ℕ) (hA : Pi ∅ 2 A) :
    ∃ r : Matrix, MatrixComputable r ∧ ∀ x, x ∈ A ↔ ∀ y, ∃ z, r x y z = true := by
  obtain ⟨R,hR,he⟩ := (finite_matrix_normal_form ∅ 2 false
    (fun v : Tuple 1 => v 0 ∈ A)).mp ((unary_finite_bridge ∅ 2 false A).mpr hA)
  obtain ⟨b,hb,hRb⟩ := ComputablePred.computable_iff.mp ((finite_decidable_empty_iff R).mp hR)
  let r : Matrix := fun x y z => b ![x,y,z]
  have hr : MatrixComputable r := hb.comp triple_primitive.to_comp
  refine ⟨r,hr,fun x => ?_⟩
  have hx := he (fun _ => x)
  change (x ∈ A ↔ ∀ y, ∃ z, R (appendTuple (fun _ : Fin 1 => x) (Fin.cons y (Fin.cons z Fin.elim0)))) at hx
  have ht (y z : ℕ) :
      R (appendTuple (fun _ : Fin 1 => x) (Fin.cons y (Fin.cons z Fin.elim0))) ↔
        r x y z = true := by
    rw [hRb]
    have hv : appendTuple (fun _ : Fin 1 => x) (Fin.cons y (Fin.cons z Fin.elim0)) =
        (![x,y,z] : Tuple 3) := by
      ext i
      fin_cases i <;> rfl
    rw [hv]
  exact hx.trans (forall_congr' (fun y => exists_congr (fun z => ht y z)))

theorem sigma_two_matrix (A : Set ℕ) (hA : Sigma ∅ 2 A) :
    ∃ r : Matrix, MatrixComputable r ∧ ∀ x, x ∈ A ↔ ∃ y, Permanent r x y := by
  obtain ⟨R,hR,he⟩ := (finite_matrix_normal_form ∅ 2 true
    (fun v : Tuple 1 => v 0 ∈ A)).mp ((unary_finite_bridge ∅ 2 true A).mpr hA)
  obtain ⟨b,hb,hRb⟩ := ComputablePred.computable_iff.mp ((finite_decidable_empty_iff R).mp hR)
  let r : Matrix := fun x y z => b ![x,y,z]
  have hr : MatrixComputable r := hb.comp triple_primitive.to_comp
  refine ⟨r,hr,fun x => ?_⟩
  have hx := he (fun _ => x)
  change (x ∈ A ↔ ∃ y, ∀ z, R (appendTuple (fun _ : Fin 1 => x) (Fin.cons y (Fin.cons z Fin.elim0)))) at hx
  have ht (y z : ℕ) :
      R (appendTuple (fun _ : Fin 1 => x) (Fin.cons y (Fin.cons z Fin.elim0))) ↔
        r x y z = true := by
    rw [hRb]
    have hv : appendTuple (fun _ : Fin 1 => x) (Fin.cons y (Fin.cons z Fin.elim0)) =
        (![x,y,z] : Tuple 3) := by
      ext i
      fin_cases i <;> rfl
    rw [hv]
  exact hx.trans (exists_congr (fun y => forall_congr' (fun z => ht y z)))

theorem totality_primitive_hardness (A : Set ℕ) (hA : Pi ∅ 2 A) :
    ∃ r : Matrix, ∃ hr : MatrixComputable r,
      Primrec (totalMap r hr) ∧ ∀ x, x ∈ A ↔ totalMap r hr x ∈ TOT := by
  obtain ⟨r,hr,he⟩ := pi_two_matrix A hA
  exact ⟨r,hr,totalMap_primitive r hr,fun x => (he x).trans (totalMap_correct r hr x).symm⟩

theorem finiteness_primitive_hardness (A : Set ℕ) (hA : Sigma ∅ 2 A) :
    ∃ r : Matrix, ∃ hr : MatrixComputable r,
      Primrec (finiteMap r hr) ∧ ∀ x, x ∈ A ↔ finiteMap r hr x ∈ FIN := by
  obtain ⟨r,hr,he⟩ := sigma_two_matrix A hA
  exact ⟨r,hr,finiteMap_primitive r hr,fun x => (he x).trans (finiteMap_correct r hr x).symm⟩

theorem infinitude_primitive_hardness (A : Set ℕ) (hA : Pi ∅ 2 A) :
    ∃ r : Matrix, ∃ hr : MatrixComputable r,
      Primrec (finiteMap r hr) ∧ ∀ x, x ∈ A ↔ finiteMap r hr x ∈ Infinitude := by
  classical
  have hc : Sigma ∅ 2 (Aᶜ : Set ℕ) := (level_complement ∅ 2 false A).mp hA
  obtain ⟨r,hr,hp,he⟩ := finiteness_primitive_hardness Aᶜ hc
  refine ⟨r,hr,hp,fun x => ?_⟩
  rw [infinitude_complement]
  simpa only [Set.mem_compl_iff, not_not] using not_congr (he x)

theorem totality_complete : PiComplete TOT := by
  refine ⟨Lemmatheca.Entry.ArithmeticalHierarchy.totality_pi_two,fun A hA => ?_⟩
  obtain ⟨r,hr,hp,he⟩ := totality_primitive_hardness A hA
  exact ⟨totalMap r hr,hp.to_comp,he⟩

theorem finiteness_complete : PostsTheorem.SigmaComplete ∅ 2 FIN := by
  refine ⟨Lemmatheca.Entry.ArithmeticalHierarchy.finiteness_sigma_two,fun A hA => ?_⟩
  obtain ⟨r,hr,hp,he⟩ := finiteness_primitive_hardness A hA
  exact ⟨finiteMap r hr,hp.to_comp,he⟩

theorem infinitude_complete : PiComplete Infinitude := by
  refine ⟨infinitude_pi_two,fun A hA => ?_⟩
  obtain ⟨r,hr,hp,he⟩ := infinitude_primitive_hardness A hA
  exact ⟨finiteMap r hr,hp.to_comp,he⟩

theorem totality_not_sigma_two : ¬ Sigma ∅ 2 TOT := by
  intro h
  apply (PostsTheorem.polarity_incomparable ∅ 2 (by decide)).2
  intro A hA
  exact manyOne_preimage ∅ 2 true A TOT (totality_complete.2 A hA) h

theorem finiteness_not_pi_two : ¬ Pi ∅ 2 FIN := by
  exact (PostsTheorem.complete_boundaries ∅ 2 (by decide) FIN finiteness_complete).1

theorem infinitude_not_sigma_two : ¬ Sigma ∅ 2 Infinitude := by
  intro h
  apply (PostsTheorem.polarity_incomparable ∅ 2 (by decide)).2
  intro A hA
  exact manyOne_preimage ∅ 2 true A Infinitude (infinitude_complete.2 A hA) h

private theorem not_first_levels (H : Set ℕ)
    (hn : (¬ Sigma ∅ 2 H) ∨ (¬ Pi ∅ 2 H)) :
    (¬ REPred H) ∧ (¬ REPred (fun x => x ∉ H)) := by
  constructor
  · intro h
    have hs := (ordinary_sigma_one_iff_re H).mpr h
    rcases hn with hn | hn
    · exact hn (level_padding ∅ 1 true true H hs)
    · exact hn (level_padding ∅ 1 true false H hs)
  · intro h
    have hs := (ordinary_sigma_one_iff_re (fun x => x ∉ H)).mpr h
    have hp : Pi ∅ 1 H := (level_complement ∅ 1 false H).mpr hs
    rcases hn with hn | hn
    · exact hn (level_padding ∅ 1 false true H hp)
    · exact hn (level_padding ∅ 1 false false H hp)

theorem totality_not_re : ¬ REPred TOT := by
  exact (not_first_levels TOT (Or.inl totality_not_sigma_two)).1

theorem totality_not_co_re : ¬ REPred (fun e => e ∉ TOT) := by
  exact (not_first_levels TOT (Or.inl totality_not_sigma_two)).2

theorem finiteness_not_re : ¬ REPred FIN := by
  exact (not_first_levels FIN (Or.inr finiteness_not_pi_two)).1

theorem finiteness_not_co_re : ¬ REPred (fun e => e ∉ FIN) := by
  exact (not_first_levels FIN (Or.inr finiteness_not_pi_two)).2

theorem infinitude_not_re : ¬ REPred Infinitude := by
  exact (not_first_levels Infinitude (Or.inl infinitude_not_sigma_two)).1

theorem infinitude_not_co_re : ¬ REPred (fun e => e ∉ Infinitude) := by
  exact (not_first_levels Infinitude (Or.inl infinitude_not_sigma_two)).2

theorem totality_undecidable : ¬ ComputablePred TOT := by
  intro h
  exact totality_not_re h.to_re

theorem finiteness_undecidable : ¬ ComputablePred FIN := by
  intro h
  exact finiteness_not_re h.to_re

theorem infinitude_undecidable : ¬ ComputablePred Infinitude := by
  intro h
  exact infinitude_not_re h.to_re

theorem totality_equiv_infinitude : ManyOneEquiv TOT Infinitude := by
  exact ⟨infinitude_complete.2 TOT totality_complete.1,
    totality_complete.2 Infinitude infinitude_complete.1⟩

theorem totality_not_reduce_finiteness : ¬ ManyOneReducible TOT FIN := by
  intro h
  exact totality_not_sigma_two
    (manyOne_preimage ∅ 2 true TOT FIN h Lemmatheca.Entry.ArithmeticalHierarchy.finiteness_sigma_two)

theorem finiteness_not_reduce_totality : ¬ ManyOneReducible FIN TOT := by
  intro h
  exact finiteness_not_pi_two
    (manyOne_preimage ∅ 2 false FIN TOT h Lemmatheca.Entry.ArithmeticalHierarchy.totality_pi_two)

theorem infinitude_not_reduce_finiteness : ¬ ManyOneReducible Infinitude FIN := by
  intro h
  exact infinitude_not_sigma_two
    (manyOne_preimage ∅ 2 true Infinitude FIN h Lemmatheca.Entry.ArithmeticalHierarchy.finiteness_sigma_two)

theorem finiteness_not_reduce_infinitude : ¬ ManyOneReducible FIN Infinitude := by
  intro h
  exact finiteness_not_pi_two (manyOne_preimage ∅ 2 false FIN Infinitude h infinitude_pi_two)

end Lemmatheca.ComputabilityTheory.IndexSetCompleteness
