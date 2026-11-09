import Lemmatheca.EffectiveEnumerations.Stages
import Lemmatheca.ArithmeticalHierarchy.Arithmetic

/-! Coded comparisons of the domains in the fixed ordinary numbering. -/
namespace Lemmatheca.ComputabilityTheory.ComparingEnumerableSets

open EffectiveEnumerations ArithmeticalHierarchy


private theorem primrec_tuple {α : Type} [Primcodable α] {k : ℕ} {f : α → Tuple k}
    (hf : ∀ i, Primrec (fun x => f x i)) : Primrec f := by
  exact Primrec.fin_curry.mpr (Primrec.fin_curry₁.mpr hf).swap

private theorem pi_two_of_test (P : Set ℕ) (R : ℕ → ℕ → ℕ → Prop)
    (hR : PrimrecPred (fun v : Tuple 3 => R (v 0) (v 1) (v 2)))
    (he : ∀ w, w ∈ P ↔ ∀ a, ∃ t, R w a t) : Pi ∅ 2 P := by
  apply (unary_finite_bridge ∅ 2 false _).mp
  apply (finite_matrix_normal_form ∅ 2 false _).mpr
  refine ⟨fun v => R (v 0) (v 1) (v 2),
    (finite_decidable_empty_iff _).mpr hR.computablePred, ?_⟩
  intro x
  have hx := he (x 0)
  change P (x 0) ↔ _ at hx
  simpa [quantify, appendTuple, Fin.append, Fin.addCases] using hx

def Inclusion : Set ℕ :=
  {w | indexSet w.unpair.1 ⊆ indexSet w.unpair.2}

def Equality : Set ℕ :=
  {w | indexSet w.unpair.1 = indexSet w.unpair.2}

theorem coded_comparisons (d e : ℕ) :
    (Nat.pair d e ∈ Inclusion ↔ indexSet d ⊆ indexSet e) ∧
      (Nat.pair d e ∈ Equality ↔ indexSet d = indexSet e) := by
  simp [Inclusion, Equality]

def inclusionTest (d e x s t : ℕ) : Prop :=
  s ≤ t ∧ (x ∉ stage d s ∨ x ∈ stage e t)

theorem inclusion_test_primitive :
    PrimrecPred (fun v : Tuple 5 => inclusionTest (v 0) (v 1) (v 2) (v 3) (v 4)) := by
  have c (i : Fin 5) : Primrec (fun v : Tuple 5 => v i) :=
    Primrec.fin_app.comp Primrec.id (Primrec.const i)
  have hd : PrimrecPred (fun v : Tuple 5 => v 2 ∈ stage (v 0) (v 3)) :=
    stage_predicate_primitive.comp (((c 0).pair (c 3)).pair (c 2))
  have he : PrimrecPred (fun v : Tuple 5 => v 2 ∈ stage (v 1) (v 4)) :=
    stage_predicate_primitive.comp (((c 1).pair (c 4)).pair (c 2))
  exact (Primrec.nat_le.comp (c 3) (c 4)).and (hd.not.or he)


private theorem inclusion_test_later {d e x s t u : ℕ}
    (h : inclusionTest d e x s t) (htu : t ≤ u) : inclusionTest d e x s u := by
  refine ⟨h.1.trans htu, ?_⟩
  exact h.2.imp_right (fun hx => stage_monotone e htu hx)

theorem inclusion_normal_form (d e : ℕ) :
    indexSet d ⊆ indexSet e ↔ ∀ x s, ∃ t, inclusionTest d e x s t := by
  classical
  constructor
  · intro h x s
    by_cases hx : x ∈ stage d s
    · obtain ⟨v, hv⟩ := (stage_union e x).mp (h ((stage_union d x).mpr ⟨s, hx⟩))
      exact ⟨max s v, le_max_left _ _, Or.inr (stage_monotone e (le_max_right _ _) hv)⟩
    · exact ⟨s, le_rfl, Or.inl hx⟩
  · intro h x hx
    obtain ⟨s, hs⟩ := (stage_union d x).mp hx
    obtain ⟨t, _, ht⟩ := h x s
    exact (stage_union e x).mpr ⟨t, ht.resolve_left (not_not.mpr hs)⟩

theorem inclusion_pi_two : Pi ∅ 2 Inclusion := by
  let R : ℕ → ℕ → ℕ → Prop := fun w a t =>
    inclusionTest w.unpair.1 w.unpair.2 a.unpair.1 a.unpair.2 t
  have c (i : Fin 3) : Primrec (fun v : Tuple 3 => v i) :=
    Primrec.fin_app.comp Primrec.id (Primrec.const i)
  have hf : Primrec (fun v : Tuple 3 =>
      (![ (v 0).unpair.1, (v 0).unpair.2, (v 1).unpair.1,
        (v 1).unpair.2, v 2] : Tuple 5)) := by
    apply primrec_tuple
    intro i
    fin_cases i
    · exact Primrec.fst.comp (Primrec.unpair.comp (c 0))
    · exact Primrec.snd.comp (Primrec.unpair.comp (c 0))
    · exact Primrec.fst.comp (Primrec.unpair.comp (c 1))
    · exact Primrec.snd.comp (Primrec.unpair.comp (c 1))
    · exact c 2
  apply pi_two_of_test Inclusion R (inclusion_test_primitive.comp hf)
  intro w
  change indexSet w.unpair.1 ⊆ indexSet w.unpair.2 ↔ _
  rw [inclusion_normal_form]
  constructor
  · intro h a
    exact h a.unpair.1 a.unpair.2
  · intro h x s
    simpa [R] using h (Nat.pair x s)

theorem equality_normal_form (d e : ℕ) :
    indexSet d = indexSet e ↔
      ∀ x s, ∃ t, inclusionTest d e x s t ∧ inclusionTest e d x s t := by
  constructor
  · intro he x s
    have hd : indexSet d ⊆ indexSet e := fun x hx => he ▸ hx
    have hr : indexSet e ⊆ indexSet d := fun x hx => he.symm ▸ hx
    obtain ⟨t₀, h₀⟩ := (inclusion_normal_form d e).mp hd x s
    obtain ⟨t₁, h₁⟩ := (inclusion_normal_form e d).mp hr x s
    exact ⟨max t₀ t₁, inclusion_test_later h₀ (le_max_left _ _),
      inclusion_test_later h₁ (le_max_right _ _)⟩
  · intro h
    apply Set.Subset.antisymm
    · exact (inclusion_normal_form d e).mpr (fun x s => by
        obtain ⟨t, ht, _⟩ := h x s
        exact ⟨t, ht⟩)
    · exact (inclusion_normal_form e d).mpr (fun x s => by
        obtain ⟨t, _, ht⟩ := h x s
        exact ⟨t, ht⟩)

theorem equality_pi_two : Pi ∅ 2 Equality := by
  let R : ℕ → ℕ → ℕ → Prop := fun w a t =>
    inclusionTest w.unpair.1 w.unpair.2 a.unpair.1 a.unpair.2 t ∧
      inclusionTest w.unpair.2 w.unpair.1 a.unpair.1 a.unpair.2 t
  have c (i : Fin 3) : Primrec (fun v : Tuple 3 => v i) :=
    Primrec.fin_app.comp Primrec.id (Primrec.const i)
  have hf (flip : Bool) : Primrec (fun v : Tuple 3 =>
      (![if flip then (v 0).unpair.2 else (v 0).unpair.1,
        if flip then (v 0).unpair.1 else (v 0).unpair.2,
        (v 1).unpair.1, (v 1).unpair.2, v 2] : Tuple 5)) := by
    cases flip <;> simp only [Bool.false_eq_true, ite_false, ite_true]
    all_goals
      apply primrec_tuple
      intro i
      fin_cases i
    · exact Primrec.fst.comp (Primrec.unpair.comp (c 0))
    · exact Primrec.snd.comp (Primrec.unpair.comp (c 0))
    · exact Primrec.fst.comp (Primrec.unpair.comp (c 1))
    · exact Primrec.snd.comp (Primrec.unpair.comp (c 1))
    · exact c 2
    · exact Primrec.snd.comp (Primrec.unpair.comp (c 0))
    · exact Primrec.fst.comp (Primrec.unpair.comp (c 0))
    · exact Primrec.fst.comp (Primrec.unpair.comp (c 1))
    · exact Primrec.snd.comp (Primrec.unpair.comp (c 1))
    · exact c 2
  have hR : PrimrecPred (fun v : Tuple 3 => R (v 0) (v 1) (v 2)) :=
    (inclusion_test_primitive.comp (hf false)).and (inclusion_test_primitive.comp (hf true))
  apply pi_two_of_test Equality R hR
  intro w
  change indexSet w.unpair.1 = indexSet w.unpair.2 ↔ _
  rw [equality_normal_form]
  constructor
  · intro h a
    exact h a.unpair.1 a.unpair.2
  · intro h x s
    simpa [R] using h (Nat.pair x s)

def Noninclusion : Set ℕ := Inclusionᶜ

def Inequality : Set ℕ := Equalityᶜ

theorem negative_domain_witnesses (d e : ℕ) :
    (Nat.pair d e ∈ Noninclusion ↔ ∃ x, x ∈ indexSet d ∧ x ∉ indexSet e) ∧
      (Nat.pair d e ∈ Inequality ↔
        (∃ x, x ∈ indexSet d ∧ x ∉ indexSet e) ∨
        (∃ x, x ∈ indexSet e ∧ x ∉ indexSet d)) := by
  classical
  have hn (D E : Set ℕ) : ¬ D ⊆ E ↔ ∃ x, x ∈ D ∧ x ∉ E := by
    simp only [Set.subset_def, not_forall, exists_prop]
  simp only [Noninclusion, Inequality, Set.mem_compl_iff]
  rw [(coded_comparisons d e).1, (coded_comparisons d e).2]
  refine ⟨hn _ _, ?_⟩
  constructor
  · intro h
    by_cases hde : indexSet d ⊆ indexSet e
    · right
      apply (hn _ _).mp
      exact fun hed => h (Set.Subset.antisymm hde hed)
    · exact Or.inl ((hn _ _).mp hde)
  · rintro (⟨x, hd, he⟩ | ⟨x, he, hd⟩) h
    · exact he (h ▸ hd)
    · exact hd (h.symm ▸ he)

theorem noninclusion_normal_form (d e : ℕ) :
    Nat.pair d e ∈ Noninclusion ↔
      ∃ x s, ∀ t, x ∈ stage d s ∧ x ∉ stage e t := by
  rw [(negative_domain_witnesses d e).1]
  constructor
  · rintro ⟨x, hd, he⟩
    obtain ⟨s, hs⟩ := (stage_union d x).mp hd
    exact ⟨x, s, fun t => ⟨hs, fun ht => he ((stage_union e x).mpr ⟨t, ht⟩)⟩⟩
  · rintro ⟨x, s, h⟩
    refine ⟨x, (stage_union d x).mpr ⟨s, (h 0).1⟩, ?_⟩
    intro he
    obtain ⟨t, ht⟩ := (stage_union e x).mp he
    exact (h t).2 ht

theorem noninclusion_matrix_primitive :
    PrimrecPred (fun v : Tuple 5 =>
      v 2 ∈ stage (v 0) (v 3) ∧ v 2 ∉ stage (v 1) (v 4)) := by
  have c (i : Fin 5) : Primrec (fun v : Tuple 5 => v i) :=
    Primrec.fin_app.comp Primrec.id (Primrec.const i)
  exact (stage_predicate_primitive.comp (((c 0).pair (c 3)).pair (c 2))).and
    (stage_predicate_primitive.comp (((c 1).pair (c 4)).pair (c 2))).not

theorem negative_sigma_two : Sigma ∅ 2 Noninclusion ∧ Sigma ∅ 2 Inequality := by
  exact ⟨(level_complement ∅ 2 false Inclusion).mp inclusion_pi_two,
    (level_complement ∅ 2 false Equality).mp equality_pi_two⟩

end Lemmatheca.ComputabilityTheory.ComparingEnumerableSets
