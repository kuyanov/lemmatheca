import Lemmatheca.IndependentPredicates.LanguageModels

/-! Native one-variable elimination and completeness of the independent-predicate theory. -/
namespace Lemmatheca.ModelTheory.IndependentPredicates

open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic.FirstOrderNormalForms

private theorem term_is_var {n : ℕ} (t : Lang.Term (Empty ⊕ Fin n)) :
    ∃ i : Fin n, t = .var (.inr i) := by
  cases t with
  | var x =>
    cases x with
    | inl x => exact x.elim
    | inr i => exact ⟨i, rfl⟩
  | func f _ => exact f.elim

private abbrev PatternAtom (S : Finset ℕ) (n : ℕ) :=
  (Fin n × Fin n) ⊕ (↥S × Fin n)

private def atomTruth {M : Type} [Lang.Structure M] {S : Finset ℕ} {n : ℕ}
    (a : Fin n → M) : PatternAtom S n → Prop
  | .inl (i, j) => a i = a j
  | .inr (k, i) => predicate k.val (a i)

private def atomFormula {S : Finset ℕ} {n : ℕ} :
    PatternAtom S n → Lang.BoundedFormula Empty n
  | .inl (i, j) => .equal (.var (.inr i)) (.var (.inr j))
  | .inr (k, i) => predicateFormula k.val (.var (.inr i))

private theorem atomFormula_qf {S : Finset ℕ} {n : ℕ} (z : PatternAtom S n) :
    (atomFormula z).IsQF := by
  cases z with
  | inl z => exact (BoundedFormula.IsAtomic.equal _ _).isQF
  | inr z => exact (BoundedFormula.IsAtomic.rel _ _).isQF

private theorem atomFormula_realize {M : Type} [Lang.Structure M]
    {S : Finset ℕ} {n : ℕ} (z : PatternAtom S n) (a : Fin n → M) :
    (atomFormula z).Realize Empty.elim a ↔ atomTruth a z := by
  cases z <;> rfl

private def SamePattern {M N : Type} [Lang.Structure M] [Lang.Structure N]
    (S : Finset ℕ) {n : ℕ} (a : Fin n → M) (b : Fin n → N) : Prop :=
  ∀ z : PatternAtom S n, atomTruth a z ↔ atomTruth b z

private theorem qf_agreement {M N : Type} [Lang.Structure M] [Lang.Structure N]
    {S : Finset ℕ} {n : ℕ} {a : Fin n → M} {b : Fin n → N}
    (hp : SamePattern S a b) {φ : Lang.BoundedFormula Empty n} (hφ : φ.IsQF)
    (hS : predicateSupport φ ⊆ S) :
    φ.Realize Empty.elim a ↔ φ.Realize Empty.elim b := by
  revert hS
  induction hφ with
  | falsum => intro _; exact Iff.rfl
  | of_isAtomic ha =>
    intro hS
    cases ha with
    | equal t s =>
      obtain ⟨i, rfl⟩ := term_is_var t
      obtain ⟨j, rfl⟩ := term_is_var s
      exact hp (.inl (i, j))
    | rel r ts =>
      cases r with
      | pred k =>
        obtain ⟨i, hi⟩ := term_is_var (ts 0)
        have ht : ts = fun _ => .var (.inr i) := by
          funext j
          exact (congrArg ts (Subsingleton.elim _ _)).trans hi
        subst ts
        change ({k} : Finset ℕ) ⊆ S at hS
        have hk : k ∈ S := hS (Finset.mem_singleton_self k)
        exact hp (.inr (⟨k, hk⟩, i))
  | imp _ _ ihφ ihψ =>
    intro hS
    exact imp_congr (ihφ (fun k hk => hS (Finset.mem_union_left _ hk)))
      (ihψ (fun k hk => hS (Finset.mem_union_right _ hk)))

private noncomputable def nativePattern {M : Type} [Lang.Structure M]
    (S : Finset ℕ) {n : ℕ} (a : Fin n → M) : PatternAtom S n → Bool := by
  classical
  exact fun z => decide (atomTruth a z)

private theorem pattern_eq_iff {M N : Type} [Lang.Structure M] [Lang.Structure N]
    {S : Finset ℕ} {n : ℕ} {a : Fin n → M} {b : Fin n → N} :
    nativePattern S a = nativePattern S b ↔ SamePattern S a b := by
  classical
  constructor
  · intro h z
    exact decide_eq_decide.mp (congrFun h z)
  · intro h
    funext z
    exact decide_eq_decide.mpr (h z)

private theorem snoc_pattern {M N : Type} [Lang.Structure M] [Lang.Structure N]
    {S : Finset ℕ} {n : ℕ} {a : Fin n → M} {b : Fin n → N} {x : M} {y : N}
    (hp : SamePattern S a b) (heq : ∀ i, x = a i ↔ y = b i)
    (hpred : ∀ k ∈ S, predicate k x ↔ predicate k y) :
    SamePattern S (Fin.snoc a x) (Fin.snoc b y) := by
  intro z
  cases z with
  | inl z =>
    rcases z with ⟨i, j⟩
    refine Fin.lastCases ?_ (fun i => ?_) i
    · refine Fin.lastCases ?_ (fun j => ?_) j
      · simp only [atomTruth, Fin.snoc_last]
      · simpa only [atomTruth, Fin.snoc_last, Fin.snoc_castSucc] using heq j
    · refine Fin.lastCases ?_ (fun j => ?_) j
      · simpa only [atomTruth, Fin.snoc_last, Fin.snoc_castSucc, eq_comm] using heq i
      · simpa only [atomTruth, Fin.snoc_castSucc] using hp (.inl (i, j))
  | inr z =>
    rcases z with ⟨k, i⟩
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simpa only [atomTruth, Fin.snoc_last] using hpred k.val k.property
    · simpa only [atomTruth, Fin.snoc_castSucc] using hp (.inr (k, i))

private theorem extend_pattern {M N : Type} [Lang.Structure M] [Lang.Structure N]
    [N ⊨ independentTheory] {S : Finset ℕ} {n : ℕ}
    {a : Fin n → M} {b : Fin n → N} (hp : SamePattern S a b) (x : M) :
    ∃ y : N, SamePattern S (Fin.snoc a x) (Fin.snoc b y) := by
  classical
  by_cases hx : ∃ i, x = a i
  · obtain ⟨i, rfl⟩ := hx
    refine ⟨b i, snoc_pattern hp (fun j => hp (.inl (i, j))) ?_⟩
    intro k hk
    exact hp (.inr (⟨k, hk⟩, i))
  · let F := S.filter fun k => predicate k x
    let G := S.filter fun k => ¬ predicate k x
    have hd : Disjoint F G := by
      apply Finset.disjoint_left.mpr
      intro k hkF hkG
      exact (Finset.mem_filter.mp hkG).2 (Finset.mem_filter.mp hkF).2
    obtain ⟨y, hy, hyfresh⟩ := fresh_cell_witness F G hd (Finset.univ.image b)
    refine ⟨y, snoc_pattern hp ?_ ?_⟩
    · intro i
      exact iff_of_false (fun h => hx ⟨i, h⟩)
        (fun h => hyfresh (h ▸ Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩))
    · intro k hk
      by_cases h : predicate k x
      · exact iff_of_true h (hy.1 k (Finset.mem_filter.mpr ⟨hk, h⟩))
      · exact iff_of_false h (hy.2 k (Finset.mem_filter.mpr ⟨hk, h⟩))

private noncomputable def patternRow (S : Finset ℕ) (n : ℕ)
    (p : PatternAtom S n → Bool) : List (Lang.BoundedFormula Empty n) :=
  Finset.univ.toList.map fun z => if p z then atomFormula z else (atomFormula z).not

private theorem patternRow_realize {M : Type} [Lang.Structure M]
    (S : Finset ℕ) (n : ℕ) (p : PatternAtom S n → Bool) (a : Fin n → M) :
    (QuantifierElimination.conjunction (patternRow S n p)).Realize Empty.elim a ↔
      nativePattern S a = p := by
  classical
  have hz (z : PatternAtom S n) :
      (if p z then atomFormula z else (atomFormula z).not).Realize Empty.elim a ↔
        nativePattern S a z = p z := by
    cases p z <;> simp [nativePattern, atomFormula_realize]
  rw [QuantifierElimination.conjunction, BoundedFormula.realize_foldr_inf]
  constructor
  · intro h
    funext z
    exact (hz z).mp (h _ (List.mem_map.mpr ⟨z,
      Finset.mem_toList.mpr (Finset.mem_univ _), rfl⟩))
  · intro h θ hθ
    obtain ⟨z, _, rfl⟩ := List.mem_map.mp hθ
    exact (hz z).mpr (congrFun h z)

private theorem conjunction_qf {n : ℕ} (row : List (Lang.BoundedFormula Empty n))
    (h : ∀ θ ∈ row, θ.IsQF) : (QuantifierElimination.conjunction row).IsQF := by
  induction row with
  | nil => exact BoundedFormula.IsQF.falsum.imp .falsum
  | cons θ row ih =>
    exact (h θ (List.mem_cons_self ..)).inf
      (ih (fun χ hχ => h χ (List.mem_cons_of_mem _ hχ)))

private theorem patternRow_qf (S : Finset ℕ) (n : ℕ) (p : PatternAtom S n → Bool) :
    (QuantifierElimination.conjunction (patternRow S n p)).IsQF := by
  classical
  apply conjunction_qf
  intro θ hθ
  obtain ⟨z, _, rfl⟩ := List.mem_map.mp hθ
  cases p z <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · exact (atomFormula_qf z).not
  · exact atomFormula_qf z

private theorem disjunction_qf {n : ℕ} (rows : List (List (Lang.BoundedFormula Empty n)))
    (h : ∀ row ∈ rows, (QuantifierElimination.conjunction row).IsQF) :
    (QuantifierElimination.disjunction rows).IsQF := by
  induction rows with
  | nil => exact .falsum
  | cons row rows ih =>
    exact (h row (List.mem_cons_self ..)).sup
      (ih (fun other ho => h other (List.mem_cons_of_mem _ ho)))

private theorem eliminate_qf (n : ℕ) (φ : Lang.BoundedFormula Empty (n + 1))
    (hφ : φ.IsQF) : ∃ ψ : Lang.BoundedFormula Empty n,
      ψ.IsQF ∧ independentTheory.Iff φ.ex ψ := by
  classical
  let S := predicateSupport φ
  let Good (p : PatternAtom S n → Bool) : Prop :=
    ∃ (M : independentTheory.ModelType.{0, 0, 0}) (a : Fin n → M) (x : M),
      nativePattern S a = p ∧ φ.Realize Empty.elim (Fin.snoc a x)
  let rows := (Finset.univ.filter Good).toList.map (patternRow S n)
  let ψ := QuantifierElimination.disjunction rows
  have hψ : ψ.IsQF := by
    apply disjunction_qf
    intro row hr
    obtain ⟨p, _, rfl⟩ := List.mem_map.mp hr
    exact patternRow_qf S n p
  have hψreal (M : independentTheory.ModelType.{0, 0, 0}) (a : Fin n → M) :
      ψ.Realize Empty.elim a ↔ ∃ p, Good p ∧ nativePattern S a = p := by
    simp only [ψ, rows, QuantifierElimination.disjunction,
      BoundedFormula.realize_foldr_sup, List.mem_map, Finset.mem_toList,
      Finset.mem_filter, Finset.mem_univ, true_and, exists_exists_and_eq_and,
      patternRow_realize]
  refine ⟨ψ, hψ, ?_⟩
  intro M v a
  have hv : v = Empty.elim := Subsingleton.elim _ _
  subst v
  rw [BoundedFormula.realize_iff, BoundedFormula.realize_ex, hψreal]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨nativePattern S a, ⟨M, a, x, rfl, hx⟩, rfl⟩
  · rintro ⟨p, ⟨N, b, x, hb, hx⟩, ha⟩
    have hp : SamePattern S b a := pattern_eq_iff.mp (hb.trans ha.symm)
    obtain ⟨y, hy⟩ := extend_pattern hp x
    exact ⟨y, (qf_agreement hy hφ (fun _ h => h)).mp hx⟩

theorem literal_conjunction_elimination (n : ℕ)
    (row : List (Lang.BoundedFormula Empty (n + 1))) (h : ∀ θ ∈ row, IsLiteral θ) :
    ∃ ψ : Lang.BoundedFormula Empty n, ψ.IsQF ∧
      independentTheory.Iff (QuantifierElimination.conjunction row).ex ψ := by
  apply eliminate_qf
  apply conjunction_qf
  intro θ hθ
  rcases h θ hθ with ha | ⟨χ, hχ, rfl⟩
  · exact ha.isQF
  · exact hχ.isQF.not

theorem hasQuantifierElimination :
    QuantifierElimination.HasQuantifierElimination independentTheory := by
  exact QuantifierElimination.qe_of_literal_conjunctions independentTheory
    literal_conjunction_elimination

theorem independentTheory_complete : independentTheory.IsComplete := by
  apply (Theory.IsComplete.isComplete_iff_models_elementarily_equivalent
    (T := independentTheory)).mpr
  let : Finset ℕ ⊨ independentTheory := finiteSubset_model
  refine ⟨Theory.Model.isSatisfiable (Finset ℕ), fun M N => ?_⟩
  apply elementarilyEquivalent_iff.mpr
  intro σ
  obtain ⟨ψ, hψ, he⟩ := hasQuantifierElimination 0 σ
  have hp : SamePattern (predicateSupport ψ) (Fin.elim0 : Fin 0 → M)
      (Fin.elim0 : Fin 0 → N) := by
    rintro (⟨i, _⟩ | ⟨_, i⟩) <;> exact Fin.elim0 i
  have h := qf_agreement hp hψ (fun _ h => h)
  have h' : (M ⊨ ψ) ↔ (N ⊨ ψ) := by
    simpa only [Sentence.Realize, Formula.Realize, Unique.eq_default] using h
  exact (he.models_sentence_iff (M := M)).trans
    (h'.trans (he.models_sentence_iff (M := N)).symm)

end Lemmatheca.ModelTheory.IndependentPredicates
