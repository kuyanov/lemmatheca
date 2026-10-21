import Lemmatheca.GroundEquality.Models
import Mathlib.ModelTheory.Complexity

/-! Finite signed ground literals and the specified relation extension of the finite
congruence model. All atoms use the shared first-order terms. -/

namespace Lemmatheca.MathematicalLogic.QuantifierFreeValidity

open FirstOrder FirstOrder.Language

universe u v w
variable {L : Language.{u, v}}

/-- Actual shared ground equality or relation data. -/
inductive Atom (L : Language.{u, v})
  | equal (left right : GroundEquality.GroundTerm L)
  | rel {arity : ℕ} (symbol : L.Relations arity) (arguments : Fin arity → GroundEquality.GroundTerm L)

abbrev Literal (L : Language.{u, v}) := Bool × Atom L
abbrev Problem (L : Language.{u, v}) := Finset (Literal L)

/-- Embed the atom into the actual shared sentence syntax. -/
def Atom.formula : Atom L → L.Sentence
  | .equal t s => .equal (t.relabel Sum.inl) (s.relabel Sum.inl)
  | .rel R ts => .rel R (fun i => (ts i).relabel Sum.inl)

/-- Select the atom or its actual first-order negation. -/
def literalFormula (l : Literal L) : L.Sentence :=
  if l.1 then l.2.formula else l.2.formula.not

def Atom.Realize (a : Atom L) (M : Type w) [L.Structure M] : Prop :=
  a.formula.Realize M

def Satisfies (Γ : Problem L) (M : Type w) [L.Structure M] : Prop :=
  ∀ l ∈ Γ, (literalFormula l).Realize M

def HasModel (Γ : Problem L) : Prop :=
  ∃ (M : Type u) (inst : L.Structure M), Nonempty M ∧ @Satisfies _ Γ M inst

theorem atom_formula_qf (a : Atom L) : a.formula.IsQF := by
  cases a with
  | equal t s => exact (BoundedFormula.IsAtomic.equal _ _).isQF
  | rel R ts => exact (BoundedFormula.IsAtomic.rel _ _).isQF

theorem literal_truth (l : Literal L) (M : Type w) [L.Structure M] :
    (literalFormula l).Realize M ↔ if l.1 then l.2.Realize M else ¬l.2.Realize M := by
  rcases l with ⟨b, a⟩
  cases b <;> simp [literalFormula, Atom.Realize]

theorem equal_truth (t s : GroundEquality.GroundTerm L) (M : Type w) [L.Structure M] :
    (Atom.equal t s).Realize M ↔ t.realize Empty.elim = s.realize (Empty.elim : Empty → M) := by
  have hassign : (default : Empty → M) = Empty.elim := Subsingleton.elim _ _
  simp [Atom.Realize, Atom.formula, Sentence.Realize, Formula.Realize,
    BoundedFormula.Realize, Term.realize_relabel, hassign]

theorem relation_truth {n : ℕ} (R : L.Relations n) (ts : Fin n → GroundEquality.GroundTerm L)
    (M : Type w) [L.Structure M] :
    (Atom.rel R ts).Realize M ↔ Structure.RelMap R (fun i => (ts i).realize (Empty.elim : Empty → M)) := by
  have hassign : (default : Empty → M) = Empty.elim := Subsingleton.elim _ _
  simp [Atom.Realize, Atom.formula, Sentence.Realize, Formula.Realize,
    BoundedFormula.Realize, Term.realize_relabel, hassign]

variable [∀ n, DecidableEq (L.Functions n)] [∀ n, DecidableEq (L.Relations n)]

instance atomDecidableEq : DecidableEq (Atom L) := by
  intro a b
  cases a with
  | equal t s =>
    cases b with
    | equal t' s' => exact decidable_of_iff (t = t' ∧ s = s') (by simp)
    | rel R ts => exact isFalse (by intro h; cases h)
  | @rel n R ts =>
    cases b with
    | equal t s => exact isFalse (by intro h; cases h)
    | @rel m Q us =>
      by_cases h : n = m
      · subst m
        exact decidable_of_iff (R = Q ∧ ts = us) (by simp)
      · exact isFalse (by intro heq; cases heq; exact h rfl)

def equations (Γ : Problem L) : Finset (GroundEquality.TermPair L) :=
  Γ.biUnion (fun l => match l with
    | (true, .equal t s) => {(t, s)}
    | _ => ∅)

def disequations (Γ : Problem L) : Finset (GroundEquality.TermPair L) :=
  Γ.biUnion (fun l => match l with
    | (false, .equal t s) => {(t, s)}
    | _ => ∅)

def Atom.subterms : Atom L → Finset (GroundEquality.GroundTerm L)
  | .equal t s => GroundEquality.subterms t ∪ GroundEquality.subterms s
  | .rel _ ts => Finset.univ.biUnion (fun i => GroundEquality.subterms (ts i))

def support (Γ : Problem L) : Finset (GroundEquality.GroundTerm L) :=
  Γ.biUnion (fun l => l.2.subterms)

omit [∀ n, DecidableEq (L.Relations n)] in
theorem support_closed [_instR : ∀ n, DecidableEq (L.Relations n)] (Γ : Problem L) : GroundEquality.SubtermClosed (support Γ) := by
  intro n f ts h i
  obtain ⟨l, hl, ht⟩ := Finset.mem_biUnion.mp h
  apply Finset.mem_biUnion.mpr
  refine ⟨l, hl, ?_⟩
  rcases l with ⟨b, a⟩
  cases a with
  | equal t s =>
    rcases Finset.mem_union.mp ht with ht | ht
    · exact Finset.mem_union_left _ (GroundEquality.subterms_closed t f ts ht i)
    · exact Finset.mem_union_right _ (GroundEquality.subterms_closed s f ts ht i)
  | rel R us =>
    obtain ⟨j, hj, ht⟩ := Finset.mem_biUnion.mp ht
    exact Finset.mem_biUnion.mpr ⟨j, hj, GroundEquality.subterms_closed (us j) f ts ht i⟩

omit [∀ n, DecidableEq (L.Relations n)] in
private theorem mem_equations (Γ : Problem L) (t s : GroundEquality.GroundTerm L) :
    (t, s) ∈ equations Γ ↔ (true, Atom.equal t s) ∈ Γ := by
  constructor
  · intro h
    obtain ⟨⟨b, a⟩, hl, hp⟩ := Finset.mem_biUnion.mp h
    cases b <;> cases a <;> simp_all [equations]
  · intro h
    exact Finset.mem_biUnion.mpr ⟨(true, Atom.equal t s), h, by simp⟩

omit [∀ n, DecidableEq (L.Relations n)] in
private theorem mem_disequations (Γ : Problem L) (t s : GroundEquality.GroundTerm L) :
    (t, s) ∈ disequations Γ ↔ (false, Atom.equal t s) ∈ Γ := by
  constructor
  · intro h
    obtain ⟨⟨b, a⟩, hl, hp⟩ := Finset.mem_biUnion.mp h
    cases b <;> cases a <;> simp_all [disequations]
  · intro h
    exact Finset.mem_biUnion.mpr ⟨(false, Atom.equal t s), h, by simp⟩

omit [∀ n, DecidableEq (L.Relations n)] in
private theorem atom_subterms_supported (Γ : Problem L) (l : Literal L) (hl : l ∈ Γ) :
    l.2.subterms ⊆ support Γ := by
  intro t ht
  exact Finset.mem_biUnion.mpr ⟨l, hl, ht⟩

omit [∀ n, DecidableEq (L.Relations n)] in
theorem equations_supported [_instR : ∀ n, DecidableEq (L.Relations n)] (Γ : Problem L) :
    equations Γ ⊆ (support Γ).product (support Γ) := by
  intro p hp
  have hl := (mem_equations Γ p.1 p.2).mp hp
  exact Finset.mem_product.mpr
    ⟨atom_subterms_supported Γ _ hl (Finset.mem_union_left _ (GroundEquality.mem_subterms p.1)),
      atom_subterms_supported Γ _ hl (Finset.mem_union_right _ (GroundEquality.mem_subterms p.2))⟩

omit [∀ n, DecidableEq (L.Relations n)] in
theorem disequations_supported [_instR : ∀ n, DecidableEq (L.Relations n)] (Γ : Problem L) :
    disequations Γ ⊆ (support Γ).product (support Γ) := by
  intro p hp
  have hl := (mem_disequations Γ p.1 p.2).mp hp
  exact Finset.mem_product.mpr
    ⟨atom_subterms_supported Γ _ hl (Finset.mem_union_left _ (GroundEquality.mem_subterms p.1)),
      atom_subterms_supported Γ _ hl (Finset.mem_union_right _ (GroundEquality.mem_subterms p.2))⟩

omit [∀ n, DecidableEq (L.Relations n)] in
theorem relation_arguments_supported [_instR : ∀ n, DecidableEq (L.Relations n)] (Γ : Problem L) {b : Bool} {n : ℕ}
    {R : L.Relations n} {ts : Fin n → GroundEquality.GroundTerm L}
    (h : (b, Atom.rel R ts) ∈ Γ) (i : Fin n) : ts i ∈ support Γ := by
  apply atom_subterms_supported Γ _ h
  exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, GroundEquality.mem_subterms (ts i)⟩

/-- The finite congruence computed solely from the positive equations. -/
def closure (Γ : Problem L) := GroundEquality.closure (support Γ) (equations Γ)

/-- Same relation symbol and congruent corresponding arguments; different arities never match. -/
def RelCongruent (C : Finset (GroundEquality.TermPair L)) : Atom L → Atom L → Prop
  | @Atom.rel _ n R ts, @Atom.rel _ m Q us =>
      if h : n = m then R = h.symm ▸ Q ∧ ∀ i, (ts i, us (Fin.cast h i)) ∈ C else False
  | _, _ => False

instance relCongruentDecidable (C : Finset (GroundEquality.TermPair L)) (a b : Atom L) :
    Decidable (RelCongruent C a b) := by
  cases a with
  | equal => exact isFalse (by simp [RelCongruent])
  | rel R ts =>
    cases b with
    | equal => exact isFalse (by simp [RelCongruent])
    | rel Q us => unfold RelCongruent; infer_instance

/-- Exactly the two finite conflict checks. -/
def ConflictFree (Γ : Problem L) : Prop :=
  (∀ p ∈ disequations Γ, p ∉ closure Γ) ∧
  (∀ a ∈ Γ, ∀ b ∈ Γ, a.1 = true → b.1 = false → ¬RelCongruent (closure Γ) a.2 b.2)

instance conflictFreeDecidable (Γ : Problem L) : Decidable (ConflictFree Γ) := by
  unfold ConflictFree
  infer_instance

abbrev Carrier (Γ : Problem L) := GroundEquality.Carrier (support Γ) (equations Γ) (equations_supported Γ)

def classOf (Γ : Problem L) (t : GroundEquality.GroundTerm L) (ht : t ∈ support Γ) : Carrier Γ :=
  GroundEquality.classOf (support Γ) (equations Γ) (equations_supported Γ) t ht

/-- Positive represented tuples, with their actual argument classes. -/
def relationMap (Γ : Problem L) {n : ℕ} (R : L.Relations n)
    (xs : Fin n → Carrier Γ) : Prop :=
  ∃ (ts : Fin n → GroundEquality.GroundTerm L), (true, Atom.rel R ts) ∈ Γ ∧
    ∀ i, ∃ hi : ts i ∈ support Γ, classOf Γ (ts i) hi = xs i

/-- Keep exactly GroundEquality.functionMap and change only the relations. -/
@[instance_reducible] noncomputable def modelStructure (Γ : Problem L) : L.Structure (Carrier Γ) where
  funMap := GroundEquality.functionMap (support Γ) (equations Γ) (equations_supported Γ) (support_closed Γ)
  RelMap := relationMap Γ

theorem relationMap_coherent (Γ : Problem L) {n : ℕ} (R : L.Relations n)
    (ts us : Fin n → GroundEquality.GroundTerm L)
    (ht : ∀ i, ts i ∈ support Γ) (hu : ∀ i, us i ∈ support Γ)
    (h : ∀ i, (ts i, us i) ∈ closure Γ) :
    relationMap Γ R (fun i => classOf Γ (ts i) (ht i)) ↔
      relationMap Γ R (fun i => classOf Γ (us i) (hu i)) := by
  have heq : (fun i => classOf Γ (ts i) (ht i)) = (fun i => classOf Γ (us i) (hu i)) := by
    funext i
    exact (GroundEquality.classOf_eq_iff _ _ _ _ _ _ _).mpr (h i)
  rw [heq]

theorem model_term_value (Γ : Problem L) (t : GroundEquality.GroundTerm L) (ht : t ∈ support Γ) :
    letI := modelStructure Γ
    t.realize Empty.elim = classOf Γ t ht := by
  let : L.Structure (Carrier Γ) := modelStructure Γ
  induction t with
  | var e => exact e.elim
  | func f ts ih =>
    change GroundEquality.functionMap _ _ _ _ f (fun i => (ts i).realize Empty.elim) = _
    exact GroundEquality.functionMap_of_represented _ _ _ _ f _
      ⟨ts, ht, fun i => (ih i (support_closed Γ f ts ht i)).symm⟩

theorem model_equality_iff (Γ : Problem L) (t s : GroundEquality.GroundTerm L)
    (ht : t ∈ support Γ) (hs : s ∈ support Γ) :
    letI := modelStructure Γ
    (Atom.equal t s).Realize (Carrier Γ) ↔ (t, s) ∈ closure Γ := by
  let : L.Structure (Carrier Γ) := modelStructure Γ
  rw [equal_truth, model_term_value Γ t ht, model_term_value Γ s hs]
  exact GroundEquality.classOf_eq_iff _ _ _ _ _ _ _

theorem model_relation_iff (Γ : Problem L) {n : ℕ} (R : L.Relations n)
    (ts : Fin n → GroundEquality.GroundTerm L) (ht : ∀ i, ts i ∈ support Γ) :
    letI := modelStructure Γ
    (Atom.rel R ts).Realize (Carrier Γ) ↔
      ∃ us : Fin n → GroundEquality.GroundTerm L, (true, Atom.rel R us) ∈ Γ ∧
        ∀ i, (us i, ts i) ∈ closure Γ := by
  let : L.Structure (Carrier Γ) := modelStructure Γ
  rw [relation_truth]
  change relationMap Γ R (fun i => (ts i).realize Empty.elim) ↔ _
  have hv : (fun i => (ts i).realize (Empty.elim : Empty → Carrier Γ)) =
      (fun i => classOf Γ (ts i) (ht i)) := funext fun i => model_term_value Γ (ts i) (ht i)
  rw [hv]
  constructor
  · rintro ⟨us, hu, hargs⟩
    refine ⟨us, hu, fun i => ?_⟩
    obtain ⟨hi, heq⟩ := hargs i
    exact (GroundEquality.classOf_eq_iff _ _ _ _ _ _ _).mp heq
  · rintro ⟨us, hu, hargs⟩
    refine ⟨us, hu, fun i => ⟨relation_arguments_supported Γ hu i, ?_⟩⟩
    exact (GroundEquality.classOf_eq_iff _ _ _ _ _ _ _).mpr (hargs i)

omit [∀ n, DecidableEq (L.Functions n)] [∀ n, DecidableEq (L.Relations n)] in
private theorem positive_true (Γ : Problem L) (M : Type w) [L.Structure M]
    (hM : Satisfies Γ M) (a : Atom L) (ha : (true, a) ∈ Γ) : a.Realize M := by
  simpa [literalFormula, Atom.Realize] using hM (true, a) ha

omit [∀ n, DecidableEq (L.Functions n)] [∀ n, DecidableEq (L.Relations n)] in
private theorem negative_false (Γ : Problem L) (M : Type w) [L.Structure M]
    (hM : Satisfies Γ M) (a : Atom L) (ha : (false, a) ∈ Γ) : ¬a.Realize M := by
  simpa [literalFormula, Atom.Realize] using hM (false, a) ha

theorem conflict_sound (Γ : Problem L) (M : Type w) [L.Structure M]
    (hM : Satisfies Γ M) : ConflictFree Γ := by
  have hE : ∀ p ∈ equations Γ,
      p.1.realize Empty.elim = p.2.realize (Empty.elim : Empty → M) := by
    intro p hp
    exact (equal_truth p.1 p.2 M).mp
      (positive_true Γ M hM _ ((mem_equations Γ p.1 p.2).mp hp))
  have hsound : ∀ p ∈ closure Γ,
      p.1.realize Empty.elim = p.2.realize (Empty.elim : Empty → M) :=
    GroundEquality.closure_sound _ _ (equations_supported Γ) M hE
  constructor
  · intro p hp hc
    exact negative_false Γ M hM _ ((mem_disequations Γ p.1 p.2).mp hp)
      ((equal_truth p.1 p.2 M).mpr (hsound p hc))
  · rintro ⟨ba, a⟩ ha ⟨bb, b⟩ hb hba hbb hc
    dsimp at hba hbb
    subst ba
    subst bb
    cases a with
    | equal t s => exact hc.elim
    | @rel n R ts =>
      cases b with
      | equal t s => exact hc.elim
      | @rel m Q us =>
        change RelCongruent (closure Γ) (Atom.rel R ts) (Atom.rel Q us) at hc
        by_cases hnm : n = m
        · subst m
          simp only [RelCongruent, Fin.cast_refl] at hc
          obtain ⟨hR, hargs⟩ := hc
          dsimp at hR hargs
          subst Q
          have hv : (fun i => (ts i).realize (Empty.elim : Empty → M)) =
              (fun i => (us i).realize (Empty.elim : Empty → M)) :=
            funext fun i => hsound _ (hargs i)
          apply negative_false Γ M hM _ hb
          apply (relation_truth R us M).mpr
          rw [← hv]
          exact (relation_truth R ts M).mp (positive_true Γ M hM _ ha)
        · simp [RelCongruent, hnm] at hc

theorem model_satisfies (Γ : Problem L) (h : ConflictFree Γ) :
    letI := modelStructure Γ
    Satisfies Γ (Carrier Γ) := by
  let : L.Structure (Carrier Γ) := modelStructure Γ
  rintro ⟨b, a⟩ hl
  rw [literal_truth]
  cases b with
  | false =>
    cases a with
    | equal t s =>
      have hp := (mem_disequations Γ t s).mpr hl
      obtain ⟨ht, hs⟩ := Finset.mem_product.mp (disequations_supported Γ hp)
      exact fun ha => h.1 _ hp ((model_equality_iff Γ t s ht hs).mp ha)
    | rel R ts =>
      intro ha
      obtain ⟨us, hu, hargs⟩ :=
        (model_relation_iff Γ R ts (relation_arguments_supported Γ hl)).mp ha
      apply h.2 (true, Atom.rel R us) hu (false, Atom.rel R ts) hl rfl rfl
      simpa [RelCongruent] using hargs
  | true =>
    cases a with
    | equal t s =>
      have hp := (mem_equations Γ t s).mpr hl
      obtain ⟨ht, hs⟩ := Finset.mem_product.mp (equations_supported Γ hp)
      exact (model_equality_iff Γ t s ht hs).mpr (GroundEquality.equations_subset_closure _ _ hp)
    | rel R ts =>
      apply (model_relation_iff Γ R ts (relation_arguments_supported Γ hl)).mpr
      exact ⟨ts, hl, fun i => (GroundEquality.closure_congruence _ _ (equations_supported Γ)).refl
        (ts i) (relation_arguments_supported Γ hl i)⟩

theorem carrier_finite (Γ : Problem L) : Finite (Carrier Γ) := by
  exact GroundEquality.finite_carrier _ _ _

theorem carrier_card_bound (Γ : Problem L) : Nat.card (Carrier Γ) ≤ (support Γ).card + 1 := by
  exact GroundEquality.carrier_card_bound _ _ _

theorem hasModel_iff (Γ : Problem L) : HasModel Γ ↔ ConflictFree Γ := by
  constructor
  · rintro ⟨M, inst, _, hM⟩
    let : L.Structure M := inst
    exact conflict_sound Γ M hM
  · intro h
    exact ⟨Carrier Γ, modelStructure Γ, inferInstance, model_satisfies Γ h⟩

/-- An executable finite predicate, not a semantic model-existence oracle. -/
def literalTest (Γ : Problem L) : Bool := decide (ConflictFree Γ)

theorem literalTest_correct (Γ : Problem L) : literalTest Γ = true ↔ HasModel Γ := by
  simp only [literalTest, decide_eq_true_eq]
  exact (hasModel_iff Γ).symm

end Lemmatheca.MathematicalLogic.QuantifierFreeValidity
