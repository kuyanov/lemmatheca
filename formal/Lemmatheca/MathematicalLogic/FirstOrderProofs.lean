import Lemmatheca.MathematicalLogic.FirstOrderSemantics

/-! Finite classical natural deduction with explicitly fresh auxiliary parameters.
The parameter type grows by one at an eigenparameter rule. Structural constructors
abbreviate finite proof-tree transformations, never semantic entailment. -/

namespace Lemmatheca.MathematicalLogic.FirstOrderProofs
open FirstOrder FirstOrder.Language
universe u v w
variable {L : Language.{u, v}} {α β : Type w}
noncomputable section
local instance : DecidableEq α := Classical.decEq _
local instance : DecidableEq (L.Formula α) := Classical.decEq _

/-- Open the distinguished bound slot at one term. -/
def instantiate (φ : L.BoundedFormula α 1) (t : L.Term α) : L.Formula α :=
  φ.toFormula.subst (Sum.elim Term.var (fun _ => t))

/-- Simultaneously fill finitely many distinguished slots with terms. -/
def instantiateSlots {n : ℕ} (φ : L.BoundedFormula α n) (ts : Fin n → L.Term α) :
    L.Formula α := φ.toFormula.subst (Sum.elim Term.var ts)

/-- Add a new parameter name disjoint from the old names. -/
def liftContext (Γ : Finset (L.Formula α)) : Finset (L.Formula (α ⊕ Fin 1)) :=
  Γ.image (Formula.relabel Sum.inl)

/-- Finite natural deduction, including the stated admissible tree operations. -/
inductive Proof (L : Language.{u, v}) : {α : Type w} → Finset (L.Formula α) → L.Formula α → Prop
  | assumption {α Γ A} : A ∈ Γ → Proof L (α := α) Γ A
  | conjIntro {α Γ A B} : Proof L (α := α) Γ A → Proof L Γ B → Proof L Γ (A ⊓ B)
  | conjElimLeft {α Γ A B} : Proof L (α := α) Γ (A ⊓ B) → Proof L Γ A
  | conjElimRight {α Γ A B} : Proof L (α := α) Γ (A ⊓ B) → Proof L Γ B
  | disjIntroLeft {α Γ A B} : Proof L (α := α) Γ A → Proof L Γ (A ⊔ B)
  | disjIntroRight {α Γ A B} : Proof L (α := α) Γ B → Proof L Γ (A ⊔ B)
  | disjElim {α Γ A B C} : Proof L (α := α) Γ (A ⊔ B) →
      Proof L (insert A Γ) C → Proof L (insert B Γ) C → Proof L Γ C
  | impIntro {α Γ A B} : Proof L (α := α) (insert A Γ) B → Proof L Γ (A.imp B)
  | impElim {α Γ A B} : Proof L (α := α) Γ (A.imp B) → Proof L Γ A → Proof L Γ B
  | negIntro {α Γ A} : Proof L (α := α) (insert A Γ) ⊥ → Proof L Γ A.not
  | negElim {α Γ A} : Proof L (α := α) Γ A → Proof L Γ A.not → Proof L Γ ⊥
  | falsumElim {α Γ A} : Proof L (α := α) Γ ⊥ → Proof L Γ A
  | classicalContradiction {α Γ A} : Proof L (α := α) (insert A.not Γ) ⊥ → Proof L Γ A
  | allElim {α Γ} {φ : L.BoundedFormula α 1} (t : L.Term α) : Proof L (α := α) Γ φ.all →
      Proof L Γ (instantiate φ t)
  | exIntro {α Γ} {φ : L.BoundedFormula α 1} (t : L.Term α) : Proof L (α := α) Γ (instantiate φ t) → Proof L Γ φ.ex
  | allIntro {α Γ} {φ : L.BoundedFormula α 1} : Proof L (α := α ⊕ Fin 1) (liftContext Γ) φ.toFormula →
      Proof L (α := α) Γ φ.all
  | allIntroParameter {α Γ} {φ : L.BoundedFormula α 1} (c : α)
      (hcφ : c ∉ φ.freeVarFinset) (hcΓ : ∀ A ∈ Γ, c ∉ A.freeVarFinset) :
      Proof L (α := α) Γ (instantiate φ (.var c)) → Proof L Γ φ.all
  | exElim {α Γ C} {φ : L.BoundedFormula α 1} : Proof L (α := α) Γ φ.ex →
      Proof L (insert φ.toFormula (liftContext Γ)) (C.relabel Sum.inl) → Proof L Γ C
  | equalIntro {α Γ} (t : L.Term α) : Proof L (α := α) Γ (t.equal t)
  | equalElim {α Γ} (φ : L.BoundedFormula α 1) (s t : L.Term α) :
      Proof L Γ (s.equal t) → Proof L Γ (instantiate φ s) → Proof L Γ (instantiate φ t)
  | weakening {α Γ Δ A} : Proof L (α := α) Γ A → Γ ⊆ Δ → Proof L Δ A
  | cut {α Γ Δ A B} : Proof L (α := α) Γ A → Proof L (insert A Δ) B → Proof L (Γ ∪ Δ) B
  | substitute {α β Γ A} (σ : α → L.Term β) : Proof L (α := α) Γ A →
      Proof L (Γ.image (fun φ => φ.subst σ)) (A.subst σ)
  | parameterClose {α β Γ A} :
      Proof L (α := β ⊕ α) (Γ.image (Formula.relabel Sum.inr)) (A.relabel Sum.inr) →
      Proof L (α := α) Γ A
  | rename {α β Γ A} (f : α → β) : Proof L (α := α) Γ A →
      Proof L (Γ.image (Formula.relabel f)) (Formula.relabel f A)
  | parameterCloseMap {α β Γ A} (f : α → β) (hf : Function.Injective f) :
      Proof L (α := β) (Γ.image (Formula.relabel f)) (Formula.relabel f A) →
      Proof L (α := α) Γ A
  | equalSlots {α Γ n} (φ : L.BoundedFormula α n) (ts us : Fin n → L.Term α) :
      (∀ i, Proof L Γ ((ts i).equal (us i))) →
      Proof L Γ (instantiateSlots φ ts) → Proof L Γ (instantiateSlots φ us)

/-- An arbitrary theory derives a formula using a finite collection of its axioms. -/
def Derives (T : Set (L.Formula α)) (A : L.Formula α) : Prop :=
  ∃ Γ : Finset (L.Formula α), (↑Γ : Set (L.Formula α)) ⊆ T ∧ Proof L Γ A
/-- Syntactic consistency is absence of a derivation of falsity. -/
def Consistent (T : Set (L.Formula α)) : Prop := ¬ Derives T ⊥
/-- Implication over a theory allows its antecedent as an additional assumption. -/
def ImpliesOver (T : Set (L.Formula α)) (A B : L.Formula α) : Prop := Derives (insert A T) B
/-- Equivalence over a theory requires both syntactic implications. -/
def EquivalentOver (T : Set (L.Formula α)) (A B : L.Formula α) : Prop :=
  ImpliesOver T A B ∧ ImpliesOver T B A
/-- A schema supplies one sentence for each item of indexing data. -/
def schemaTheory {ι : Type*} (s : ι → L.Sentence) : L.Theory := Set.range s

theorem instantiate_realize {M : Type*} [L.Structure M]
    (φ : L.BoundedFormula α 1) (t : L.Term α) (a : α → M) :
    (instantiate φ t).Realize a ↔ φ.Realize a (fun _ => t.realize a) := by
  rw [instantiate, Formula.Realize, BoundedFormula.realize_subst,
    ← Formula.Realize, BoundedFormula.realize_toFormula]
  simp only [Function.comp_def, Sum.elim_inl, Sum.elim_inr, Term.realize_var]

theorem instantiateSlots_realize {M : Type*} [L.Structure M] {n : ℕ}
    (φ : L.BoundedFormula α n) (ts : Fin n → L.Term α) (a : α → M) :
    (instantiateSlots φ ts).Realize a ↔ φ.Realize a (fun i => (ts i).realize a) := by
  rw [instantiateSlots, Formula.Realize, BoundedFormula.realize_subst,
    ← Formula.Realize, BoundedFormula.realize_toFormula]
  simp only [Function.comp_def, Sum.elim_inl, Sum.elim_inr, Term.realize_var]

private theorem snoc_zero {M : Type*} (m : M) :
    Fin.snoc (default : Fin 0 → M) m = (fun _ : Fin 1 => m) := by
  funext i
  have hi : i = 0 := Fin.eq_zero i
  subst i
  rfl

theorem Proof.sound {M : Type*} [L.Structure M] [Nonempty M] {Γ : Finset (L.Formula α)}
    {A : L.Formula α} (h : Proof L Γ A) (a : α → M)
    (hΓ : ∀ B ∈ Γ, B.Realize a) : A.Realize a := by
  classical
  induction h with
  | assumption hA => exact hΓ _ hA
  | conjIntro _ _ ihA ihB => exact Formula.realize_inf.mpr ⟨ihA a hΓ, ihB a hΓ⟩
  | conjElimLeft _ ih => exact (Formula.realize_inf.mp (ih a hΓ)).1
  | conjElimRight _ ih => exact (Formula.realize_inf.mp (ih a hΓ)).2
  | disjIntroLeft _ ih => exact Formula.realize_sup.mpr (Or.inl (ih a hΓ))
  | disjIntroRight _ ih => exact Formula.realize_sup.mpr (Or.inr (ih a hΓ))
  | disjElim _ _ _ ihAB ihA ihB =>
      rcases Formula.realize_sup.mp (ihAB a hΓ) with hA | hB
      · apply ihA a
        intro C hC
        rcases Finset.mem_insert.mp hC with rfl | hC
        · exact hA
        · exact hΓ C hC
      · apply ihB a
        intro C hC
        rcases Finset.mem_insert.mp hC with rfl | hC
        · exact hB
        · exact hΓ C hC
  | impIntro _ ih =>
      intro hA
      apply ih a
      intro C hC
      rcases Finset.mem_insert.mp hC with rfl | hC
      · exact hA
      · exact hΓ C hC
  | impElim _ _ ihAB ihA => exact ihAB a hΓ (ihA a hΓ)
  | negIntro _ ih =>
      intro hA
      apply ih a
      intro C hC
      rcases Finset.mem_insert.mp hC with rfl | hC
      · exact hA
      · exact hΓ C hC
  | negElim _ _ ihA ihnA => exact ihnA a hΓ (ihA a hΓ)
  | falsumElim _ ih => exact (ih a hΓ).elim
  | classicalContradiction _ ih =>
      apply Classical.byContradiction
      intro hnA
      apply ih a
      intro C hC
      rcases Finset.mem_insert.mp hC with rfl | hC
      · exact hnA
      · exact hΓ C hC
  | @allElim α Γ φ t _ ih =>
      apply (instantiate_realize φ t a).mpr
      simpa only [snoc_zero] using
        ih a hΓ (t.realize a)
  | @exIntro α Γ φ t _ ih =>
      have hφ := (instantiate_realize φ t a).mp (ih a hΓ)
      apply BoundedFormula.realize_ex.mpr
      exact ⟨t.realize a, by simpa only [snoc_zero] using hφ⟩
  | @allIntro α Γ φ _ ih =>
      intro m
      have hp := ih (Sum.elim a (fun _ => m)) (by
        intro C hC
        rcases Finset.mem_image.mp hC with ⟨B, hB, rfl⟩
        simpa using hΓ B hB)
      simpa only [Sum.elim_comp_inl, Sum.elim_comp_inr, snoc_zero] using
        (BoundedFormula.realize_toFormula φ _).mp hp
  | @allIntroParameter α Γ φ c hcφ hcΓ _ ih =>
      intro m
      let a' := Function.update a c m
      have hp := ih a' (by
        intro B hB
        apply (Lemmatheca.MathematicalLogic.FirstOrderSemantics.formula_realize_agree
          B a a' default ?_).mp (hΓ B hB)
        intro x hx
        have hxc : x ≠ c := by
          intro h
          exact hcΓ B hB (h ▸ hx)
        simp [a', hxc])
      have hφ := (instantiate_realize φ (.var c) a').mp hp
      have hm : (.var c : L.Term α).realize a' = m := by simp [a']
      rw [hm] at hφ
      have hOld := (Lemmatheca.MathematicalLogic.FirstOrderSemantics.formula_realize_agree
        φ a' a (fun _ => m) ?_).mp hφ
      · simpa only [snoc_zero] using hOld
      · intro x hx
        have hxc : x ≠ c := by
          intro h
          exact hcφ (h ▸ hx)
        simp [a', hxc]
  | @exElim α Γ C φ _ _ ihEx ihB =>
      rcases BoundedFormula.realize_ex.mp (ihEx a hΓ) with ⟨m, hm⟩
      have hp := ihB (Sum.elim a (fun _ => m)) (by
        intro D hD
        rcases Finset.mem_insert.mp hD with rfl | hD
        · apply (BoundedFormula.realize_toFormula φ _).mpr
          simpa only [Sum.elim_comp_inl, Sum.elim_comp_inr, snoc_zero] using hm
        · rcases Finset.mem_image.mp hD with ⟨B, hB, rfl⟩
          simpa using hΓ B hB)
      simpa using hp
  | equalIntro t => rfl
  | equalElim φ s t _ _ ihEq ihφ =>
      apply (instantiate_realize φ t a).mpr
      have hs := (instantiate_realize φ s a).mp (ihφ a hΓ)
      have he : s.realize a = t.realize a := by
        simpa [Term.equal, Formula.Realize, BoundedFormula.Realize,
          Term.realize_relabel] using ihEq a hΓ
      simpa [he] using hs
  | weakening _ hsub ih => exact ih a (fun B hB => hΓ B (hsub hB))
  | cut _ _ ihA ihB =>
      apply ihB a
      intro C hC
      rcases Finset.mem_insert.mp hC with rfl | hC
      · exact ihA a (fun B hB => hΓ B (Finset.mem_union_left _ hB))
      · exact hΓ C (Finset.mem_union_right _ hC)
  | substitute σ _ ih =>
      apply (BoundedFormula.realize_subst).mpr
      apply ih (fun x => (σ x).realize a)
      intro B hB
      apply (BoundedFormula.realize_subst).mp
      exact hΓ _ (Finset.mem_image.mpr ⟨B, hB, rfl⟩)
  | parameterClose _ ih =>
      let m : M := Classical.choice inferInstance
      have hp := ih (Sum.elim (fun _ => m) a) (by
        intro C hC
        rcases Finset.mem_image.mp hC with ⟨B, hB, rfl⟩
        simpa using hΓ B hB)
      simpa using hp
  | rename f _ ih =>
      apply Formula.realize_relabel.mpr
      apply ih (a ∘ f)
      intro B hB
      exact Formula.realize_relabel.mp (hΓ _ (Finset.mem_image.mpr ⟨B, hB, rfl⟩))
  | parameterCloseMap f hf _ ih =>
      let b := fun y => if hy : ∃ x, f x = y then a (Classical.choose hy)
        else Classical.choice (inferInstance : Nonempty M)
      have hb : b ∘ f = a := by
        funext x
        dsimp [b]
        have hx : ∃ z, f z = f x := ⟨x, rfl⟩
        rw [dite_eq_left hx]
        rw [hf (Classical.choose_spec hx)]
      have hp := ih b (by
        intro C hC
        rcases Finset.mem_image.mp hC with ⟨B, hB, rfl⟩
        simpa only [Formula.realize_relabel, hb] using hΓ B hB)
      simpa only [Formula.realize_relabel, hb] using hp
  | equalSlots φ ts us _ _ ihEq ihφ =>
      apply (instantiateSlots_realize φ us a).mpr
      have hp := (instantiateSlots_realize φ ts a).mp (ihφ a hΓ)
      have he : (fun i => (ts i).realize a) = (fun i => (us i).realize a) :=
        funext (fun i => Formula.realize_equal.mp (ihEq i a hΓ))
      simpa only [he] using hp

theorem derives_sound {M : Type*} [L.Structure M] [Nonempty M] {T : Set (L.Formula α)}
    {A : L.Formula α} (h : Derives T A) (a : α → M)
    (hT : ∀ B ∈ T, B.Realize a) : A.Realize a := by
  rcases h with ⟨Γ, hΓ, hp⟩
  exact hp.sound a (fun B hB => hT B (hΓ hB))

theorem derives_assumption {T : Set (L.Formula α)} {A : L.Formula α}
    (hA : A ∈ T) : Derives T A := by
  exact ⟨{A}, by simpa using hA, .assumption (by simp)⟩
theorem derives_mono {T U : Set (L.Formula α)} {A : L.Formula α}
    (h : Derives T A) (hTU : T ⊆ U) : Derives U A := by
  rcases h with ⟨Γ, hΓ, hp⟩
  exact ⟨Γ, hΓ.trans hTU, hp⟩
theorem derives_cut {T U : Set (L.Formula α)} {A B : L.Formula α}
    (hA : Derives T A) (hB : Derives (insert A U) B) : Derives (T ∪ U) B := by
  rcases hA with ⟨Γ, hΓ, hpA⟩
  rcases hB with ⟨Δ, hΔ, hpB⟩
  refine ⟨Γ ∪ Δ.erase A, ?_, .cut hpA (.weakening hpB ?_)⟩
  · intro C hC
    rcases Finset.mem_union.mp hC with hC | hC
    · exact Or.inl (hΓ hC)
    · have hc := Finset.mem_erase.mp hC
      exact Or.inr ((Set.mem_insert_iff.mp (hΔ hc.2)).resolve_left hc.1)
  · intro C hC
    by_cases hCA : C = A
    · simp [hCA]
    · exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hCA, hC⟩)
theorem derives_imp_iff {T : Set (L.Formula α)} {A B : L.Formula α} :
    Derives T (A.imp B) ↔ Derives (insert A T) B := by
  constructor
  · rintro ⟨Γ, hΓ, hp⟩
    refine ⟨insert A Γ, ?_, .impElim (.weakening hp (Finset.subset_insert _ _))
      (.assumption (by simp))⟩
    intro C hC
    rcases Finset.mem_insert.mp hC with rfl | hC
    · exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ (hΓ hC)
  · rintro ⟨Γ, hΓ, hp⟩
    refine ⟨Γ.erase A, ?_, .impIntro (.weakening hp ?_)⟩
    · intro C hC
      have hc := Finset.mem_erase.mp hC
      exact (Set.mem_insert_iff.mp (hΓ hc.2)).resolve_left hc.1
    · intro C hC
      by_cases hCA : C = A
      · simp [hCA]
      · exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hCA, hC⟩)
theorem derives_explosion {T : Set (L.Formula α)} {A : L.Formula α}
    (h : Derives T ⊥) : Derives T A := by
  rcases h with ⟨Γ, hΓ, hp⟩
  exact ⟨Γ, hΓ, .falsumElim hp⟩
theorem derives_iff_not_consistent_neg {T : Set (L.Formula α)} {A : L.Formula α} :
    Derives T A ↔ ¬ Consistent (insert A.not T) := by
  classical
  constructor
  · rintro ⟨Γ, hΓ, hp⟩ hcon
    apply hcon
    refine ⟨insert A.not Γ, ?_, .negElim (.weakening hp (Finset.subset_insert _ _))
      (.assumption (by simp))⟩
    intro C hC
    rcases Finset.mem_insert.mp hC with rfl | hC
    · exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ (hΓ hC)
  · intro hn
    obtain ⟨Γ, hΓ, hp⟩ := Classical.not_not.mp hn
    refine ⟨Γ.erase A.not, ?_, .classicalContradiction (.weakening hp ?_)⟩
    · intro C hC
      have hc := Finset.mem_erase.mp hC
      exact (Set.mem_insert_iff.mp (hΓ hc.2)).resolve_left hc.1
    · intro C hC
      by_cases hCA : C = A.not
      · simp [hCA]
      · exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hCA, hC⟩)
theorem derives_finite_support {T : Set (L.Formula α)} {A : L.Formula α}
    (h : Derives T A) : ∃ Γ : Finset (L.Formula α),
      (↑Γ : Set (L.Formula α)) ⊆ T ∧ Derives (↑Γ) A := by
  rcases h with ⟨Γ, hΓ, hp⟩
  exact ⟨Γ, hΓ, Γ, Set.Subset.rfl, hp⟩
theorem consistent_iff_finite {T : Set (L.Formula α)} :
    Consistent T ↔ ∀ Γ : Finset (L.Formula α), (↑Γ : Set (L.Formula α)) ⊆ T →
      Consistent (↑Γ : Set (L.Formula α)) := by
  constructor
  · intro hT Γ hΓ hp
    exact hT (derives_mono hp hΓ)
  · intro hfin hp
    rcases derives_finite_support hp with ⟨Γ, hΓ, hproof⟩
    exact hfin Γ hΓ hproof
theorem consistent_of_model {M : Type*} [L.Structure M] [Nonempty M]
    {T : Set (L.Formula α)} (a : α → M) (hT : ∀ B ∈ T, B.Realize a) : Consistent T := by
  intro hp
  exact derives_sound hp a hT
theorem theory_consistent_of_model {M : Type*} [L.Structure M] [Nonempty M] {T : L.Theory}
    (hT : M ⊨ T) : Consistent T := by
  exact consistent_of_model (default : Empty → M) (fun B hB => hT.realize_of_mem B hB)
theorem empty_theory_consistent (L : Language.{u, v}) : Consistent (∅ : L.Theory) := by
  let : L.Structure Unit := ⟨fun _ _ => (), fun _ _ => False⟩
  exact consistent_of_model (M := Unit) Empty.elim (by simp)
theorem impliesOver_realize {M : Type*} [L.Structure M] [Nonempty M]
    {T : L.Theory} {A B : L.Sentence}
    (h : ImpliesOver T A B) (hT : M ⊨ T) (hA : M ⊨ A) : M ⊨ B := by
  apply derives_sound h (default : Empty → M)
  intro C hC
  rcases Set.mem_insert_iff.mp hC with rfl | hC
  · exact hA
  · exact hT.realize_of_mem C hC
theorem equivalentOver_realize {M : Type*} [L.Structure M] [Nonempty M]
    {T : L.Theory} {A B : L.Sentence}
    (h : EquivalentOver T A B) (hT : M ⊨ T) : (M ⊨ A ↔ M ⊨ B) := by
  exact ⟨fun hA => impliesOver_realize h.1 hT hA, fun hB => impliesOver_realize h.2 hT hB⟩
theorem inconsistent_equivalent {T : Set (L.Formula α)} (hT : ¬ Consistent T)
    (A B : L.Formula α) : EquivalentOver T A B := by
  classical
  have hf : Derives T ⊥ := Classical.not_not.mp hT
  exact ⟨derives_explosion (derives_mono hf (Set.subset_insert _ _)),
    derives_explosion (derives_mono hf (Set.subset_insert _ _))⟩
@[simp] private theorem subst_relabel {γ : Type*} (t : L.Term α)
    (f : α → β) (σ : β → L.Term γ) :
    (t.relabel f).subst σ = t.subst (fun x => σ (f x)) := by
  induction t with
  | var x => rfl
  | func f ts ih => simp [Term.relabel, Term.subst, ih]

@[simp] private theorem subst_vars (t : L.Term α) (f : α → β) :
    t.subst (fun x => .var (f x)) = t.relabel f := by
  induction t with
  | var x => rfl
  | func f ts ih => simp [Term.relabel, Term.subst, ih]

theorem Proof.equal_symmetry {Γ : Finset (L.Formula α)} {s t : L.Term α}
    (h : Proof L Γ (s.equal t)) : Proof L Γ (t.equal s) := by
  let φ : L.BoundedFormula α 1 := (.var (.inr 0) : L.Term (α ⊕ Fin 1)).bdEqual
    (s.relabel Sum.inl)
  have hs : instantiate φ s = s.equal s := by
    simp [φ, instantiate, BoundedFormula.toFormula, Term.bdEqual,
      BoundedFormula.subst, BoundedFormula.mapTermRel, Term.equal,
      Term.subst, Term.relabel]
  have ht : instantiate φ t = t.equal s := by
    simp [φ, instantiate, BoundedFormula.toFormula, Term.bdEqual,
      BoundedFormula.subst, BoundedFormula.mapTermRel, Term.equal,
      Term.subst, Term.relabel]
  rw [← ht]
  exact .equalElim φ s t h (hs ▸ .equalIntro s)
theorem Proof.equal_transitivity {Γ : Finset (L.Formula α)} {s t r : L.Term α}
    (hst : Proof L Γ (s.equal t)) (htr : Proof L Γ (t.equal r)) :
    Proof L Γ (s.equal r) := by
  let φ : L.BoundedFormula α 1 := (s.relabel Sum.inl).bdEqual (.var (.inr 0))
  have ht : instantiate φ t = s.equal t := by
    simp [φ, instantiate, BoundedFormula.toFormula, Term.bdEqual,
      BoundedFormula.subst, BoundedFormula.mapTermRel, Term.equal,
      Term.subst, Term.relabel]
  have hr : instantiate φ r = s.equal r := by
    simp [φ, instantiate, BoundedFormula.toFormula, Term.bdEqual,
      BoundedFormula.subst, BoundedFormula.mapTermRel, Term.equal,
      Term.subst, Term.relabel]
  rw [← hr]
  exact .equalElim φ t r htr (ht ▸ hst)

/-- A unary predicate applied to the distinguished quantified slot. -/
def unaryBody (P : L.Relations 1) : L.BoundedFormula α 1 :=
  P.boundedFormula₁ (.var (.inr 0))

theorem witness_implication (P Q : L.Relations 1) :
    Derives ({((unaryBody P).imp (unaryBody Q)).all, (unaryBody P).ex} : L.Theory)
      (unaryBody Q).ex := by
  let Γ : Finset L.Sentence := {((unaryBody P).imp (unaryBody Q)).all, (unaryBody P).ex}
  refine ⟨Γ, by simp [Γ], ?_⟩
  apply Proof.exElim (φ := unaryBody P)
  · exact .assumption (by simp [Γ])
  · let c : L.Term (Empty ⊕ Fin 1) := .var (.inr 0)
    let Δ := insert (unaryBody P).toFormula (liftContext Γ)
    have hAll : Proof L Δ (((unaryBody P : L.BoundedFormula (Empty ⊕ Fin 1) 1).imp
        (unaryBody Q)).all) := by
      have hp : Proof L Δ
          (Formula.relabel Sum.inl (((unaryBody P).imp (unaryBody Q)).all : L.Sentence)) :=
        .assumption (Finset.mem_insert_of_mem
          (Finset.mem_image.mpr ⟨((unaryBody P).imp (unaryBody Q)).all, by simp [Γ], rfl⟩))
      simpa [unaryBody, Formula.relabel, BoundedFormula.relabel,
        BoundedFormula.mapTermRel, BoundedFormula.relabelAux,
        Relations.boundedFormula₁, Relations.boundedFormula,
        Term.relabel, Function.comp_def, finSumFinEquiv,
        Matrix.cons_fin_one] using hp
    have hP : Proof L Δ (instantiate (unaryBody P) c) := by
      have hp : Proof L Δ (unaryBody P).toFormula := .assumption (by simp [Δ])
      simpa [unaryBody, instantiate, BoundedFormula.toFormula, BoundedFormula.subst,
        BoundedFormula.mapTermRel, Relations.boundedFormula₁, Relations.boundedFormula,
        Relations.formula, Term.subst, Term.relabel, c] using hp
    have hQ : Proof L Δ (instantiate (unaryBody Q) c) :=
      Proof.impElim (Proof.allElim c hAll) hP
    have hp := Proof.exIntro (φ := unaryBody Q) c hQ
    simpa [Δ, unaryBody, Formula.relabel, BoundedFormula.relabel, BoundedFormula.toFormula,
      BoundedFormula.mapTermRel, BoundedFormula.relabelAux, BoundedFormula.ex,
      BoundedFormula.not, Bot.bot, Relations.boundedFormula₁, Relations.boundedFormula, Relations.formula,
      Term.relabel, Function.comp_def, finSumFinEquiv,
        Matrix.cons_fin_one] using hp

theorem Proof.relationDiagonal_exists {Γ : Finset (L.Formula α)}
    (R : L.Relations 2) (c : L.Term α) (h : Proof L Γ (R.formula₂ c c)) :
    Proof L Γ (R.boundedFormula₂ (c.relabel Sum.inl) (.var (.inr 0)) :
      L.BoundedFormula α 1).ex := by
  apply Proof.exIntro c
  have he : instantiate (R.boundedFormula₂ (c.relabel Sum.inl) (.var (.inr 0)) :
      L.BoundedFormula α 1) c = R.formula₂ c c := by
    simp only [instantiate, BoundedFormula.toFormula, BoundedFormula.subst,
      BoundedFormula.mapTermRel, Relations.boundedFormula₂, Relations.boundedFormula,
      Relations.formula₂, Relations.formula]
    congr 1
    funext i
    refine Fin.cases ?_ (Fin.cases ?_ (fun j => nomatch j)) i
    · simp [Term.relabel]
    · simp [Term.subst, Term.relabel]
  rw [he]
  exact h

end
end Lemmatheca.MathematicalLogic.FirstOrderProofs
