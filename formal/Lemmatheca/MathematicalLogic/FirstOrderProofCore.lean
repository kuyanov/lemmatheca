import Lemmatheca.MathematicalLogic.FirstOrderProofSyntax

/-! The displayed natural-deduction calculus. Only logical and equality rules
are constructors; structural operations are proved by induction below. -/
namespace Lemmatheca.MathematicalLogic.FirstOrderProofs
open FirstOrder FirstOrder.Language
universe u v w
variable {L : Language.{u, v}} {α β : Type w}
noncomputable section
local instance {δ : Type w} : DecidableEq (L.Formula δ) := Classical.decEq _

/-- Finite natural deduction, with protected fresh eigenparameters. -/
inductive CoreProof (L : Language.{u, v}) : {α : Type w} → Finset (L.Formula α) → L.Formula α → Prop
  | assumption {α Γ A} : A ∈ Γ → CoreProof L (α := α) Γ A
  | conjIntro {α Γ A B} : CoreProof L (α := α) Γ A → CoreProof L Γ B → CoreProof L Γ (A ⊓ B)
  | conjElimLeft {α Γ A B} : CoreProof L (α := α) Γ (A ⊓ B) → CoreProof L Γ A
  | conjElimRight {α Γ A B} : CoreProof L (α := α) Γ (A ⊓ B) → CoreProof L Γ B
  | disjIntroLeft {α Γ A B} : CoreProof L (α := α) Γ A → CoreProof L Γ (A ⊔ B)
  | disjIntroRight {α Γ A B} : CoreProof L (α := α) Γ B → CoreProof L Γ (A ⊔ B)
  | disjElim {α Γ A B C} : CoreProof L (α := α) Γ (A ⊔ B) →
      CoreProof L (insert A Γ) C → CoreProof L (insert B Γ) C → CoreProof L Γ C
  | impIntro {α Γ A B} : CoreProof L (α := α) (insert A Γ) B → CoreProof L Γ (A.imp B)
  | impElim {α Γ A B} : CoreProof L (α := α) Γ (A.imp B) → CoreProof L Γ A → CoreProof L Γ B
  | negIntro {α Γ A} : CoreProof L (α := α) (insert A Γ) ⊥ → CoreProof L Γ A.not
  | negElim {α Γ A} : CoreProof L (α := α) Γ A → CoreProof L Γ A.not → CoreProof L Γ ⊥
  | falsumElim {α Γ A} : CoreProof L (α := α) Γ ⊥ → CoreProof L Γ A
  | classicalContradiction {α Γ A} : CoreProof L (α := α) (insert A.not Γ) ⊥ → CoreProof L Γ A
  | allElim {α Γ} {φ : L.BoundedFormula α 1} (t : L.Term α) : CoreProof L (α := α) Γ φ.all →
      CoreProof L Γ (instantiate φ t)
  | exIntro {α Γ} {φ : L.BoundedFormula α 1} (t : L.Term α) : CoreProof L (α := α) Γ (instantiate φ t) → CoreProof L Γ φ.ex
  | allIntro {α Γ} {φ : L.BoundedFormula α 1} : CoreProof L (α := α ⊕ Fin 1) (liftContext Γ) φ.toFormula →
      CoreProof L (α := α) Γ φ.all
  | exElim {α Γ C} {φ : L.BoundedFormula α 1} : CoreProof L (α := α) Γ φ.ex →
      CoreProof L (insert φ.toFormula (liftContext Γ)) (C.relabel Sum.inl) → CoreProof L Γ C
  | equalIntro {α Γ} (t : L.Term α) : CoreProof L (α := α) Γ (t.equal t)
  | equalElim {α Γ} (φ : L.BoundedFormula α 1) (s t : L.Term α) :
      CoreProof L Γ (s.equal t) → CoreProof L Γ (instantiate φ s) → CoreProof L Γ (instantiate φ t)

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

theorem CoreProof.sound {M : Type*} [L.Structure M] [Nonempty M] {Γ : Finset (L.Formula α)}
    {A : L.Formula α} (h : CoreProof L Γ A) (a : α → M)
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

theorem CoreProof.weakening {Γ Δ : Finset (L.Formula α)} {A : L.Formula α}
    (h : CoreProof L Γ A) : Γ ⊆ Δ → CoreProof L Δ A := by
  induction h with
  | assumption hA => intro hsub; exact .assumption (hsub hA)
  | conjIntro _ _ ihA ihB => intro hsub; exact .conjIntro (ihA hsub) (ihB hsub)
  | conjElimLeft _ ih => intro hsub; exact .conjElimLeft (ih hsub)
  | conjElimRight _ ih => intro hsub; exact .conjElimRight (ih hsub)
  | disjIntroLeft _ ih => intro hsub; exact .disjIntroLeft (ih hsub)
  | disjIntroRight _ ih => intro hsub; exact .disjIntroRight (ih hsub)
  | disjElim _ _ _ ihAB ihA ihB =>
      intro hsub
      exact .disjElim (ihAB hsub) (ihA (Finset.insert_subset_insert _ hsub))
        (ihB (Finset.insert_subset_insert _ hsub))
  | impIntro _ ih => intro hsub; exact .impIntro (ih (Finset.insert_subset_insert _ hsub))
  | impElim _ _ ihAB ihA => intro hsub; exact .impElim (ihAB hsub) (ihA hsub)
  | negIntro _ ih => intro hsub; exact .negIntro (ih (Finset.insert_subset_insert _ hsub))
  | negElim _ _ ihA ihnA => intro hsub; exact .negElim (ihA hsub) (ihnA hsub)
  | falsumElim _ ih => intro hsub; exact .falsumElim (ih hsub)
  | classicalContradiction _ ih =>
      intro hsub
      exact .classicalContradiction (ih (Finset.insert_subset_insert _ hsub))
  | allElim t _ ih => intro hsub; exact .allElim t (ih hsub)
  | exIntro t _ ih => intro hsub; exact .exIntro t (ih hsub)
  | allIntro _ ih =>
      intro hsub
      apply CoreProof.allIntro (ih (Finset.image_subset_image hsub))
  | exElim _ _ ihEx ihB =>
      intro hsub
      exact .exElim (ihEx hsub) (ihB (Finset.insert_subset_insert _
        (Finset.image_subset_image hsub)))
  | equalIntro t => intro _; exact .equalIntro t
  | equalElim φ s t _ _ ihEq ihφ =>
      intro hsub
      exact .equalElim φ s t (ihEq hsub) (ihφ hsub)

/-- Capture-free substitution is an admissible proof-tree operation. The new
name introduced by an eigenparameter rule is protected by `liftSubst`. -/
theorem CoreProof.substitute {Γ : Finset (L.Formula α)} {A : L.Formula α}
    (h : CoreProof L Γ A) : ∀ {β : Type w} (σ : α → L.Term β),
    CoreProof L (Γ.image (fun φ => φ.subst σ)) (A.subst σ) := by
  induction h with
  | assumption hA => intro β σ; exact .assumption (Finset.mem_image.mpr ⟨_, hA, rfl⟩)
  | conjIntro _ _ ihA ihB =>
      intro β σ
      rw [formula_subst_inf]
      exact .conjIntro (ihA σ) (ihB σ)
  | conjElimLeft _ ih =>
      intro β σ
      exact .conjElimLeft (by simpa only [formula_subst_inf] using ih σ)
  | conjElimRight _ ih =>
      intro β σ
      exact .conjElimRight (by simpa only [formula_subst_inf] using ih σ)
  | disjIntroLeft _ ih => intro β σ; rw [formula_subst_sup]; exact .disjIntroLeft (ih σ)
  | disjIntroRight _ ih => intro β σ; rw [formula_subst_sup]; exact .disjIntroRight (ih σ)
  | disjElim _ _ _ ihAB ihA ihB =>
      intro β σ
      apply CoreProof.disjElim (by simpa only [formula_subst_sup] using ihAB σ)
      · simpa only [Finset.image_insert] using ihA σ
      · simpa only [Finset.image_insert] using ihB σ
  | impIntro _ ih =>
      intro β σ
      rw [formula_subst_imp]
      apply CoreProof.impIntro
      simpa only [Finset.image_insert] using ih σ
  | impElim _ _ ihAB ihA =>
      intro β σ
      exact .impElim (by simpa only [formula_subst_imp] using ihAB σ) (ihA σ)
  | negIntro _ ih =>
      intro β σ
      rw [formula_subst_not]
      apply CoreProof.negIntro
      simpa only [Finset.image_insert, formula_subst_bot] using ih σ
  | negElim _ _ ihA ihnA =>
      intro β σ
      rw [formula_subst_bot]
      exact .negElim (ihA σ) (by simpa only [formula_subst_not] using ihnA σ)
  | falsumElim _ ih =>
      intro β σ
      exact .falsumElim (by simpa only [formula_subst_bot] using ih σ)
  | classicalContradiction _ ih =>
      intro β σ
      apply CoreProof.classicalContradiction
      simpa only [Finset.image_insert, formula_subst_not, formula_subst_bot] using ih σ
  | allElim t _ ih =>
      intro β σ
      rw [instantiate_subst]
      exact .allElim (t.subst σ) (by simpa only [formula_subst_all] using ih σ)
  | exIntro t _ ih =>
      intro β σ
      rw [formula_subst_ex]
      apply CoreProof.exIntro (t.subst σ)
      simpa only [instantiate_subst] using ih σ
  | allIntro _ ih =>
      intro β σ
      rw [formula_subst_all]
      apply CoreProof.allIntro
      simpa only [liftContext_subst, toFormula_subst] using ih (liftSubst σ 1)
  | exElim _ _ ihEx ihB =>
      intro β σ
      apply CoreProof.exElim (by simpa only [formula_subst_ex] using ihEx σ)
      have hp := ihB (liftSubst σ 1)
      simp only [Finset.image_insert, liftContext_subst] at hp
      simpa only [toFormula_subst, formula_relabel_subst, formula_subst_relabel,
        liftSubst, Sum.elim_inl] using hp
  | equalIntro t =>
      intro β σ
      rw [formula_subst_equal]
      exact CoreProof.equalIntro (t.subst σ)
  | equalElim φ s t _ _ ihEq ihφ =>
      intro β σ
      rw [instantiate_subst]
      exact .equalElim (φ.subst σ) (s.subst σ) (t.subst σ)
        (by simpa only [formula_subst_equal] using ihEq σ)
        (by simpa only [instantiate_subst] using ihφ σ)

end
end Lemmatheca.MathematicalLogic.FirstOrderProofs
