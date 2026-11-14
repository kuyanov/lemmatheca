import Lemmatheca.IntuitionisticFirstOrderDeduction.Structural

/-! Ordinary classical interpretation. Raw soundness does not assume an inhabited
domain; assigning the auxiliary reserve in a public certificate does. -/
namespace Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction
open _root_.FirstOrder _root_.FirstOrder.Language
universe u v w
variable {L : Language.{u,v}} {α β : Type w} {c e : Bool}
noncomputable section
local instance ndSoundnessFormulaEq {δ : Type w} : DecidableEq (Formula L δ) :=
  Classical.decEq _

/-- Interpretation of a complete full formula at its free-name assignment. -/
def Holds {M : Type*} [L.Structure M] (A : Formula L α) (a : α → M) : Prop :=
  A.Realize a Fin.elim0

theorem holds_subst {M : Type*} [L.Structure M] (A : Formula L α)
    (σ : α → L.Term β) (a : β → M) :
    Holds (A.subst σ) a ↔ Holds A (fun x => (σ x).realize a) := by
  unfold Holds Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.Realize
    Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst
  rw [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.realize_map]
  have hv : (fun x : α ⊕ Fin 0 =>
      (Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.freeScope σ 0 x).realize
        (Sum.elim a Fin.elim0)) = Sum.elim (fun x => (σ x).realize a) Fin.elim0 := by
    funext x
    cases x with
    | inl x => simp [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.freeScope,
        Term.realize_relabel, Function.comp_def]
    | inr i => exact Fin.elim0 i
  rw [hv]

theorem holds_rename {M : Type*} [L.Structure M] (A : Formula L α)
    (f : α → β) (a : β → M) : Holds (A.rename f) a ↔ Holds A (a ∘ f) := by
  simpa only [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.rename,
    Term.realize_var, Function.comp_def] using holds_subst A (fun x => .var (f x)) a

theorem holds_instantiate {M : Type*} [L.Structure M] (B : BF L α 1)
    (t : L.Term α) (a : α → M) :
    Holds (B.instantiate t) a ↔ B.Realize a (fun _ => t.realize a) := by
  unfold Holds Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.Realize
    Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.instantiate
    Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.instantiateSlots
  rw [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.realize_map]
  have hv : (fun x : α ⊕ Fin 1 =>
      (Sum.elim (fun x => (Term.var (Sum.inl x) : L.Term (α ⊕ Fin 0)))
        (fun _ => t.relabel Sum.inl) x).realize (Sum.elim a Fin.elim0)) =
      Sum.elim a (fun _ => t.realize a) := by
    funext x
    cases x <;> simp [Term.realize_relabel, Function.comp_def]
  rw [hv]

theorem holds_open {M : Type*} [L.Structure M] (B : BF L α 1) (a : α → M) (m : M) :
    Holds B.toFormula (Sum.elim a (fun _ => m)) ↔ B.Realize a (fun _ => m) := by
  unfold Holds Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.Realize
    Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.toFormula
  rw [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.realize_map]
  rfl

private theorem extend_zero {M : Type*} (a : α → M) (m : M) :
    Lemmatheca.ProofTheory.FirstOrder.extendAssignment (Sum.elim a Fin.elim0) m =
      Sum.elim a (fun _ : Fin 1 => m) := by
  funext x
  cases x with
  | inl x => rfl
  | inr i =>
      have hi : i = 0 := Fin.eq_zero i
      subst i
      rfl



theorem holds_all {M : Type*} [L.Structure M] (B : BF L α 1) (a : α → M) :
    Holds (.all B) a ↔ ∀ m, B.Realize a (fun _ => m) := by
  unfold Holds Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.Realize
  simp only [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.realize, extend_zero]

theorem holds_ex {M : Type*} [L.Structure M] (B : BF L α 1) (a : α → M) :
    Holds (.ex B) a ↔ ∃ m, B.Realize a (fun _ => m) := by
  unfold Holds Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.Realize
  simp only [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.realize, extend_zero]

theorem Derivation.sound {M : Type*} [L.Structure M] {Γ : Context L α}
    {A : Formula L α} (h : Derivation c e L Γ A) (a : α → M)
    (hΓ : ∀ B ∈ Γ, Holds B a) : Holds A a := by
  classical
  induction h with
  | assumption hA => exact hΓ _ hA
  | conjIntro _ _ ihA ihB => exact ⟨ihA a hΓ, ihB a hΓ⟩
  | conjElimLeft _ ih => exact (ih a hΓ).1
  | conjElimRight _ ih => exact (ih a hΓ).2
  | disjIntroLeft _ ih => exact Or.inl (ih a hΓ)
  | disjIntroRight _ ih => exact Or.inr (ih a hΓ)
  | disjElim _ _ _ ihAB ihA ihB =>
      rcases ihAB a hΓ with hA | hB
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
  | classicalContradiction _ _ ih =>
      apply Classical.byContradiction
      intro hnA
      apply ih a
      intro C hC
      rcases Finset.mem_insert.mp hC with rfl | hC
      · exact hnA
      · exact hΓ C hC
  | allElim t _ ih =>
      apply (holds_instantiate _ t a).mpr
      exact (holds_all _ a).mp (ih a hΓ) (t.realize a)
  | exIntro t _ ih =>
      apply (holds_ex _ a).mpr
      exact ⟨t.realize a, (holds_instantiate _ t a).mp (ih a hΓ)⟩
  | @allIntro α Γ B _ ih =>
      apply (holds_all _ a).mpr
      intro m
      have hp := ih (Sum.elim a (fun _ => m)) (by
        intro C hC
        rcases Finset.mem_image.mp hC with ⟨D, hD, rfl⟩
        exact (holds_rename D _ _).mpr (hΓ D hD))
      exact (holds_open B a m).mp hp
  | @exElim α Γ C B _ _ ihEx ihB =>
      rcases (holds_ex B a).mp (ihEx a hΓ) with ⟨m, hm⟩
      have hp := ihB (Sum.elim a (fun _ => m)) (by
        intro D hD
        rcases Finset.mem_insert.mp hD with rfl | hD
        · exact (holds_open B a m).mpr hm
        · rcases Finset.mem_image.mp hD with ⟨E, hE, rfl⟩
          exact (holds_rename E _ _).mpr (hΓ E hE))
      exact (holds_rename C Sum.inl (Sum.elim a (fun _ => m))).mp hp
  | equalIntro t _ => simp [Holds, termEqual,
      Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.Realize,
      Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.realize]
  | equalElim B s t _ _ _ ihEq ihB =>
      apply (holds_instantiate B t a).mpr
      have hs := (holds_instantiate B s a).mp (ihB a hΓ)
      have he : s.realize a = t.realize a := by
        simpa [Holds, termEqual,
          Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.Realize,
          Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.realize,
          Term.realize_relabel, Function.comp_def] using ihEq a hΓ
      simpa only [he] using hs

theorem Proof.sound {M : Type*} [L.Structure M] [Nonempty M] {Γ : Context L α}
    {A : Formula L α} (h : Proof c e L Γ A) (a : α → M)
    (hΓ : ∀ B ∈ Γ, Holds B a) : Holds A a := by
  classical
  let m : M := Classical.choice inferInstance
  have hp := Derivation.sound h (Sum.elim a (fun _ => m)) (by
    intro C hC
    obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hC
    exact (holds_rename B _ _).mpr (hΓ B hB))
  exact (holds_rename A Sum.inl (Sum.elim a (fun _ => m))).mp hp

theorem TheoryProof.sound {M : Type*} [L.Structure M] [Nonempty M]
    {T : Set (Formula L α)} {A : Formula L α} (h : TheoryProof c e L T A) (a : α → M)
    (hT : ∀ B ∈ T, Holds B a) : Holds A a := by
  exact h.derivation.sound a (fun B hB => hT B (h.allowed B hB))

theorem raw_consistent (L : Language.{u,v}) (α : Type w) (c e : Bool) :
    ¬ Nonempty (Derivation c e L (α := α) ∅ .falsum) := by
  let unitModel : L.Structure PUnit.{1} := {funMap := fun _ _ => PUnit.unit, RelMap := fun _ _ => False}
  rintro ⟨h⟩
  exact h.sound (fun _ => PUnit.unit) (by simp)

theorem public_consistent (L : Language.{u,v}) (α : Type w) (c e : Bool) :
    ¬ Derives c e L (α := α) ∅ .falsum := by
  let unitModel : L.Structure PUnit.{1} := {funMap := fun _ _ => PUnit.unit, RelMap := fun _ _ => False}
  rintro ⟨h⟩
  exact h.sound (fun _ => PUnit.unit) (by simp)

end
end Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction
