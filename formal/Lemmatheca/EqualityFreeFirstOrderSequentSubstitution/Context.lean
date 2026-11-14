import Lemmatheca.EqualityFreeFirstOrderSequents.Properties

/-! Images of signed sequents and the protected free-name substitutions used by
actual quantified proof transformations. No new formula syntax is introduced. -/
namespace Lemmatheca.ProofTheory.ClassicalFirstOrder
open _root_.FirstOrder _root_.FirstOrder.Language
open Lemmatheca.MathematicalLogic.FirstOrderProofs (liftSubst)
universe u v w
variable {L : Language.{u,v}} {α β γ : Type w}
noncomputable section

/-- Image of the complete signed formulas under a free-term substitution. -/
def substContext (Γ : Sequent L α) (σ : α → L.Term β) : Sequent L β :=
  Γ.image (fun A => A.subst σ)

@[simp] theorem substContext_insert (A : Nnf L α 0) (Γ : Sequent L α)
    (σ : α → L.Term β) :
    substContext (insert A Γ) σ = insert (A.subst σ) (substContext Γ σ) := by
  simp [substContext]

@[simp] theorem substContext_empty (σ : α → L.Term β) :
    substContext (∅ : Sequent L α) σ = ∅ := by
  simp [substContext]

@[simp] theorem substContext_id (Γ : Sequent L α) :
    substContext Γ Term.var = Γ := by
  simp [substContext]

theorem Nnf.rename_subst {n} (A : Nnf L α n) (f : α → β) (σ : β → L.Term γ) :
    (A.rename f).subst σ = A.subst (fun x => σ (f x)) := by
  simp only [Nnf.rename, Nnf.subst_comp, Term.subst]

theorem Nnf.subst_rename {n} (A : Nnf L α n) (σ : α → L.Term β) (f : β → γ) :
    (A.subst σ).rename f = A.subst (fun x => (σ x).relabel f) := by
  simp only [Nnf.rename, Nnf.subst_comp,
    Lemmatheca.MathematicalLogic.FirstOrderProofs.term_subst_vars]

theorem liftContext_subst (Γ : Sequent L α) (σ : α → L.Term β) :
    substContext (liftContext Γ) (liftSubst σ 1) = liftContext (substContext Γ σ) := by
  simp only [substContext, liftContext, renameContext, Finset.image_image]
  congr 1
  funext A
  dsimp only [Function.comp_apply]
  rw [Nnf.rename_subst, Nnf.subst_rename]
  rfl

theorem renameContext_comp (Γ : Sequent L α) (f : α → β) (g : β → γ) :
    renameContext (renameContext Γ f) g = renameContext Γ (g ∘ f) := by
  simp only [renameContext, Finset.image_image, Function.comp_def, Nnf.rename_comp]

@[simp] theorem renameContext_id (Γ : Sequent L α) : renameContext Γ id = Γ := by
  simp [renameContext]

/-- Only the names in the finite endsequent; internal temporary names are not included. -/
def sequentSupport [DecidableEq α] (Γ : Sequent L α) : Finset α :=
  Γ.biUnion (fun A => A.freeVarFinset)

theorem Nnf.freeVarFinset_subst [DecidableEq α] [DecidableEq β] (A : Nnf L α 0) (σ : α → L.Term β) :
    (A.subst σ).freeVarFinset = A.freeVarFinset.biUnion (fun x => (σ x).varFinset) := by
  unfold Nnf.freeVarFinset
  rw [Nnf.read_subst]
  exact A.read.freeVarFinset_subst σ

theorem sequentSupport_subst [DecidableEq α] [DecidableEq β] (Γ : Sequent L α) (σ : α → L.Term β) :
    sequentSupport (substContext Γ σ) =
      (sequentSupport Γ).biUnion (fun x => (σ x).varFinset) := by
  classical
  ext x
  simp only [sequentSupport, substContext, Finset.mem_biUnion, Finset.mem_image]
  constructor
  · rintro ⟨B, ⟨A, hA, rfl⟩, hx⟩
    rw [Nnf.freeVarFinset_subst] at hx
    rcases Finset.mem_biUnion.mp hx with ⟨y, hy, hxy⟩
    exact ⟨y, ⟨A, hA, hy⟩, hxy⟩
  · rintro ⟨y, ⟨A, hA, hy⟩, hxy⟩
    refine ⟨A.subst σ, ⟨A, hA, rfl⟩, ?_⟩
    rw [Nnf.freeVarFinset_subst]
    exact Finset.mem_biUnion.mpr ⟨y, hy, hxy⟩

/-- Extend across the countable reserve while retaining each reserved name. -/
def reserveSubst (σ : α → L.Term β) : α ⊕ ℕ → L.Term (β ⊕ ℕ) :=
  Sum.elim (fun x => (σ x).relabel Sum.inl) (fun i => .var (.inr i))

theorem reserve_subst_context (Γ : Sequent L α) (σ : α → L.Term β) :
    substContext (renameContext Γ (Sum.inl : α → α ⊕ ℕ)) (reserveSubst σ) =
      renameContext (substContext Γ σ) Sum.inl := by
  simp only [substContext, renameContext, Finset.image_image]
  congr 1
  funext A
  dsimp only [Function.comp_apply]
  rw [Nnf.rename_subst, Nnf.subst_rename]
  rfl

end
end Lemmatheca.ProofTheory.ClassicalFirstOrder
