import Mathlib.ModelTheory.Syntax

/-! Free parameters and indexed scoped placeholders for first-order syntax. -/

namespace Lemmatheca.MathematicalLogic.FirstOrderSyntax

open FirstOrder FirstOrder.Language

universe u v u' v'

variable {L : Language.{u, v}} {α : Type u'} {β : Type v'} {n : ℕ}

/-- Substitute free parameters in a scoped term and retain every placeholder. -/
def scopedTermSubst (t : L.Term (α ⊕ Fin n)) (σ : α → L.Term β) :
    L.Term (β ⊕ Fin n) :=
  t.subst (Sum.elim (fun a => (σ a).relabel Sum.inl) (fun i => .var (.inr i)))

theorem term_varFinset_subst [DecidableEq α] [DecidableEq β]
    (t : L.Term α) (σ : α → L.Term β) :
    (t.subst σ).varFinset = t.varFinset.biUnion (fun a => (σ a).varFinset) := by
  induction t with
  | var a => simp [Finset.singleton_biUnion]
  | func f ts ih => simp only [Term.subst, Term.varFinset, ih, Finset.biUnion_biUnion]

private theorem varFinsetLeft_relabel_inl [DecidableEq α] (t : L.Term α) :
    (t.relabel (Sum.inl : α → α ⊕ Fin n)).varFinsetLeft = t.varFinset := by
  induction t with
  | var a => rfl
  | func f ts ih => simp only [Term.relabel, Term.varFinsetLeft, Term.varFinset, ih]

theorem scopedTermSubst_varFinsetLeft [DecidableEq α] [DecidableEq β]
    (t : L.Term (α ⊕ Fin n)) (σ : α → L.Term β) :
    (scopedTermSubst t σ).varFinsetLeft =
      t.varFinsetLeft.biUnion (fun a => (σ a).varFinset) := by
  induction t with
  | var a =>
    cases a with
    | inl a => simp [scopedTermSubst, varFinsetLeft_relabel_inl, Finset.singleton_biUnion]
    | inr i => simp [scopedTermSubst]
  | func f ts ih =>
    change (Finset.univ.biUnion fun i => (scopedTermSubst (ts i) σ).varFinsetLeft) = _
    simp only [ih, Term.varFinsetLeft, Finset.biUnion_biUnion]

theorem formula_freeVarFinset_subst [DecidableEq α] [DecidableEq β]
    (φ : L.BoundedFormula α n) (σ : α → L.Term β) :
    (φ.subst σ).freeVarFinset =
      φ.freeVarFinset.biUnion (fun a => (σ a).varFinset) := by
  induction φ with
  | falsum => rfl
  | equal t₁ t₂ =>
    change (scopedTermSubst t₁ σ).varFinsetLeft ∪ (scopedTermSubst t₂ σ).varFinsetLeft = _
    rw [scopedTermSubst_varFinsetLeft, scopedTermSubst_varFinsetLeft]
    exact (Finset.union_biUnion).symm
  | rel R ts =>
    change (Finset.univ.biUnion fun i => (scopedTermSubst (ts i) σ).varFinsetLeft) = _
    simp only [scopedTermSubst_varFinsetLeft, BoundedFormula.freeVarFinset,
      Finset.biUnion_biUnion]
  | imp φ ψ ihφ ihψ =>
    change (φ.subst σ).freeVarFinset ∪ (ψ.subst σ).freeVarFinset = _
    rw [ihφ, ihψ]
    exact (Finset.union_biUnion).symm
  | all φ ih => exact ih

/-- Retype a complete formula with empty free support as a sentence. -/
def sentenceOfNoFreeVar [DecidableEq α] (φ : L.Formula α)
    (h : φ.freeVarFinset = ∅) : L.Sentence :=
  φ.restrictFreeVar fun a => (Finset.notMem_empty a.val (h ▸ a.property)).elim

/-- A single binary relation symbol, with no symbols at other arities. -/
inductive BinaryRelationSymbol : ℕ → Type
  | rel : BinaryRelationSymbol 2

/-- The language with one binary relation and no function symbols. -/
def binaryRelLanguage : Language :=
  ⟨fun _ => Empty, BinaryRelationSymbol⟩

end Lemmatheca.MathematicalLogic.FirstOrderSyntax
