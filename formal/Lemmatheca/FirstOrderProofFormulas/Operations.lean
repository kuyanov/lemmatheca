import Lemmatheca.FirstOrderProofFormulas.Syntax

/-! Capture-free substitution laws and interfaces for proof transformations. -/
namespace Lemmatheca.ProofTheory.FirstOrder
open _root_.FirstOrder _root_.FirstOrder.Language
open Lemmatheca.MathematicalLogic.FirstOrderProofs
universe u v w w' w''
variable {L : Language.{u,v}} {α : Type w} {β : Type w'} {γ : Type w''}

@[simp] theorem liftScope_inclusion {n m} (σ : ScopeSubst L α β n m) (x : α ⊕ Fin n) :
    liftScope σ (scopeInclusion n x) = (σ x).relabel (scopeInclusion m) := by
  cases x <;> simp [liftScope, scopeInclusion]

@[simp] theorem liftScope_last {n m} (σ : ScopeSubst L α β n m) :
    liftScope σ (.inr (Fin.last n)) = .var (.inr (Fin.last m)) := by
  simp [liftScope]

@[simp] theorem liftScope_id (n : ℕ) :
    liftScope (Term.var : ScopeSubst L α α n n) = Term.var := by
  funext x
  cases x with
  | inl a => rfl
  | inr i =>
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [liftScope, scopeInclusion]

theorem liftScope_comp {n m k} (σ : ScopeSubst L α β n m) (τ : ScopeSubst L β γ m k) :
    liftScope (fun x => (σ x).subst τ) =
      (fun x => (liftScope σ x).subst (liftScope τ)) := by
  have hold (t : L.Term (β ⊕ Fin m)) :
      (t.relabel (scopeInclusion m)).subst (liftScope τ) =
        (t.subst τ).relabel (scopeInclusion k) := by
    rw [term_subst_relabel, term_relabel_subst]
    congr 1
    funext x
    exact liftScope_inclusion τ x
  funext x
  cases x with
  | inl a => simpa [liftScope] using (hold (σ (.inl a))).symm
  | inr i =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [liftScope, Term.subst]
    · simpa [liftScope] using (hold (σ (.inr j))).symm

namespace BoundedFormula

@[simp] theorem map_id {n} (A : BoundedFormula L α n) : A.map Term.var = A := by
  induction A <;> simp_all [map, term_subst_var]

theorem map_comp {n m k} (A : BoundedFormula L α n)
    (σ : ScopeSubst L α β n m) (τ : ScopeSubst L β γ m k) :
    (A.map σ).map τ = A.map (fun x => (σ x).subst τ) := by
  induction A generalizing m k <;>
    simp_all [map, term_subst_subst, ← liftScope_comp]

@[simp] theorem depth_map {n m} (A : BoundedFormula L α n) (σ : ScopeSubst L α β n m) :
    (A.map σ).depth = A.depth := by
  induction A generalizing m <;> simp_all [map, depth]

@[simp] theorem equalityFree_map {n m} (A : BoundedFormula L α n) (σ : ScopeSubst L α β n m) :
    (A.map σ).EqualityFree ↔ A.EqualityFree := by
  induction A generalizing m <;> simp_all [map, EqualityFree]

@[simp] theorem quantifierFree_map {n m} (A : BoundedFormula L α n)
    (σ : ScopeSubst L α β n m) :
    (A.map σ).QuantifierFree ↔ A.QuantifierFree := by
  induction A generalizing m <;> simp_all [map, QuantifierFree]

@[simp] theorem liftScope_freeScope (σ : α → L.Term β) (n : ℕ) :
    liftScope (freeScope σ n) = freeScope σ (n+1) := by
  funext x
  cases x with
  | inl a =>
    simp only [liftScope, freeScope, Sum.elim_inl, Term.relabel_relabel]
    rfl
  | inr i =>
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [liftScope, freeScope, scopeInclusion]

@[simp] theorem subst_falsum (σ : α → L.Term β) (n : ℕ) :
    (falsum : BoundedFormula L α n).subst σ = falsum := by
  rfl
@[simp] theorem subst_equal {n} (s t : L.Term (α ⊕ Fin n)) (σ : α → L.Term β) :
    (equal s t).subst σ = equal (s.subst (freeScope σ n)) (t.subst (freeScope σ n)) := by
  rfl
@[simp] theorem subst_rel {n k} (R : L.Relations k) (ts : Fin k → L.Term (α ⊕ Fin n))
    (σ : α → L.Term β) :
    (rel R ts).subst σ = rel R (fun i => (ts i).subst (freeScope σ n)) := by
  rfl
@[simp] theorem subst_neg {n} (A : BoundedFormula L α n) (σ : α → L.Term β) :
    A.neg.subst σ = (A.subst σ).neg := by
  rfl
@[simp] theorem subst_conj {n} (A B : BoundedFormula L α n) (σ : α → L.Term β) :
    (A.conj B).subst σ = (A.subst σ).conj (B.subst σ) := by
  rfl
@[simp] theorem subst_disj {n} (A B : BoundedFormula L α n) (σ : α → L.Term β) :
    (A.disj B).subst σ = (A.subst σ).disj (B.subst σ) := by
  rfl
@[simp] theorem subst_impl {n} (A B : BoundedFormula L α n) (σ : α → L.Term β) :
    (A.impl B).subst σ = (A.subst σ).impl (B.subst σ) := by
  rfl
@[simp] theorem subst_all {n} (A : BoundedFormula L α (n+1)) (σ : α → L.Term β) :
    A.all.subst σ = (A.subst σ).all := by
  simp [subst, map]
@[simp] theorem subst_ex {n} (A : BoundedFormula L α (n+1)) (σ : α → L.Term β) :
    A.ex.subst σ = (A.subst σ).ex := by
  simp [subst, map]

@[simp] theorem subst_id {n} (A : BoundedFormula L α n) : A.subst Term.var = A := by
  have hv : freeScope (Term.var : α → L.Term α) n = Term.var := by
    funext x
    cases x <;> rfl
  simpa only [subst, hv] using A.map_id

theorem subst_comp {n} (A : BoundedFormula L α n)
    (σ : α → L.Term β) (τ : β → L.Term γ) :
    (A.subst σ).subst τ = A.subst (fun x => (σ x).subst τ) := by
  unfold subst
  rw [map_comp]
  congr 1
  funext x
  cases x with
  | inl a =>
    simp only [freeScope, Sum.elim_inl, term_subst_relabel, term_relabel_subst]
  | inr i => rfl

@[simp] theorem rename_id {n} (A : BoundedFormula L α n) : A.rename id = A := by
  exact A.subst_id

theorem rename_comp {n} (A : BoundedFormula L α n) (f : α → β) (g : β → γ) :
    (A.rename f).rename g = A.rename (g ∘ f) := by
  simp only [rename, subst_comp, Term.subst, Function.comp_def]

theorem freeVarFinset_subst [DecidableEq α] [DecidableEq β] {n}
    (A : BoundedFormula L α n) (σ : α → L.Term β) :
    (A.subst σ).freeVarFinset = A.freeVarFinset.biUnion (fun x => (σ x).varFinset) := by
  have hterm {k} (t : L.Term (α ⊕ Fin k)) :
      (t.subst (freeScope σ k)).varFinsetLeft =
        t.varFinsetLeft.biUnion (fun x => (σ x).varFinset) :=
    Lemmatheca.MathematicalLogic.FirstOrderSyntax.scopedTermSubst_varFinsetLeft t σ
  induction A with
  | falsum => simp [subst, map, freeVarFinset]
  | equal s t => simp [subst_equal, freeVarFinset, hterm, Finset.union_biUnion]
  | rel R ts => simp [subst_rel, freeVarFinset, hterm, Finset.biUnion_biUnion]
  | neg A ih => simpa only [subst_neg, freeVarFinset] using ih
  | conj A B ihA ihB => simp [subst_conj, freeVarFinset, ihA, ihB, Finset.union_biUnion]
  | disj A B ihA ihB => simp [subst_disj, freeVarFinset, ihA, ihB, Finset.union_biUnion]
  | impl A B ihA ihB => simp [subst_impl, freeVarFinset, ihA, ihB, Finset.union_biUnion]
  | all A ih => simpa only [subst_all, freeVarFinset] using ih
  | ex A ih => simpa only [subst_ex, freeVarFinset] using ih

theorem toFormula_subst {n} (A : BoundedFormula L α n) (σ : α → L.Term β) :
    (A.subst σ).toFormula = A.toFormula.subst (liftSubst σ n) := by
  unfold toFormula subst
  rw [map_comp, map_comp]
  congr 1
  funext x
  cases x <;> simp [freeScope, liftSubst, term_subst_vars,
    Term.subst, Term.relabel_relabel]

theorem instantiateSlots_subst {n} (A : BoundedFormula L α n)
    (ts : Fin n → L.Term α) (σ : α → L.Term β) :
    (A.instantiateSlots ts).subst σ =
      (A.subst σ).instantiateSlots (fun i => (ts i).subst σ) := by
  unfold instantiateSlots subst
  rw [map_comp, map_comp]
  congr 1
  funext x
  cases x <;> simp [freeScope, term_subst_relabel, term_relabel_subst, term_subst_vars,
    Term.subst]

theorem instantiate_subst (A : BoundedFormula L α 1) (t : L.Term α) (σ : α → L.Term β) :
    (A.instantiate t).subst σ = (A.subst σ).instantiate (t.subst σ) := by
  simpa only [instantiate] using instantiateSlots_subst A (fun _ => t) σ

end BoundedFormula
end Lemmatheca.ProofTheory.FirstOrder
