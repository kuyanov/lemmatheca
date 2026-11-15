import Lemmatheca.HeytingArithmeticStrongInduction.Syntax

/-! A finite bounded-expression grammar with an explicit original-language expansion. -/
namespace Lemmatheca.ProofTheory.HeytingArithmetic.Bounded
open _root_.FirstOrder _root_.FirstOrder.Language
open Lemmatheca.ProofTheory.FirstOrder.BoundedFormula
open Lemmatheca.ProofTheory.HeytingArithmetic.Order
open Lemmatheca.ProofTheory.HeytingArithmetic.StrongInduction

/-- The bound uses the old names; only the body receives the fresh input. -/
inductive Expr : Type → Type 1 where
  | falsum {α : Type} : Expr α
  | equal {α : Type} (s t : LA.Term α) : Expr α
  | le {α : Type} (s t : LA.Term α) : Expr α
  | lt {α : Type} (s t : LA.Term α) : Expr α
  | neg {α : Type} (B : Expr α) : Expr α
  | conj {α : Type} (B C : Expr α) : Expr α
  | disj {α : Type} (B C : Expr α) : Expr α
  | impl {α : Type} (B C : Expr α) : Expr α
  | allLT {α : Type} (t : LA.Term α) (B : Expr (α ⊕ Unit)) : Expr α
  | exLT {α : Type} (t : LA.Term α) (B : Expr (α ⊕ Unit)) : Expr α
  | allLE {α : Type} (t : LA.Term α) (B : Expr (α ⊕ Unit)) : Expr α
  | exLE {α : Type} (t : LA.Term α) (B : Expr (α ⊕ Unit)) : Expr α

variable {α β : Type}

def strictExists (A : Formula (α ⊕ Unit)) (t : LA.Term α) : Formula α :=
  exUnit (.conj (ltFormula (.var (.inr ())) (t.relabel Sum.inl)) A)

def inclusiveAll (A : Formula (α ⊕ Unit)) (t : LA.Term α) : Formula α :=
  allUnit (.impl (leFormula (.var (.inr ())) (t.relabel Sum.inl)) A)

def inclusiveExists (A : Formula (α ⊕ Unit)) (t : LA.Term α) : Formula α :=
  exUnit (.conj (leFormula (.var (.inr ())) (t.relabel Sum.inl)) A)

open Lemmatheca.MathematicalLogic.FirstOrderProofs

private theorem unitSubst_vars (f : α → β) :
    unitSubst (fun a => (.var (f a) : LA.Term β)) =
      fun x => (.var (Sum.map f id x) : LA.Term (β ⊕ Unit)) := by
  funext x
  cases x <;> rfl

/-- The exact old-parameter substitution extends past the fresh quantified input. -/
theorem strictExists_subst (A : Formula (α ⊕ Unit)) (t : LA.Term α) (σ : α → LA.Term β) :
    (strictExists A t).subst σ = strictExists (A.subst (unitSubst σ)) (t.subst σ) := by
  simp [strictExists, exUnit_subst, subst_conj, unitSubst,
    term_subst_relabel, term_relabel_subst, Term.subst]

theorem inclusiveAll_subst (A : Formula (α ⊕ Unit)) (t : LA.Term α) (σ : α → LA.Term β) :
    (inclusiveAll A t).subst σ = inclusiveAll (A.subst (unitSubst σ)) (t.subst σ) := by
  simp [inclusiveAll, allUnit_subst, subst_impl, unitSubst,
    term_subst_relabel, term_relabel_subst, Term.subst]

theorem inclusiveExists_subst (A : Formula (α ⊕ Unit)) (t : LA.Term α) (σ : α → LA.Term β) :
    (inclusiveExists A t).subst σ = inclusiveExists (A.subst (unitSubst σ)) (t.subst σ) := by
  simp [inclusiveExists, exUnit_subst, subst_conj, unitSubst,
    term_subst_relabel, term_relabel_subst, Term.subst]

theorem strictExists_rename (A : Formula (α ⊕ Unit)) (t : LA.Term α) (f : α → β) :
    (strictExists A t).rename f = strictExists (parameterRename A f) (t.relabel f) := by
  simpa only [unitSubst_vars, parameterRename,
    Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.rename, term_subst_vars] using
    strictExists_subst A t (fun a => .var (f a))

theorem inclusiveAll_rename (A : Formula (α ⊕ Unit)) (t : LA.Term α) (f : α → β) :
    (inclusiveAll A t).rename f = inclusiveAll (parameterRename A f) (t.relabel f) := by
  simpa only [unitSubst_vars, parameterRename,
    Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.rename, term_subst_vars] using
    inclusiveAll_subst A t (fun a => .var (f a))

theorem inclusiveExists_rename (A : Formula (α ⊕ Unit)) (t : LA.Term α) (f : α → β) :
    (inclusiveExists A t).rename f = inclusiveExists (parameterRename A f) (t.relabel f) := by
  simpa only [unitSubst_vars, parameterRename,
    Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.rename, term_subst_vars] using
    inclusiveExists_subst A t (fun a => .var (f a))

/-- The guarded native existential body uses this actual supplied instance. -/
theorem strictExists_body_instance (A : Formula (α ⊕ Unit)) (t s : LA.Term α) :
    atTerm (.conj (ltFormula (.var (.inr ())) (t.relabel Sum.inl)) A) s =
      .conj (ltFormula s t) (atTerm A s) := by
  simp [atTerm, subst_conj, term_subst_relabel, Term.subst]

theorem inclusiveAll_body_instance (A : Formula (α ⊕ Unit)) (t s : LA.Term α) :
    atTerm (.impl (leFormula (.var (.inr ())) (t.relabel Sum.inl)) A) s =
      .impl (leFormula s t) (atTerm A s) := by
  simp [atTerm, subst_impl, term_subst_relabel, Term.subst]

theorem inclusiveExists_body_instance (A : Formula (α ⊕ Unit)) (t s : LA.Term α) :
    atTerm (.conj (leFormula (.var (.inr ())) (t.relabel Sum.inl)) A) s =
      .conj (leFormula s t) (atTerm A s) := by
  simp [atTerm, subst_conj, term_subst_relabel, Term.subst]

/-- Protected opening changes the input tag, retaining the literal old-name bound. -/
theorem strictExists_body_open (A : Formula (α ⊕ Unit)) (t : LA.Term α) :
    (.conj (ltFormula (.var (.inr ())) (t.relabel Sum.inl)) A : Formula (α ⊕ Unit)).rename
      (Sum.map id (fun _ => (0 : Fin 1))) =
      .conj (ltFormula (.var (.inr (0 : Fin 1))) (t.relabel Sum.inl))
        (A.rename (Sum.map id (fun _ => (0 : Fin 1)))) := by
  simp [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.rename, subst_conj,
    term_subst_vars, Term.relabel_relabel, Function.comp_def]

theorem inclusiveAll_body_open (A : Formula (α ⊕ Unit)) (t : LA.Term α) :
    (.impl (leFormula (.var (.inr ())) (t.relabel Sum.inl)) A : Formula (α ⊕ Unit)).rename
      (Sum.map id (fun _ => (0 : Fin 1))) =
      .impl (leFormula (.var (.inr (0 : Fin 1))) (t.relabel Sum.inl))
        (A.rename (Sum.map id (fun _ => (0 : Fin 1)))) := by
  simp [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.rename, subst_impl,
    term_subst_vars, Term.relabel_relabel, Function.comp_def]

theorem inclusiveExists_body_open (A : Formula (α ⊕ Unit)) (t : LA.Term α) :
    (.conj (leFormula (.var (.inr ())) (t.relabel Sum.inl)) A : Formula (α ⊕ Unit)).rename
      (Sum.map id (fun _ => (0 : Fin 1))) =
      .conj (leFormula (.var (.inr (0 : Fin 1))) (t.relabel Sum.inl))
        (A.rename (Sum.map id (fun _ => (0 : Fin 1)))) := by
  simp [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.rename, subst_conj,
    term_subst_vars, Term.relabel_relabel, Function.comp_def]


/-- Every output is an actual native arithmetic formula over the original signature. -/
def Expr.expand {α : Type} : Expr α → Formula α
  | .falsum => .falsum
  | .equal s t => termEqual s t
  | .le s t => leFormula s t
  | .lt s t => ltFormula s t
  | .neg B => .neg B.expand
  | .conj B C => .conj B.expand C.expand
  | .disj B C => .disj B.expand C.expand
  | .impl B C => .impl B.expand C.expand
  | .allLT t B => history B.expand t
  | .exLT t B => strictExists B.expand t
  | .allLE t B => inclusiveAll B.expand t
  | .exLE t B => inclusiveExists B.expand t

/-- Capture-free substitution stays within the displayed bounded grammar. -/
def Expr.subst {α β : Type} (B : Expr α) (σ : α → LA.Term β) : Expr β :=
  match B with
  | .falsum => .falsum
  | .equal s t => .equal (s.subst σ) (t.subst σ)
  | .le s t => .le (s.subst σ) (t.subst σ)
  | .lt s t => .lt (s.subst σ) (t.subst σ)
  | .neg C => .neg (C.subst σ)
  | .conj C D => .conj (C.subst σ) (D.subst σ)
  | .disj C D => .disj (C.subst σ) (D.subst σ)
  | .impl C D => .impl (C.subst σ) (D.subst σ)
  | .allLT t C => .allLT (t.subst σ) (C.subst (unitSubst σ))
  | .exLT t C => .exLT (t.subst σ) (C.subst (unitSubst σ))
  | .allLE t C => .allLE (t.subst σ) (C.subst (unitSubst σ))
  | .exLE t C => .exLE (t.subst σ) (C.subst (unitSubst σ))

def Expr.rename (B : Expr α) (f : α → β) : Expr β :=
  B.subst (fun a => .var (f a))

theorem expand_subst (B : Expr α) (σ : α → LA.Term β) :
    (B.subst σ).expand = B.expand.subst σ := by
  induction B generalizing β <;>
    simp_all only [Expr.subst, Expr.expand, termEqual_subst_poly,
      leFormula_subst, ltFormula_subst, subst_falsum, subst_neg, subst_conj, subst_disj,
      subst_impl, history_subst, strictExists_subst, inclusiveAll_subst, inclusiveExists_subst]

theorem expand_rename (B : Expr α) (f : α → β) :
    (B.rename f).expand = B.expand.rename f := by
  exact expand_subst B (fun a => .var (f a))

end Lemmatheca.ProofTheory.HeytingArithmetic.Bounded
