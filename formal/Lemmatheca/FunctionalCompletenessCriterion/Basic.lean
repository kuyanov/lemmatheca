import Lemmatheca.PropositionalNormalForms.PropositionalNormalForms
import Mathlib.Data.Bool.Basic

namespace Lemmatheca.MathematicalLogic.FunctionalCompletenessCriterion

open Propositional
universe u v

structure Operation where
  arity : ℕ
  table : TruthFunction arity

inductive Term (S : Set Operation) (α : Type u) : Type u where
  | atom (a : α)
  | gate (g : Operation) (hg : g ∈ S) (args : Fin g.arity → Term S α)

def termEval {S : Set Operation} {α : Type u} (row : α → Bool) : Term S α → Bool
  | .atom a => row a
  | .gate g _ args => g.table (fun i => termEval row (args i))

def termSubst {S : Set Operation} {α : Type u} {β : Type v}
    (σ : α → Term S β) : Term S α → Term S β
  | .atom a => σ a
  | .gate g hg args => .gate g hg (fun i => termSubst σ (args i))

def Generates (S : Set Operation) {n : ℕ} (f : TruthFunction n) : Prop :=
  ∃ t : Term S (Fin n), ∀ row, termEval row t = f row

def PositiveComplete (S : Set Operation) : Prop :=
  ∀ n, 0 < n → ∀ f : TruthFunction n, Generates S f

def FullComplete (S : Set Operation) : Prop :=
  ∀ n, ∀ f : TruthFunction n, Generates S f

def HasClosedTerm (S : Set Operation) : Prop := Nonempty (Term S (Fin 0))

def superpose {n m : ℕ} (f : TruthFunction n) (args : Fin n → TruthFunction m) :
    TruthFunction m := fun row => f (fun i => args i row)

noncomputable def toFormula {S : Set Operation} {α : Type u} : Term S α → PropFormula α
  | .atom a => .atom a
  | .gate g _ args =>
    Propositional.subst (fun i => toFormula (args i))
      (dnfFormula (canonicalDnf id g.table))

theorem termSubst_eval {S : Set Operation} {α : Type u} {β : Type v}
    (σ : α → Term S β) (t : Term S α) (row : β → Bool) :
    termEval row (termSubst σ t) = termEval (fun a => termEval row (σ a)) t := by
  induction t with
  | atom a => rfl
  | gate g hg args ih =>
    simp only [termSubst, termEval]
    exact congrArg g.table (funext ih)

theorem toFormula_eval {S : Set Operation} {α : Type u}
    (t : Term S α) (row : α → Bool) :
    Propositional.eval row (toFormula t) = termEval row t := by
  induction t with
  | atom a => rfl
  | gate g hg args ih =>
    simp only [toFormula, Propositional.eval_subst]
    rw [(canonicalDnf_represents id g.table).2]
    exact congrArg g.table (funext ih)

theorem toFormula_represents {S : Set Operation} {n : ℕ} (t : Term S (Fin n)) :
    Represents id (fun row => termEval row t) (toFormula t) := by
  constructor
  · intro a ha
    exact ⟨a, rfl⟩
  · intro row
    exact toFormula_eval t row

theorem generates_projection (S : Set Operation) {n : ℕ} (i : Fin n) :
    Generates S (fun row => row i) := by
  exact ⟨.atom i, fun _ => rfl⟩

theorem generates_member {S : Set Operation} (g : Operation) (hg : g ∈ S) :
    Generates S g.table := by
  exact ⟨.gate g hg (fun i => .atom i), fun _ => rfl⟩

theorem generates_superpose {S : Set Operation} {n m : ℕ}
    (f : TruthFunction n) (args : Fin n → TruthFunction m)
    (hf : Generates S f) (hargs : ∀ i, Generates S (args i)) :
    Generates S (superpose f args) := by
  classical
  obtain ⟨t, ht⟩ := hf
  choose ts hts using hargs
  refine ⟨termSubst ts t, fun row => ?_⟩
  rw [termSubst_eval, ht]
  exact congrArg f (funext (fun i => hts i row))

theorem closed_iff_nullary (S : Set Operation) :
    HasClosedTerm S ↔ ∃ g ∈ S, g.arity = 0 := by
  constructor
  · rintro ⟨t⟩
    induction t with
    | atom a => exact Fin.elim0 a
    | gate g hg args ih =>
      by_cases h : g.arity = 0
      · exact ⟨g, hg, h⟩
      · exact ih ⟨0, Nat.pos_of_ne_zero h⟩
  · rintro ⟨g, hg, h⟩
    exact ⟨.gate g hg (fun i => Fin.elim0 (h ▸ i))⟩

end Lemmatheca.MathematicalLogic.FunctionalCompletenessCriterion
