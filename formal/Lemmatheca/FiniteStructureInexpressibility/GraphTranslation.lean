import Lemmatheca.FiniteRoundComparison.NativeSyntax
import Lemmatheca.ExpressiveLimits.ExpressiveLimits

/-! Native relation-formula substitution for the cyclic-distance-two graph interpretation. -/

namespace Lemmatheca.ModelTheory.FiniteStructureInexpressibility

open FirstOrder FirstOrder.Language
open Lemmatheca.ModelTheory.FiniteRoundComparison

variable {α : Type} {n : ℕ}

def edgeFormula (t u : ExpressiveLimits.language.Term (α ⊕ Fin n)) : ExpressiveLimits.language.BoundedFormula α n :=
  .rel ExpressiveLimits.edgeSymbol ![t, u]

def liftTerm (t : ExpressiveLimits.language.Term (α ⊕ Fin n)) : ExpressiveLimits.language.Term (α ⊕ Fin (n + 1)) :=
  t.relabel (Sum.map id Fin.castSucc)

/-- Ordinary strict successor, with a fresh last slot for the point excluded from the interval. -/
def successorFormula (t u : ExpressiveLimits.language.Term (α ⊕ Fin n)) : ExpressiveLimits.language.BoundedFormula α n :=
  edgeFormula t u ⊓
    (edgeFormula (liftTerm t) (.var (.inr (Fin.last n))) ⊓
      edgeFormula (.var (.inr (Fin.last n))) (liftTerm u)).ex.not

def minimumFormula (t : ExpressiveLimits.language.Term (α ⊕ Fin n)) : ExpressiveLimits.language.BoundedFormula α n :=
  (edgeFormula (.var (.inr (Fin.last n))) (liftTerm t)).ex.not

def maximumFormula (t : ExpressiveLimits.language.Term (α ⊕ Fin n)) : ExpressiveLimits.language.BoundedFormula α n :=
  (edgeFormula (liftTerm t) (.var (.inr (Fin.last n)))).ex.not

def cyclicSuccessorFormula (t u : ExpressiveLimits.language.Term (α ⊕ Fin n)) :
    ExpressiveLimits.language.BoundedFormula α n :=
  successorFormula t u ⊔ (maximumFormula t ⊓ minimumFormula u)

def twoStepFormula (t u : ExpressiveLimits.language.Term (α ⊕ Fin n)) : ExpressiveLimits.language.BoundedFormula α n :=
  (cyclicSuccessorFormula (liftTerm t) (.var (.inr (Fin.last n))) ⊓
    cyclicSuccessorFormula (.var (.inr (Fin.last n))) (liftTerm u)).ex

def graphEdgeFormula (t u : ExpressiveLimits.language.Term (α ⊕ Fin n)) : ExpressiveLimits.language.BoundedFormula α n :=
  twoStepFormula t u ⊔ twoStepFormula u t

/-- The semantic cyclic successor in an arbitrary source binary relation. -/
def CyclicSuccessor {M : Type} (r : M → M → Prop) (a b : M) : Prop :=
  (r a b ∧ ¬ ∃ c, r a c ∧ r c b) ∨ ((¬ ∃ c, r a c) ∧ ¬ ∃ c, r c b)

def GraphEdge {M : Type} (r : M → M → Prop) (a b : M) : Prop :=
  (∃ c, CyclicSuccessor r a c ∧ CyclicSuccessor r c b) ∨
    (∃ c, CyclicSuccessor r b c ∧ CyclicSuccessor r c a)

theorem defining_formula_ranks (t u : ExpressiveLimits.language.Term (α ⊕ Fin n)) :
    quantifierRank (successorFormula t u) = 1 ∧
    quantifierRank (minimumFormula t) = 1 ∧
    quantifierRank (maximumFormula t) = 1 ∧
    quantifierRank (cyclicSuccessorFormula t u) = 1 ∧
    quantifierRank (twoStepFormula t u) = 2 ∧
    quantifierRank (graphEdgeFormula t u) = 2 := by
  simp only [graphEdgeFormula, twoStepFormula, cyclicSuccessorFormula,
    successorFormula, maximumFormula, minimumFormula, edgeFormula, quantifierRank_sup,
    quantifierRank_inf, quantifierRank]
  decide

private theorem liftTerm_realize {M : Type} (r : M → M → Prop)
    (t : ExpressiveLimits.language.Term (α ⊕ Fin n)) (v : α → M) (a : Fin n → M) (c : M) :
    @Term.realize ExpressiveLimits.language M
      (ExpressiveLimits.relationStructure r) (α ⊕ Fin (n + 1)) (Sum.elim v (Fin.snoc a c)) (liftTerm t) =
    @Term.realize ExpressiveLimits.language M
      (ExpressiveLimits.relationStructure r) (α ⊕ Fin n) (Sum.elim v a) t := by
  let := ExpressiveLimits.relationStructure r
  rw [liftTerm, Term.realize_relabel]
  congr 1
  funext x
  cases x with
  | inl x => rfl
  | inr x => simp

private theorem term_structure_independent {M : Type} (r s : M → M → Prop)
    (t : ExpressiveLimits.language.Term α) (v : α → M) :
    @Term.realize ExpressiveLimits.language M (ExpressiveLimits.relationStructure r) α v t =
      @Term.realize ExpressiveLimits.language M (ExpressiveLimits.relationStructure s) α v t := by
  cases t with
  | var x => rfl
  | func f _ => exact f.elim

private theorem edgeFormula_realize {M : Type} (r : M → M → Prop)
    (t u : ExpressiveLimits.language.Term (α ⊕ Fin n)) (v : α → M) (a : Fin n → M) :
    @BoundedFormula.Realize ExpressiveLimits.language M (ExpressiveLimits.relationStructure r) α n
      (edgeFormula t u) v a ↔
      r (@Term.realize ExpressiveLimits.language M (ExpressiveLimits.relationStructure r)
          (α ⊕ Fin n) (Sum.elim v a) t)
        (@Term.realize ExpressiveLimits.language M (ExpressiveLimits.relationStructure r)
          (α ⊕ Fin n) (Sum.elim v a) u) := Iff.rfl

theorem cyclicSuccessorFormula_realize {M : Type} (r : M → M → Prop)
    (t u : ExpressiveLimits.language.Term (α ⊕ Fin n)) (v : α → M) (a : Fin n → M) :
    @BoundedFormula.Realize ExpressiveLimits.language M (ExpressiveLimits.relationStructure r) α n
      (cyclicSuccessorFormula t u) v a ↔
      CyclicSuccessor r
        (@Term.realize ExpressiveLimits.language M (ExpressiveLimits.relationStructure r) (α ⊕ Fin n) (Sum.elim v a) t)
        (@Term.realize ExpressiveLimits.language M (ExpressiveLimits.relationStructure r) (α ⊕ Fin n) (Sum.elim v a) u) := by
  let := ExpressiveLimits.relationStructure r
  simp only [cyclicSuccessorFormula, successorFormula, maximumFormula, minimumFormula,
    BoundedFormula.realize_sup, BoundedFormula.realize_inf, BoundedFormula.realize_not,
    BoundedFormula.realize_ex, edgeFormula_realize, liftTerm_realize,
    Term.realize_var, Sum.elim_inr, Fin.snoc_last]
  rfl

theorem graphEdgeFormula_realize {M : Type} (r : M → M → Prop)
    (t u : ExpressiveLimits.language.Term (α ⊕ Fin n)) (v : α → M) (a : Fin n → M) :
    @BoundedFormula.Realize ExpressiveLimits.language M (ExpressiveLimits.relationStructure r) α n
      (graphEdgeFormula t u) v a ↔
      GraphEdge r
        (@Term.realize ExpressiveLimits.language M (ExpressiveLimits.relationStructure r) (α ⊕ Fin n) (Sum.elim v a) t)
        (@Term.realize ExpressiveLimits.language M (ExpressiveLimits.relationStructure r) (α ⊕ Fin n) (Sum.elim v a) u) := by
  let := ExpressiveLimits.relationStructure r
  simp only [graphEdgeFormula, twoStepFormula, BoundedFormula.realize_sup,
    BoundedFormula.realize_ex, BoundedFormula.realize_inf, cyclicSuccessorFormula_realize,
    liftTerm_realize, Term.realize_var, Sum.elim_inr, Fin.snoc_last]
  rfl

/-- Replace each actual native edge occurrence by its defining order formula. -/
def graphTranslation : {n : ℕ} → ExpressiveLimits.language.BoundedFormula α n → ExpressiveLimits.language.BoundedFormula α n
  | _, .falsum => .falsum
  | _, .equal t u => .equal t u
  | _, .rel .edge ts => graphEdgeFormula (ts 0) (ts 1)
  | _, .imp φ ψ => (graphTranslation φ).imp (graphTranslation ψ)
  | _, .all φ => (graphTranslation φ).all

theorem graphTranslation_realize {M : Type} (r : M → M → Prop)
    (φ : ExpressiveLimits.language.BoundedFormula α n) (v : α → M) (a : Fin n → M) :
    @BoundedFormula.Realize ExpressiveLimits.language M (ExpressiveLimits.relationStructure (GraphEdge r)) α n φ v a ↔
      @BoundedFormula.Realize ExpressiveLimits.language M (ExpressiveLimits.relationStructure r) α n
        (graphTranslation φ) v a := by
  induction φ with
  | falsum => rfl
  | equal t u =>
    change (_ = _) ↔ (_ = _)
    rw [term_structure_independent (GraphEdge r) r,
      term_structure_independent (GraphEdge r) r]
  | rel R ts =>
    cases R
    change GraphEdge r _ _ ↔ @BoundedFormula.Realize ExpressiveLimits.language M
      (ExpressiveLimits.relationStructure r) _ _ (graphEdgeFormula (ts 0) (ts 1)) v a
    rw [graphEdgeFormula_realize]
    simp only [term_structure_independent (GraphEdge r) r]
  | imp φ ψ ihφ ihψ => exact imp_congr (ihφ a) (ihψ a)
  | all φ ih =>
    simp only [graphTranslation, BoundedFormula.realize_all]
    exact forall_congr' fun c => ih (Fin.snoc a c)

theorem graphTranslation_rank (φ : ExpressiveLimits.language.BoundedFormula α n) :
    quantifierRank (graphTranslation φ) ≤ quantifierRank φ + 2 := by
  induction φ with
  | falsum => simp [graphTranslation, quantifierRank]
  | equal t u => simp [graphTranslation, quantifierRank]
  | rel R ts =>
    cases R
    simp only [graphTranslation, graphEdgeFormula, twoStepFormula, cyclicSuccessorFormula,
      successorFormula, maximumFormula, minimumFormula, edgeFormula, quantifierRank_sup,
      quantifierRank_inf, quantifierRank]
    decide
  | imp φ ψ ihφ ihψ =>
    change max _ _ ≤ max _ _ + 2
    exact max_le (ihφ.trans (Nat.add_le_add_right (le_max_left _ _) 2))
      (ihψ.trans (Nat.add_le_add_right (le_max_right _ _) 2))
  | all φ ih => exact Nat.add_le_add_right ih 1

end Lemmatheca.ModelTheory.FiniteStructureInexpressibility
