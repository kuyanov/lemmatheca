import Lemmatheca.IntuitionisticFirstOrderDeduction.Examples
import Lemmatheca.ArithmeticTheories.ArithmeticTheories

/-! Native constructive arithmetic uses the existing arithmetic language and
terms. Its finite closures retain the full primitive connective constructors. -/
namespace Lemmatheca.ProofTheory.HeytingArithmetic
open _root_.FirstOrder _root_.FirstOrder.Language
universe w w'
open Lemmatheca.ProofTheory.FirstOrder (ScopeSubst liftScope scopeInclusion classicalMap)
open Lemmatheca.ProofTheory.FirstOrder.BoundedFormula
abbrev LA := Lemmatheca.ModelTheory.ArithmeticTheories.language
abbrev BF := Lemmatheca.ProofTheory.FirstOrder.BoundedFormula LA
abbrev Formula := Lemmatheca.ProofTheory.FirstOrder.Formula LA
abbrev Context := Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Context LA
abbrev Sentence := Formula Empty
abbrev zeroTerm := @Lemmatheca.ModelTheory.ArithmeticTheories.zeroTerm
abbrev succTerm := @Lemmatheca.ModelTheory.ArithmeticTheories.succTerm
abbrev addTerm := @Lemmatheca.ModelTheory.ArithmeticTheories.addTerm
abbrev mulTerm := @Lemmatheca.ModelTheory.ArithmeticTheories.mulTerm
abbrev numeral := Lemmatheca.ModelTheory.ArithmeticTheories.numeral
abbrev termEqual := @Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.termEqual LA

variable {α : Type w} {β : Type w'}

/-- Replace the single distinguished free variable by its available bound slot. -/
def bindUnit (A : Formula (α ⊕ Unit)) : BF α 1 :=
  A.map (Sum.elim (fun x => .var (Sum.map id (fun _ => (0 : Fin 1)) x)) Fin.elim0)

def allUnit (A : Formula (α ⊕ Unit)) : Formula α := .all (bindUnit A)
def exUnit (A : Formula (α ⊕ Unit)) : Formula α := .ex (bindUnit A)

/-- Close the newest available slot repeatedly, leaving original names fixed. -/
def allSlots : ∀ {n}, BF α n → Formula α
  | 0, A => A
  | _ + 1, A => allSlots (.all A)

/-- Universal closure in the displayed finite parameter order. -/
def close {k : ℕ} (A : Formula (Fin k)) : Sentence :=
  allSlots (A.map (Sum.elim (fun i => .var (.inr i)) Fin.elim0))

/-- Opening uses a fresh Fin1 tag in the identical original parameter scope. -/
theorem bindUnit_open (A : Formula (α ⊕ Unit)) :
    (bindUnit A).toFormula = A.rename (Sum.map id (fun _ => (0 : Fin 1))) := by
  unfold bindUnit Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.toFormula
    Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.rename
    Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst
  rw [map_comp]
  congr 1
  funext z
  cases z with
  | inl a => cases a <;> rfl
  | inr i => exact i.elim0

theorem bindUnit_instance (A : Formula (α ⊕ Unit)) (t : LA.Term α) :
    (bindUnit A).instantiate t = A.subst (Sum.elim Term.var (fun _ => t)) := by
  unfold bindUnit Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.instantiate
    Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.instantiateSlots
    Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst
  rw [map_comp]
  congr 1
  funext z
  cases z with
  | inl a => cases a <;> rfl
  | inr i => exact i.elim0

theorem allUnit_rename (A : Formula (α ⊕ Unit)) (f : α → β) :
    allUnit (A.rename (Sum.map f id)) = (allUnit A).rename f := by
  unfold allUnit bindUnit
  unfold Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.rename
  rw [subst_all]
  congr 1
  unfold Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst
  rw [map_comp, map_comp]
  congr 1
  funext z
  cases z with
  | inl a => cases a <;> rfl
  | inr i => exact i.elim0

theorem exUnit_rename (A : Formula (α ⊕ Unit)) (f : α → β) :
    exUnit (A.rename (Sum.map f id)) = (exUnit A).rename f := by
  unfold exUnit bindUnit
  unfold Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.rename
  rw [subst_ex]
  congr 1
  unfold Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst
  rw [map_comp, map_comp]
  congr 1
  funext z
  cases z with
  | inl a => cases a <;> rfl
  | inr i => exact i.elim0


/-- The old relabelling and the native scope map use identical bound tags. -/
private theorem classicalMap_relabel {δ ε : Type*} {n k}
    (D : LA.BoundedFormula δ n) (g : δ → ε ⊕ Fin k) :
    classicalMap D (fun z => .var (_root_.FirstOrder.Language.BoundedFormula.relabelAux g n z)) =
      D.relabel g := by
  induction D with
  | falsum => rfl
  | equal s t =>
    simp [classicalMap, _root_.FirstOrder.Language.BoundedFormula.relabel,
      _root_.FirstOrder.Language.BoundedFormula.mapTermRel,
      Lemmatheca.MathematicalLogic.FirstOrderProofs.term_subst_vars]
  | rel R ts =>
    simp [classicalMap, _root_.FirstOrder.Language.BoundedFormula.relabel,
      _root_.FirstOrder.Language.BoundedFormula.mapTermRel,
      Lemmatheca.MathematicalLogic.FirstOrderProofs.term_subst_vars]
  | imp D E ihD ihE => simp [classicalMap, ihD, ihE]
  | @all n D ih =>
    simp only [classicalMap, _root_.FirstOrder.Language.BoundedFormula.relabel_all]
    rw [← ih]
    congr 1
    apply congrArg (classicalMap D)
    funext z
    cases z with
    | inl a =>
      cases h : g a with
      | inl b => simp [liftScope, scopeInclusion,
          _root_.FirstOrder.Language.BoundedFormula.relabelAux, h, Term.relabel]
      | inr i =>
        simp [liftScope, scopeInclusion,
          _root_.FirstOrder.Language.BoundedFormula.relabelAux, h, Term.relabel]
        rfl
    | inr i =>
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [liftScope, _root_.FirstOrder.Language.BoundedFormula.relabelAux]
      · simp [liftScope, scopeInclusion,
          _root_.FirstOrder.Language.BoundedFormula.relabelAux, Term.relabel]

private theorem complete_classicalMap_relabel {δ ε : Type*} {k}
    (D : LA.Formula δ) (g : δ → ε ⊕ Fin k) :
    classicalMap D (Sum.elim (fun a => .var (g a)) Fin.elim0) = _root_.FirstOrder.Language.BoundedFormula.relabel g D := by
  rw [← classicalMap_relabel D g]
  congr 1
  funext z
  cases z with
  | inl a =>
    cases h : g a with
    | inl b => simp [_root_.FirstOrder.Language.BoundedFormula.relabelAux, h]
    | inr i =>
      simp [_root_.FirstOrder.Language.BoundedFormula.relabelAux, h]
      rfl
  | inr i => exact i.elim0

private theorem unit_exs (D : LA.Formula (α ⊕ Unit)) {n} (e : Unit ≃ Fin n) :
    (_root_.FirstOrder.Language.BoundedFormula.relabel (Sum.map id e) D).exs =
      (_root_.FirstOrder.Language.BoundedFormula.relabel (Sum.elim Sum.inl (fun _ => Sum.inr (0 : Fin 1))) D).ex := by
  have hn : n = 1 := by simpa using (Fintype.card_congr e).symm
  subst n
  have he : Sum.map (id : α → α) e =
      Sum.elim Sum.inl (fun _ : Unit => Sum.inr (0 : Fin 1)) := by
    funext z
    cases z with
    | inl a => rfl
    | inr u => exact congrArg Sum.inr (Subsingleton.elim _ _)
  rw [he]
  rfl

/-- These identities concern the existing small classical formula constructors. -/
theorem allSlots_toClassical {n} (A : BF α n) :
    (allSlots A).toClassical = A.toClassical.alls := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih (.all A)

theorem close_toClassical {k} (A : Formula (Fin k)) :
    (close A).toClassical = Lemmatheca.ModelTheory.ArithmeticTheories.close A.toClassical := by
  unfold close
  rw [allSlots_toClassical, toClassical_map]
  rw [complete_classicalMap_relabel]
  rfl

theorem allUnit_toClassical (A : Formula (α ⊕ Unit)) :
    (allUnit A).toClassical = Lemmatheca.ModelTheory.ArithmeticTheories.allUnit A.toClassical := by
  unfold allUnit bindUnit
  rw [toClassical, toClassical_map]
  rw [complete_classicalMap_relabel]
  rfl

theorem exUnit_toClassical (A : Formula (α ⊕ Unit)) :
    (exUnit A).toClassical = _root_.FirstOrder.Language.Formula.iExs Unit A.toClassical := by
  unfold exUnit bindUnit
  rw [toClassical, toClassical_map]
  rw [complete_classicalMap_relabel]
  exact (unit_exs A.toClassical
    (Classical.choice (Classical.choose_spec (Finite.exists_equiv_fin Unit)))).symm

end Lemmatheca.ProofTheory.HeytingArithmetic
