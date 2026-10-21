import Mathlib.ModelTheory.Semantics
import Lemmatheca.FirstOrderLanguages.FirstOrderSyntax

/-! Evaluation, free support, and elementary boundary cases of first-order semantics. -/

namespace Lemmatheca.MathematicalLogic.FirstOrderSemantics

open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic.FirstOrderSyntax

universe u v w u' v'

variable {L : Language.{u, v}} {M : Type w} [L.Structure M]
variable {α : Type u'} {β : Type v'} {n : ℕ}

theorem term_realize_agree [DecidableEq α] (t : L.Term α) (a a' : α → M)
    (h : ∀ x ∈ t.varFinset, a x = a' x) : t.realize a = t.realize a' := by
  induction t with
  | var x => exact h x (Finset.mem_singleton_self x)
  | func f ts ih =>
    simp only [Term.realize]
    congr 1
    funext i
    apply ih i
    intro x hx
    exact h x (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hx⟩)

theorem scopedTerm_realize_agree [DecidableEq α] (t : L.Term (α ⊕ Fin n))
    (a a' : α → M) (b : Fin n → M)
    (h : ∀ x ∈ t.varFinsetLeft, a x = a' x) :
    t.realize (Sum.elim a b) = t.realize (Sum.elim a' b) := by
  induction t with
  | var x =>
    cases x with
    | inl x => exact h x (Finset.mem_singleton_self x)
    | inr i => rfl
  | func f ts ih =>
    simp only [Term.realize]
    congr 1
    funext i
    apply ih i
    intro x hx
    exact h x (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hx⟩)

theorem formula_realize_agree [DecidableEq α] (φ : L.BoundedFormula α n)
    (a a' : α → M) (b : Fin n → M)
    (h : ∀ x ∈ φ.freeVarFinset, a x = a' x) :
    φ.Realize a b ↔ φ.Realize a' b := by
  let v : φ.freeVarFinset → M := fun x => a x
  have ha := BoundedFormula.realize_restrictFreeVar (φ := φ) (f := id)
    (v := v) (xs := b) a (fun _ => rfl)
  have ha' := BoundedFormula.realize_restrictFreeVar (φ := φ) (f := id)
    (v := v) (xs := b) a' (fun x => h x x.property)
  exact ha.symm.trans ha'

theorem formula_realize_noFreeVar [DecidableEq α] (φ : L.Formula α)
    (h : φ.freeVarFinset = ∅) (a a' : α → M) :
    φ.Realize a ↔ φ.Realize a' := by
  apply formula_realize_agree φ a a' default
  intro x hx
  rw [h] at hx
  exact (Finset.notMem_empty x hx).elim

theorem sentenceOfNoFreeVar_realize [DecidableEq α] (φ : L.Formula α)
    (h : φ.freeVarFinset = ∅) (a : α → M) :
    M ⊨ sentenceOfNoFreeVar φ h ↔ φ.Realize a := by
  exact BoundedFormula.realize_restrictFreeVar a
    (fun x => (Finset.notMem_empty x.val (h ▸ x.property)).elim)

theorem noFreeVar_realize_all_iff [Nonempty M] [DecidableEq α] (φ : L.Formula α)
    (h : φ.freeVarFinset = ∅) (a : α → M) :
    (∀ a' : α → M, φ.Realize a') ↔ φ.Realize a := by
  constructor
  · exact fun hall => hall a
  · intro ha a'
    exact (formula_realize_noFreeVar φ h a a').mp ha

theorem noFreeVar_realize_exists_iff [Nonempty M] [DecidableEq α] (φ : L.Formula α)
    (h : φ.freeVarFinset = ∅) (a : α → M) :
    (∃ a' : α → M, φ.Realize a') ↔ φ.Realize a := by
  constructor
  · rintro ⟨a', ha'⟩
    exact (formula_realize_noFreeVar φ h a' a).mp ha'
  · exact fun ha => ⟨a, ha⟩

theorem scopedTermSubst_realize (t : L.Term (α ⊕ Fin n))
    (σ : α → L.Term β) (a : β → M) (b : Fin n → M) :
    (scopedTermSubst t σ).realize (Sum.elim a b) =
      t.realize (Sum.elim (fun x => (σ x).realize a) b) := by
  rw [scopedTermSubst, Term.realize_subst]
  congr 1
  funext x
  cases x with
  | inl x => exact Term.realize_relabel
  | inr i => rfl

theorem singleSubst_assignment [DecidableEq α] (t : L.Term α) (x : α) (a : α → M) :
    (fun y => ((if y = x then t else .var y) : L.Term α).realize a) =
      Function.update a x (t.realize a) := by
  funext y
  by_cases hy : y = x
  · subst y
    simp
  · simp [hy]

/-- Interpret the one binary relation by any supplied relation. -/
@[instance_reducible]
def binaryRelStructure (M : Type w) (r : M → M → Prop) : binaryRelLanguage.Structure M where
  funMap f := Empty.elim f
  RelMap := fun s a => match s with
    | .rel => r (a 0) (a 1)

/-- The sentence asserting that the domain contains a self-equal element. -/
def existsSelfEqual (L : Language.{u, v}) : L.Sentence :=
  (BoundedFormula.equal (.var (.inr 0)) (.var (.inr 0)) : L.BoundedFormula Empty 1).ex

/-- The sentence asserting that every domain element equals itself. -/
def allSelfEqual (L : Language.{u, v}) : L.Sentence :=
  (BoundedFormula.equal (.var (.inr 0)) (.var (.inr 0)) : L.BoundedFormula Empty 1).all

theorem existsSelfEqual_realize : M ⊨ existsSelfEqual L ↔ Nonempty M := by
  simp [Sentence.Realize, Formula.Realize, existsSelfEqual, BoundedFormula.Realize,
    Term.realize]

theorem allSelfEqual_realize : M ⊨ allSelfEqual L := by
  simp [Sentence.Realize, Formula.Realize, allSelfEqual, BoundedFormula.Realize,
    Term.realize]

/-- The sentence asserting that all pairs of elements are equal. -/
def allPairEqual (L : Language.{u, v}) : L.Sentence :=
  ((BoundedFormula.equal (.var (.inr 0)) (.var (.inr 1)) :
    L.BoundedFormula Empty 2).all).all

theorem allPairEqual_realize : M ⊨ allPairEqual L ↔ Subsingleton M := by
  change (∀ a b : M, a = b) ↔ Subsingleton M
  exact ⟨fun h => ⟨h⟩, fun h => h.elim⟩

theorem contradictoryTheory_not_model (θ : L.Sentence) :
    ¬ M ⊨ ({θ, θ.not} : L.Theory) := by
  intro h
  have hθ := h.realize_of_mem θ (by simp)
  have hnθ := h.realize_of_mem θ.not (by simp)
  exact hnθ hθ

end Lemmatheca.MathematicalLogic.FirstOrderSemantics

namespace Lemmatheca.MathematicalLogic.FirstOrderProofs

open FirstOrder FirstOrder.Language

universe u v w
variable {L : Language.{u, v}} {α : Type w}

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

end Lemmatheca.MathematicalLogic.FirstOrderProofs
