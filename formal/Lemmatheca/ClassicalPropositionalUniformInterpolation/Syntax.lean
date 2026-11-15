import Lemmatheca.PropositionalProofs.Deduction
import Lemmatheca.CraigInterpolation.Examples

/-! Finite Boolean projection on the existing native propositional syntax. -/
namespace Lemmatheca.ProofTheory.ClassicalPropositional.UniformInterpolation

open Lemmatheca.MathematicalLogic.Propositional
open PropFormula

universe u
variable {α : Type u} [DecidableEq α]

/-- Replace precisely the selected atom by the specified Boolean constant. -/
def constantInstance (p : α) (b : Bool) (A : PropFormula α) : PropFormula α :=
  subst (fun q => if q = p then (if b then verum else falsum) else atom q) A

/-- The computable two-branch existential projection. -/
def existsAtom (p : α) (A : PropFormula α) : PropFormula α :=
  disj (constantInstance p false A) (constantInstance p true A)

/-- The corresponding two-branch universal projection. -/
def forallAtom (p : α) (A : PropFormula α) : PropFormula α :=
  conj (constantInstance p false A) (constantInstance p true A)

/-- A finite list gives a specified formula, before any future conclusion is known. -/
def existsList : List α → PropFormula α → PropFormula α
  | [], A => A
  | p :: L, A => existsAtom p (existsList L A)

/-- Iterate the universal projection in the same list convention. -/
def forallList : List α → PropFormula α → PropFormula α
  | [], A => A
  | p :: L, A => forallAtom p (forallList L A)

/-- Agreement is required at every atom outside the forgotten set. -/
def AgreeOutside (F : Finset α) (w v : Valuation α) : Prop :=
  ∀ q, q ∉ F → w q = v q

/-- The fixed middle formula captures every consequence with no private source atoms. -/
def Uniform (A : PropFormula α) (S : Finset α) (I : PropFormula α) : Prop :=
  Entails {A} I ∧ atoms I ⊆ S ∧
    ∀ B : PropFormula α, atoms B ∩ atoms A ⊆ S → Entails {A} B → Entails {I} B

/-- This implementation agrees exactly with the earlier classical forgetting definition. -/
theorem existsAtom_eq_existing (p : α) (A : PropFormula α) :
    existsAtom p A = Lemmatheca.Entry.CraigInterpolation.forgetAtom p A := by
  unfold existsAtom constantInstance Lemmatheca.Entry.CraigInterpolation.forgetAtom
  simp only [Bool.false_eq_true, ite_false, ite_true]
  congr 1
  all_goals
    congr 1
    funext q
    by_cases h : q = p <;> simp [h]

/-- Constant substitution evaluates at exactly the updated valuation. -/
theorem constantInstance_eval (p : α) (b : Bool) (A : PropFormula α) (v : Valuation α) :
    eval v (constantInstance p b A) = eval (Function.update v p b) A := by
  rw [constantInstance, eval_subst]
  congr 1
  funext q
  by_cases h : q = p
  · subst q
    cases b <;> simp [eval, verum]
  · simp [h, eval]

/-- The substitution removes the selected atom and introduces no other atom. -/
theorem constantInstance_support (p : α) (b : Bool) (A : PropFormula α) :
    atoms (constantInstance p b A) ⊆ atoms A \ {p} := by
  induction A with
  | atom q =>
    by_cases h : q = p
    · subst q
      cases b <;> simp [constantInstance, subst, atoms, verum]
    · simp [constantInstance, subst, h, atoms]
  | falsum => simp [constantInstance, subst, atoms]
  | neg A ih => simpa [constantInstance, subst, atoms] using ih
  | conj A B ihA ihB | disj A B ihA ihB | impl A B ihA ihB =>
    simp only [constantInstance, subst, atoms] at *
    intro q hq
    rcases Finset.mem_union.mp hq with hq | hq
    · have h := Finset.mem_sdiff.mp (ihA hq)
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_union_left _ h.1, h.2⟩
    · have h := Finset.mem_sdiff.mp (ihB hq)
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_union_right _ h.1, h.2⟩

/-- Both single-atom formulas satisfy the exact stated support bound. -/
theorem atom_support (p : α) (A : PropFormula α) :
    atoms (existsAtom p A) ⊆ atoms A \ {p} ∧
      atoms (forallAtom p A) ⊆ atoms A \ {p} := by
  constructor <;> intro q hq
  all_goals
    change q ∈ atoms (constantInstance p false A) ∪
      atoms (constantInstance p true A) at hq
    rcases Finset.mem_union.mp hq with hq | hq
    · exact constantInstance_support p false A hq
    · exact constantInstance_support p true A hq

end Lemmatheca.ProofTheory.ClassicalPropositional.UniformInterpolation
