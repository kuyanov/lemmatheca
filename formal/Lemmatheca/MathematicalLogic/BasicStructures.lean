import Lemmatheca.MathematicalLogic.FirstOrderSemantics
import Mathlib.Basic.Real.Basic

/-! Shared zero/successor syntax and the usual binary-order structures. -/

namespace Lemmatheca.MathematicalLogic.BasicStructures

open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic.FirstOrderSyntax
open Lemmatheca.MathematicalLogic.FirstOrderSemantics

/-- The constant zero and a unary successor symbol. -/
inductive NaturalFunctionSymbol : ℕ → Type
  | zero : NaturalFunctionSymbol 0
  | succ : NaturalFunctionSymbol 1

/-- The language with zero and successor, and no relation symbols. -/
def naturalSuccessorLanguage : Language := ⟨NaturalFunctionSymbol, fun _ => Empty⟩

private instance countableNaturalFunctions : Countable (Σ n, NaturalFunctionSymbol n) := by
  refine Function.Injective.countable (f := fun p : Σ n, NaturalFunctionSymbol n =>
    match p with | ⟨_, .zero⟩ => false | ⟨_, .succ⟩ => true) ?_
  intro a b h
  obtain ⟨_, a⟩ := a
  obtain ⟨_, b⟩ := b
  cases a <;> cases b <;> simp_all

instance naturalSuccessorSymbols_countable : Countable naturalSuccessorLanguage.Symbols := by
  change Countable ((Σ n, NaturalFunctionSymbol n) ⊕ (Σ _ : ℕ, Empty))
  infer_instance

/-- Interpret zero and successor in the natural numbers. -/
instance naturalSuccessorStructure : naturalSuccessorLanguage.Structure ℕ where
  funMap f ts := match f with
    | .zero => 0
    | .succ => ts 0 + 1
  RelMap r _ := r.elim

/-- The closed term obtained by applying successor to zero repeatedly. -/
def numeral : ℕ → naturalSuccessorLanguage.Term Empty
  | 0 => .func .zero Fin.elim0
  | n + 1 => .func .succ (fun _ => numeral n)

theorem numeral_value (n : ℕ) : (numeral n).realize Empty.elim = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (numeral n).realize Empty.elim + 1 = n + 1
    rw [ih]

/-- The unique binary relation symbol of the relation-only language. -/
def strictRel : binaryRelLanguage.Relations 2 := .rel

instance binaryRelSymbols_countable : Countable binaryRelLanguage.Symbols := by
  apply Function.Injective.countable (f := fun _ : binaryRelLanguage.Symbols => ())
  intro x y _
  cases x with
  | inl x => exact Empty.elim x.2
  | inr x =>
    rcases x with ⟨n, r⟩
    cases r
    cases y with
    | inl y => exact Empty.elim y.2
    | inr y =>
      rcases y with ⟨n, r⟩
      cases r
      rfl

/-- Interpret the binary relation by the usual strict natural-number order. -/
instance natStrictStructure : binaryRelLanguage.Structure ℕ :=
  binaryRelStructure ℕ (· < ·)

/-- Interpret the binary relation by the usual strict real-number order. -/
instance realStrictStructure : binaryRelLanguage.Structure ℝ :=
  binaryRelStructure ℝ (· < ·)

/-- The empty domain carries the empty language. -/
instance emptyStructure : Language.empty.Structure Empty where

end Lemmatheca.MathematicalLogic.BasicStructures
