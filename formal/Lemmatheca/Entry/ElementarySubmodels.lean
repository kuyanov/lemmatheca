import Lemmatheca.MathematicalLogic.ElementarySubmodels
import Lemmatheca.MathematicalLogic.FirstOrderSemantics
import Lemmatheca.Entry.FirstOrderStructures
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-! The positive-natural counterexample and a prescribed real-order submodel. -/

namespace Lemmatheca.Entry.ElementarySubmodels

open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic.FirstOrderSyntax
open Lemmatheca.MathematicalLogic.FirstOrderSemantics
open Lemmatheca.MathematicalLogic.ElementarySubmodels
open Lemmatheca.Entry.FirstOrderStructures

def positiveNaturals : binaryRelLanguage.Substructure ℕ where
  carrier := {n | 0 < n}
  fun_mem f := Empty.elim f

instance : Nonempty positiveNaturals := ⟨⟨1, Nat.zero_lt_one⟩⟩

def hasPredecessor : binaryRelLanguage.Formula (Fin 1) :=
  (strictRel.boundedFormula₂ (.var (.inr 0)) (.var (.inl 0)) :
    binaryRelLanguage.BoundedFormula (Fin 1) 1).ex

theorem natural_one_hasPredecessor : hasPredecessor.Realize (fun _ => (1 : ℕ)) := by
  simp only [hasPredecessor, Formula.Realize, BoundedFormula.realize_ex]
  change ∃ y : ℕ, y < 1
  exact ⟨0, Nat.zero_lt_one⟩

theorem positive_one_noPredecessor :
    ¬ hasPredecessor.Realize (fun _ => (⟨1, Nat.zero_lt_one⟩ : positiveNaturals)) := by
  simp only [hasPredecessor, Formula.Realize, BoundedFormula.realize_ex]
  change ¬ ∃ y : positiveNaturals, (y : ℕ) < 1
  rintro ⟨y, hy⟩
  exact (Nat.not_lt.mpr y.property) hy

theorem positiveNaturals_not_elementary : ¬ positiveNaturals.IsElementary := by
  intro h
  have hφ := h hasPredecessor (fun _ => (⟨1, Nat.zero_lt_one⟩ : positiveNaturals))
  exact positive_one_noPredecessor (hφ.mp natural_one_hasPredecessor)

instance realStrictStructure : binaryRelLanguage.Structure ℝ :=
  binaryRelStructure ℝ (· < ·)

private instance binaryRelSymbols_countable : Countable binaryRelLanguage.Symbols := by
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

def rationalPiSeed : Set ℝ := Set.range (fun q : ℚ => (q : ℝ)) ∪ {Real.pi}

theorem rationalPiSeed_countable : rationalPiSeed.Countable := by
  exact (Set.countable_range (fun q : ℚ => (q : ℝ))).union (Set.countable_singleton Real.pi)

theorem real_order_countable_submodel :
    ∃ S : binaryRelLanguage.ElementarySubstructure ℝ,
      rationalPiSeed ⊆ S ∧ Countable S := by
  exact exists_countable_elementarySubstructure rationalPiSeed rationalPiSeed_countable

end Lemmatheca.Entry.ElementarySubmodels
