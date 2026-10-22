import Lemmatheca.ElementarySubmodels.ElementarySubmodels
import Lemmatheca.FirstOrderStructures.BasicStructures
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Real.Cardinality

/-! The positive-natural counterexample and a prescribed real-order submodel. -/

namespace Lemmatheca.Entry.ElementarySubmodels

open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic.FirstOrderSyntax
open Lemmatheca.MathematicalLogic.FirstOrderSemantics
open Lemmatheca.ModelTheory.ElementarySubmodels
open Lemmatheca.MathematicalLogic.BasicStructures

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

def integerPiSeed : Set ℝ := Set.range (fun z : ℤ => (z : ℝ)) ∪ {Real.pi}

theorem integerPiSeed_countable : integerPiSeed.Countable := by
  exact (Set.countable_range (fun z : ℤ => (z : ℝ))).union (Set.countable_singleton Real.pi)

/-- The prescribed seed contains the two endpoints but no witness between them. -/
theorem integerPiSeed_gap :
    (0 : ℝ) ∈ integerPiSeed ∧ (1 : ℝ) ∈ integerPiSeed ∧
      (∃ y : ℝ, 0 < y ∧ y < 1) ∧
      ¬ ∃ y ∈ integerPiSeed, 0 < y ∧ y < 1 := by
  refine ⟨Or.inl ⟨0, by simp⟩, Or.inl ⟨1, by simp⟩,
    ⟨1 / 2, by norm_num, by norm_num⟩, ?_⟩
  rintro ⟨y, hy, hpos, hlt⟩
  rcases hy with ⟨z, rfl⟩ | hpi
  · change (0 : ℝ) < (z : ℝ) at hpos
    change (z : ℝ) < 1 at hlt
    have hz : (0 : ℤ) < z := by exact_mod_cast hpos
    have hzone : z < (1 : ℤ) := by exact_mod_cast hlt
    omega
  · have hyeq : y = Real.pi := Set.mem_singleton_iff.mp hpi
    rw [hyeq] at hlt
    exact (not_lt_of_ge Real.two_le_pi) (hlt.trans (by norm_num))

theorem real_order_countable_submodel :
    ∃ S : binaryRelLanguage.ElementarySubstructure ℝ,
      integerPiSeed ⊆ S ∧ Countable S := by
  exact exists_countable_elementarySubstructure integerPiSeed integerPiSeed_countable

/-- A proper elementary inclusion of a countable real-order submodel is not an isomorphism. -/
theorem real_order_countable_proper_submodel :
    ∃ S : binaryRelLanguage.ElementarySubstructure ℝ,
      Countable S ∧ ¬ Function.Surjective (Subtype.val : S → ℝ) := by
  obtain ⟨S, _, hS⟩ := real_order_countable_submodel
  refine ⟨S, hS, ?_⟩
  let : Countable S := hS
  intro h
  have : Countable ℝ := Function.Surjective.countable h
  exact (not_countable (α := ℝ)) this

end Lemmatheca.Entry.ElementarySubmodels
