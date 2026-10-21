import Lemmatheca.DefinabilityAndAutomorphisms.Definability
import Lemmatheca.FirstOrderStructures.BasicStructures

/-! Real-order translations and the rigid natural-number zero/successor example. -/

namespace Lemmatheca.Entry.DefinabilityAndAutomorphisms

open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic.FirstOrderSyntax
open Lemmatheca.MathematicalLogic.FirstOrderSemantics
open Lemmatheca.ModelTheory.Definability
open Lemmatheca.MathematicalLogic.BasicStructures

def positiveRay : Set ℝ := {x | 0 < x}

def realTranslation (c : ℝ) : ℝ ≃[binaryRelLanguage] ℝ where
  toEquiv :=
    { toFun := fun x => x + c
      invFun := fun x => x - c
      left_inv := fun x => by simp
      right_inv := fun x => by simp }
  map_fun' f := Empty.elim f
  map_rel' r x := by cases r; exact add_lt_add_iff_right c

theorem positiveRay_definable_with_zero :
    ({0} : Set ℝ).Definable₁ binaryRelLanguage positiveRay := by
  refine ⟨Relations.formula₂ (L := binaryRelLanguage[[( {0} : Set ℝ)]])
    (Sum.inl BinaryRelationSymbol.rel)
      ((binaryRelLanguage.con (⟨0, by simp⟩ : ↑({0} : Set ℝ))).term) (Term.var 0), ?_⟩
  ext x
  rfl

theorem translation_moves_positiveRay :
    (1 : ℝ) ∈ positiveRay ∧ realTranslation (-2) 1 ∉ positiveRay := by
  change (0 : ℝ) < 1 ∧ ¬ (0 : ℝ) < 1 + (-2)
  norm_num

theorem positiveRay_not_parameterFree :
    ¬ (∅ : Set ℝ).Definable₁ binaryRelLanguage positiveRay := by
  intro h
  have hi := definable_invariant h (realTranslation (-2)) (by simp [Fixes])
  have hx := (hi (fun _ : Fin 1 => (1 : ℝ))).mp translation_moves_positiveRay.1
  exact translation_moves_positiveRay.2 hx

theorem naturalSuccessor_rigid (g : ℕ ≃[naturalSuccessorLanguage] ℕ) :
    ∀ n, g n = n := by
  intro n
  induction n with
  | zero =>
    have h := g.map_fun NaturalFunctionSymbol.zero (fun i => Fin.elim0 i)
    exact h
  | succ n ih =>
    have h := g.map_fun NaturalFunctionSymbol.succ (fun _ => n)
    change g (n + 1) = g n + 1 at h
    simpa only [ih] using h

theorem invariant_undefinable_natural_subset :
    ∃ s : Set ℕ, (¬ (Set.univ : Set ℕ).Definable₁ naturalSuccessorLanguage s) ∧
      ∀ g : ℕ ≃[naturalSuccessorLanguage] ℕ,
        Invariant g {x : Fin 1 → ℕ | x 0 ∈ s} := by
  obtain ⟨s, hs⟩ := exists_undefinable_subset (L := naturalSuccessorLanguage) (M := ℕ)
  refine ⟨s, hs, ?_⟩
  intro g x
  change x 0 ∈ s ↔ g (x 0) ∈ s
  rw [naturalSuccessor_rigid g (x 0)]

end Lemmatheca.Entry.DefinabilityAndAutomorphisms
