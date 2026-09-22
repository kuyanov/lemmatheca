import Lemmatheca.Entry.SetsAndMaps
import Lemmatheca.SetTheory.EquivalenceRelations
import Mathlib.Data.Int.ModEq
import Mathlib.Algebra.Ring.Int.Parity

/-!
# Equivalence-relations entry: finite and parity examples

`Fin 3` represents {0, 1, 2}; the map and output labels are shared with the
sets-and-maps entry. Parity is the kernel of reduction modulo two. The helper
abbreviations introduce no new mathematical objects beyond these library instances.
All new theorem bodies remain pending until correspondence review.
-/

namespace Lemmatheca.Entry.EquivalenceRelations

open Lemmatheca.Entry.SetsAndMaps

abbrev finiteSetoid : Setoid (Fin 3) := Setoid.ker diagramMap
abbrev paritySetoid : Setoid ℤ := Setoid.ker (fun n : ℤ => n % 2)

theorem finite_relation_iff (a b : Fin 3) :
    finiteSetoid a b ↔ (a = 0 ∧ b = 0) ∨
      (a ∈ ({1, 2} : Set (Fin 3)) ∧ b ∈ ({1, 2} : Set (Fin 3))) := by sorry

theorem parity_distinct_equivalent :
    Int.ModEq 2 (-1) 3 ∧ (-1 : ℤ) ≠ 3 := by sorry

theorem empty_relation_not_reflexive :
    Std.Symm (fun _ _ : Fin 3 => False) ∧
      IsTrans (Fin 3) (fun _ _ : Fin 3 => False) ∧
      ¬ Std.Refl (fun _ _ : Fin 3 => False) := by sorry

theorem le_relation_not_symmetric :
    Std.Refl ((· ≤ ·) : Fin 3 → Fin 3 → Prop) ∧
      IsTrans (Fin 3) ((· ≤ ·) : Fin 3 → Fin 3 → Prop) ∧
      (0 : Fin 3) ≤ 1 ∧ ¬ (1 : Fin 3) ≤ 0 := by sorry

/-- The looped path 0—1—2 used to test transitivity. -/
def adjacent (a b : Fin 3) : Prop :=
  a = b ∨ (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) ∨
    (a = 1 ∧ b = 2) ∨ (a = 2 ∧ b = 1)

theorem adjacent_not_transitive :
    Std.Refl adjacent ∧ Std.Symm adjacent ∧
      adjacent 0 1 ∧ adjacent 1 2 ∧ ¬ adjacent 0 2 ∧
      {x | adjacent 0 x} = {0, 1} ∧ {x | adjacent 2 x} = {1, 2} := by sorry

theorem finite_classes :
    {x | finiteSetoid x 0} = {0} ∧
      {x | finiteSetoid x 1} = {1, 2} ∧
      {x | finiteSetoid x 2} = {1, 2} ∧
      finiteSetoid.classes = {{0}, {1, 2}} := by sorry

theorem parity_classes :
    (∀ n : ℤ, {x | paritySetoid x n} =
      if Even n then Set.range (fun k : ℤ => 2 * k)
      else Set.range (fun k : ℤ => 2 * k + 1)) ∧
      paritySetoid.classes =
        {Set.range (fun k : ℤ => 2 * k), Set.range (fun k : ℤ => 2 * k + 1)} ∧
      Set.range (fun k : ℤ => 2 * k) ≠ Set.range (fun k : ℤ => 2 * k + 1) := by sorry

theorem parity_classes_infinite :
    (Set.range (fun k : ℤ => 2 * k)).Infinite ∧
      (Set.range (fun k : ℤ => 2 * k + 1)).Infinite := by sorry

theorem overlapping_parts_not_partition :
    ¬ Setoid.IsPartition ({{0, 1}, {1, 2}} : Set (Set (Fin 3))) ∧
      ({0, 1} : Set (Fin 3)) ∩ {1, 2} = {1} := by sorry

theorem missing_part_not_partition :
    ¬ Setoid.IsPartition ({{0}, {1}} : Set (Set (Fin 3))) ∧
      (2 : Fin 3) ∉ ⋃₀ ({{0}, {1}} : Set (Set (Fin 3))) := by sorry

theorem parity_identity_not_descend :
    Quotient.mk paritySetoid 0 = Quotient.mk paritySetoid 2 ∧
      (0 : ℤ) ≠ 2 ∧
      ¬ ∃ u : Quotient paritySetoid → ℤ, ∀ n, u (Quotient.mk paritySetoid n) = n := by sorry

/-- The proposed parity label, with the specified two-element codomain. -/
def parityLabel (n : ℤ) : Fin 2 := if Even n then 0 else 1

theorem parity_label_descends :
    ∃ v : Quotient paritySetoid → Fin 2,
      (∀ n, v (Quotient.mk paritySetoid n) = parityLabel n) ∧
      v (Quotient.mk paritySetoid 0) = 0 ∧ v (Quotient.mk paritySetoid 1) = 1 := by sorry

theorem parity_successor_descends :
    ∃ s : Quotient paritySetoid → Quotient paritySetoid,
      (∀ n, s (Quotient.mk paritySetoid n) = Quotient.mk paritySetoid (n + 1)) ∧
      s (Quotient.mk paritySetoid 0) = Quotient.mk paritySetoid 1 ∧
      s (Quotient.mk paritySetoid 1) = Quotient.mk paritySetoid 0 ∧
      Function.Involutive s := by sorry

theorem diagram_fiber_p_and_range :
    diagramMap ⁻¹' {MapLabel.p} = {0} ∧
      Set.range diagramMap = {MapLabel.p, MapLabel.q} := by sorry

end Lemmatheca.Entry.EquivalenceRelations
