import Mathlib.Data.Setoid.Partition
import Mathlib.Basic.IsEmpty.Defs

/-!
# Equivalence relations: additional set descriptions

The main quotient and partition constructions are bound directly to mathlib.
These statements record remaining set descriptions and boundary cases.
They await correspondence review and proof work.
-/

namespace Lemmatheca.SetTheory

universe u v
variable {α : Type u} {β : Type v}

theorem not_symmetric_iff_witness (R : α → α → Prop) :
    ¬ Std.Symm R ↔ ∃ a b, R a b ∧ ¬ R b a := by sorry

theorem universal_relation_classes [Nonempty α] :
    (⊤ : Setoid α).classes = {Set.univ} := by sorry

theorem empty_relation [IsEmpty α] (R : α → α → Prop) :
    R = (fun _ _ => False) ∧ Equivalence R := by sorry

theorem empty_equivalence_classes [IsEmpty α] (s : Setoid α) :
    s.classes = ∅ := by sorry

theorem empty_partition_iff [IsEmpty α] (P : Set (Set α)) :
    Setoid.IsPartition P ↔ P = ∅ := by sorry

theorem kernel_classes_eq_nonempty_fibers (f : α → β) :
    (Setoid.ker f).classes = Set.range (fun y : Set.range f => f ⁻¹' {y.val}) := by sorry

theorem quotient_image_inverse_fiber (f : α → β) (y : Set.range f) :
    (Setoid.quotientEquivClasses (Setoid.ker f)
      ((Setoid.quotientKerEquivRange f).symm y)).val = f ⁻¹' {y.val} := by sorry

end Lemmatheca.SetTheory
