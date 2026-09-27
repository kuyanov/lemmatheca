import Mathlib.Data.Setoid.Partition
import Mathlib.Basic.IsEmpty.Defs

/-!
# Equivalence relations: additional set descriptions

The main quotient and partition constructions are bound directly to mathlib.
These statements record remaining set descriptions and boundary cases.
-/

namespace Lemmatheca.SetTheory

universe u v
variable {α : Type u} {β : Type v}

theorem universal_relation_classes [Nonempty α] :
    (⊤ : Setoid α).classes = {Set.univ} := by
  ext s
  simp [Setoid.classes]

theorem empty_relation [IsEmpty α] (R : α → α → Prop) :
    R = (fun _ _ => False) ∧ Equivalence R := by
  constructor
  · funext a
    exact isEmptyElim a
  · exact ⟨fun a => isEmptyElim a, fun {a} => isEmptyElim a,
      fun {a} => isEmptyElim a⟩

theorem empty_equivalence_classes [IsEmpty α] (s : Setoid α) :
    s.classes = ∅ := by
  ext t
  simp [Setoid.classes]

theorem empty_partition_iff [IsEmpty α] (P : Set (Set α)) :
    Setoid.IsPartition P ↔ P = ∅ := by
  constructor
  · intro h
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro s hs
    obtain ⟨a, _⟩ := Setoid.nonempty_of_mem_partition h hs
    exact isEmptyElim a
  · rintro rfl
    exact ⟨by simp, fun a => isEmptyElim a⟩

theorem kernel_classes_eq_nonempty_fibers (f : α → β) :
    (Setoid.ker f).classes = Set.range (fun y : Set.range f => f ⁻¹' {y.val}) := by
  ext s
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨⟨f a, ⟨a, rfl⟩⟩, rfl⟩
  · rintro ⟨⟨y, a, rfl⟩, rfl⟩
    exact ⟨a, rfl⟩

theorem quotient_image_inverse_fiber (f : α → β) (y : Set.range f) :
    (Setoid.quotientEquivClasses (Setoid.ker f)
      ((Setoid.quotientKerEquivRange f).symm y)).val = f ⁻¹' {y.val} := by
  rcases y with ⟨y, a, rfl⟩
  have h : (Setoid.quotientKerEquivRange f).symm ⟨f a, ⟨a, rfl⟩⟩ =
      Quotient.mk (Setoid.ker f) a := by
    apply (Setoid.quotientKerEquivRange f).injective
    exact (Setoid.quotientKerEquivRange f).apply_symm_apply _
  rw [h, Setoid.quotientEquivClasses_mk_eq]
  rfl

end Lemmatheca.SetTheory
