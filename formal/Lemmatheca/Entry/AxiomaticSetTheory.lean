import Lemmatheca.SetTheory.Ordinals
import Mathlib.SetTheory.ZFC.Class

set_option autoImplicit false

/-! Semantic instances of the set-construction axioms in mathlib's universe-relative
`ZFSet` realization. Predicates stand for formula instances with fixed parameters;
they do not encode first-order syntax or prove consistency, independence, or
derivability over ZF without Choice. The general Russell statement only assumes
the membership condition supplied by Separation. -/
namespace Lemmatheca.Entry.AxiomaticSetTheory
open scoped ZFSet
universe u

def IsInductive (I : ZFSet.{u}) : Prop :=
  ∅ ∈ I ∧ ∀ x ∈ I, insert x x ∈ I

def IsProperClass (P : ZFSet.{u} → Prop) : Prop :=
  ¬ ∃ A : ZFSet.{u}, ∀ x, x ∈ A ↔ P x

def russellPart (A : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun x => x ∉ x) A

theorem russell_not_mem {α : Type u} (M : α → α → Prop) (A R : α)
    (hR : ∀ x, M x R ↔ M x A ∧ ¬ M x x) : ¬ M R A := by
  sorry

theorem russellPart_not_mem (A : ZFSet.{u}) : russellPart A ∉ A := by
  sorry

theorem universal_class_proper : IsProperClass (fun _ : ZFSet.{u} => True) := by
  sorry

theorem proper_class_not_represented (P : ZFSet.{u} → Prop) (hP : IsProperClass P)
    (A : ZFSet.{u}) : ¬ ∃ x ∈ A, ∀ y, y ∈ x ↔ P y := by
  sorry

theorem relative_intersection_empty (U : ZFSet.{u}) :
    ZFSet.sep (fun x => ∀ C ∈ (∅ : ZFSet.{u}), x ∈ C) U = U := by
  sorry

theorem product_empty_cases (A : ZFSet.{u}) :
    ZFSet.prod ∅ A = ∅ ∧ ZFSet.prod A ∅ = ∅ := by
  sorry

theorem function_set_empty_cases (A B : ZFSet.{u}) :
    ZFSet.funs ∅ B = {∅} ∧ (A ≠ ∅ → ZFSet.funs A ∅ = ∅) := by
  sorry

theorem replacement_unique_outputs (A : ZFSet.{u}) (R : ZFSet.{u} → ZFSet.{u} → Prop)
    (hR : ∀ x ∈ A, ∃! y, R x y) :
    ∃ B : ZFSet.{u}, ∀ y, y ∈ B ↔ ∃ x ∈ A, R x y := by
  sorry

theorem replacement_restricted_graph (A : ZFSet.{u})
    (R : ZFSet.{u} → ZFSet.{u} → Prop) (hR : ∀ x ∈ A, ∃! y, R x y) :
    ∃ G : ZFSet.{u}, ∀ z, z ∈ G ↔ ∃ x ∈ A, ∃ y, R x y ∧ z = ZFSet.pair x y := by
  sorry

theorem foundation_two_minima :
    let z : ZFSet.{u} := ∅
    let one : ZFSet.{u} := {z}
    let two : ZFSet.{u} := {z, one}
    let A : ZFSet.{u} := {one, {two}}
    one ∈ A ∧ ({two} : ZFSet.{u}) ∈ A ∧ one ≠ ∅ ∧ ({two} : ZFSet.{u}) ≠ ∅ ∧
      one ∩ A = ∅ ∧ ({two} : ZFSet.{u}) ∩ A = ∅ := by
  sorry

theorem family_choice_graph (A : ZFSet.{u}) (hA : ∀ x ∈ A, x.Nonempty) :
    ∃ G : ZFSet.{u}, ZFSet.IsFunc A (ZFSet.sUnion A) G ∧
      ∀ x ∈ A, ∃ y ∈ x, ZFSet.pair x y ∈ G := by
  sorry

theorem family_powersets_bounded (A : ZFSet.{u}) :
    let B := ZFSet.range (fun x : A => ZFSet.powerset x.val)
    (∀ y, y ∈ B ↔ ∃ x ∈ A, ZFSet.powerset x = y) ∧
      B ⊆ ZFSet.powerset (ZFSet.powerset (ZFSet.sUnion A)) ∧
      (A = ∅ → B = ∅) := by
  sorry

end Lemmatheca.Entry.AxiomaticSetTheory
