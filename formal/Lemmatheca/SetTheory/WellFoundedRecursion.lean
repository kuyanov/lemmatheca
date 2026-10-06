import Mathlib.Tactic
import Mathlib.SetTheory.ZFC.VonNeumann

/-! Reusable WellFoundedRecursion definitions and results. -/

/-! Universe-relative set-valued recursion; this does not encode first-order ZF. -/
set_option autoImplicit false
universe u v
namespace Lemmatheca.SetTheory.WellFoundedRecursion
open scoped ZFSet Ordinal

/-- A finite relation with no positive-length cycle is well-founded. -/
theorem finite_acyclic_wellFounded {α : Type v} [Finite α] (R : α → α → Prop)
    (h : ∀ a, ¬ Relation.TransGen R a a) : WellFounded R := by
  let : IsTrans α (Relation.TransGen R) := ⟨fun _ _ _ => Relation.TransGen.trans⟩
  let : Std.Irrefl (Relation.TransGen R) := ⟨h⟩
  exact (Finite.wellFounded_of_trans_of_irrefl (Relation.TransGen R)).mono
    (fun _ _ => Relation.TransGen.single)

/-- A subset contains every predecessor of each of its points. -/
def DownwardClosed {α : Type v} (R : α → α → Prop) (D : Set α) : Prop :=
  ∀ a ∈ D, ∀ b, R b a → b ∈ D

/-- The least downward-closed subset containing a point. -/
def downwardHull {α : Type v} (R : α → α → Prop) (a : α) : Set α :=
  {b | ∀ D, DownwardClosed R D → a ∈ D → b ∈ D}

/-- A downward hull contains its point, is closed, and is least. -/
theorem downwardHull_spec {α : Type v} (R : α → α → Prop) (a : α) :
    a ∈ downwardHull R a ∧ DownwardClosed R (downwardHull R a) ∧
    ∀ D, DownwardClosed R D → a ∈ D → downwardHull R a ⊆ D := by
  refine ⟨fun D _ ha => ha, ?_, ?_⟩
  · intro b hb c hcb D hD ha
    exact hD b (hb D hD ha) c hcb
  · intro D hD ha b hb
    exact hb D hD ha

/-- The rule takes the indexed values at immediate predecessors. -/
abbrev RecursionRule {α : Type v} (R : α → α → Prop) :=
  (a : α) → ({b // R b a} → ZFSet.{u}) → ZFSet.{u}

/-- Well-founded recursion with set values. -/
noncomputable def recursiveValue {α : Type v} {R : α → α → Prop}
    (h : WellFounded R) (H : RecursionRule.{u} R) : α → ZFSet.{u} :=
  h.fix (fun a rec => H a (fun b => rec b.val b.property))

/-- Every well-founded set-valued recursion has a unique solution. -/
theorem recursion_exists_unique {α : Type v} {R : α → α → Prop}
    (h : WellFounded R) (H : RecursionRule.{u} R) :
    ∃! F : α → ZFSet.{u}, ∀ a, F a = H a (fun b => F b.val) := by
  refine ⟨recursiveValue h H, ?_, ?_⟩
  · intro a
    exact h.fix_eq _ a
  · intro F hF
    funext a
    induction a using h.induction with
    | h a ih =>
      rw [hF a, recursiveValue, h.fix_eq]
      congr 1
      funext b
      exact ih b.val b.property

/-- Solutions on downward-closed domains agree on their overlap. -/
theorem partial_solutions_agree {α : Type v} {R : α → α → Prop}
    (h : WellFounded R) (H : RecursionRule.{u} R) (D E : Set α)
    (hD : DownwardClosed R D) (hE : DownwardClosed R E)
    (F : D → ZFSet.{u}) (G : E → ZFSet.{u})
    (hF : ∀ a : D, F a = H a.val (fun b => F ⟨b.val, hD a.val a.property b.val b.property⟩))
    (hG : ∀ a : E, G a = H a.val (fun b => G ⟨b.val, hE a.val a.property b.val b.property⟩)) :
    ∀ a (haD : a ∈ D) (haE : a ∈ E), F ⟨a, haD⟩ = G ⟨a, haE⟩ := by
  intro a
  induction a using h.induction with
  | h a ih =>
    intro haD haE
    rw [hF ⟨a, haD⟩, hG ⟨a, haE⟩]
    congr 1
    funext b
    exact ih b.val b.property _ _

end Lemmatheca.SetTheory.WellFoundedRecursion
