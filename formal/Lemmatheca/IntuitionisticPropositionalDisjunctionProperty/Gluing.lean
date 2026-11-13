import Lemmatheca.IntuitionisticKripkeSemantics.Models

/-! Exact root gluing of two ordered models and preservation on both old branches. -/
namespace Lemmatheca.ProofTheory.Intuitionistic.DisjunctionProperty

open Lemmatheca.MathematicalLogic.Propositional
open PropFormula

universe u v w
variable {α : Type u} {W₀ : Type v} {W₁ : Type w}

/-- A new root and the two disjoint tagged sets of old worlds. -/
inductive World (W₀ : Type v) (W₁ : Type w)
  | root
  | left (world : W₀)
  | right (world : W₁)

variable [Preorder W₀] [Preorder W₁]

/-- The root lies below everything; each branch retains exactly its old comparisons. -/
def worldLE : World W₀ W₁ → World W₀ W₁ → Prop
  | .root, _ => True
  | .left x, .left y => x ≤ y
  | .right x, .right y => x ≤ y
  | _, _ => False

instance worldPreorder : Preorder (World W₀ W₁) where
  le := worldLE
  le_refl x := by cases x <;> simp [worldLE]
  le_trans x y z hxy hyz := by
    cases x <;> cases y <;> cases z <;> simp_all [worldLE]
    · exact le_trans hxy hyz
    · exact le_trans hxy hyz

/-- The new root verifies no atom; the two old valuations are retained exactly. -/
def glue (M₀ : Kripke.Model α W₀) (M₁ : Kripke.Model α W₁) :
    Kripke.Model α (World W₀ W₁) where
  world_nonempty := ⟨.root⟩
  valuation
    | .root, _ => False
    | .left x, p => M₀.valuation x p
    | .right x, p => M₁.valuation x p
  persistent {x y} h p hp := by
    change worldLE x y at h
    cases x <;> cases y <;> simp_all [worldLE]
    · exact M₀.persistent h p hp
    · exact M₁.persistent h p hp

/-- All native formulas keep exactly their forcing value on the left old branch. -/
theorem forces_left (M₀ : Kripke.Model α W₀) (M₁ : Kripke.Model α W₁)
    (x : W₀) (A : PropFormula α) :
    Kripke.Forces (glue M₀ M₁) (.left x) A ↔ Kripke.Forces M₀ x A := by
  induction A generalizing x with
  | atom p => rfl
  | falsum => rfl
  | neg A ih =>
      constructor
      · intro h z hxz hA
        exact h (.left z) hxz ((ih z).mpr hA)
      · intro h z hxz hA
        cases z with
        | root =>
            change False at hxz
            exact hxz.elim
        | left z => exact h z hxz ((ih z).mp hA)
        | right z =>
            change False at hxz
            exact hxz.elim
  | conj A B ihA ihB => exact and_congr (ihA x) (ihB x)
  | disj A B ihA ihB => exact or_congr (ihA x) (ihB x)
  | impl A B ihA ihB =>
      constructor
      · intro h z hxz hA
        exact (ihB z).mp (h (.left z) hxz ((ihA z).mpr hA))
      · intro h z hxz hA
        cases z with
        | root =>
            change False at hxz
            exact hxz.elim
        | left z => exact (ihB z).mpr (h z hxz ((ihA z).mp hA))
        | right z =>
            change False at hxz
            exact hxz.elim

/-- All native formulas keep exactly their forcing value on the right old branch. -/
theorem forces_right (M₀ : Kripke.Model α W₀) (M₁ : Kripke.Model α W₁)
    (x : W₁) (A : PropFormula α) :
    Kripke.Forces (glue M₀ M₁) (.right x) A ↔ Kripke.Forces M₁ x A := by
  induction A generalizing x with
  | atom p => rfl
  | falsum => rfl
  | neg A ih =>
      constructor
      · intro h z hxz hA
        exact h (.right z) hxz ((ih z).mpr hA)
      · intro h z hxz hA
        cases z with
        | root =>
            change False at hxz
            exact hxz.elim
        | right z => exact h z hxz ((ih z).mp hA)
        | left z =>
            change False at hxz
            exact hxz.elim
  | conj A B ihA ihB => exact and_congr (ihA x) (ihB x)
  | disj A B ihA ihB => exact or_congr (ihA x) (ihB x)
  | impl A B ihA ihB =>
      constructor
      · intro h z hxz hA
        exact (ihB z).mp (h (.right z) hxz ((ihA z).mpr hA))
      · intro h z hxz hA
        cases z with
        | root =>
            change False at hxz
            exact hxz.elim
        | right z => exact (ihB z).mpr (h z hxz ((ihA z).mp hA))
        | left z =>
            change False at hxz
            exact hxz.elim

/-- Exactly the common negated premises of the old least worlds hold at the new root. -/
theorem root_negation (M₀ : Kripke.Model α W₀) (M₁ : Kripke.Model α W₁)
    (w₀ : W₀) (w₁ : W₁) (h₀ : ∀ x, w₀ ≤ x) (h₁ : ∀ x, w₁ ≤ x)
    (C : PropFormula α) :
    Kripke.Forces (glue M₀ M₁) .root (neg C) ↔
      Kripke.Forces M₀ w₀ (neg C) ∧ Kripke.Forces M₁ w₁ (neg C) := by
  constructor
  · intro h
    constructor
    · apply (forces_left M₀ M₁ w₀ (neg C)).mp
      exact Kripke.forces_mono _ _
        (show (World.root : World W₀ W₁) ≤ .left w₀ from trivial) h
    · apply (forces_right M₀ M₁ w₁ (neg C)).mp
      exact Kripke.forces_mono _ _
        (show (World.root : World W₀ W₁) ≤ .right w₁ from trivial) h
  · rintro ⟨hn₀, hn₁⟩ z _ hC
    cases z with
    | root =>
        apply hn₀ w₀ le_rfl
        apply (forces_left M₀ M₁ w₀ C).mp
        exact Kripke.forces_mono _ _
          (show (World.root : World W₀ W₁) ≤ .left w₀ from trivial) hC
    | left x => exact hn₀ x (h₀ x) ((forces_left M₀ M₁ x C).mp hC)
    | right x => exact hn₁ x (h₁ x) ((forces_right M₀ M₁ x C).mp hC)

end Lemmatheca.ProofTheory.Intuitionistic.DisjunctionProperty
