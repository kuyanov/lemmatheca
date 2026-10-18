import Lemmatheca.MathematicalLogic.Skolemization

/-! Concrete counterexamples for the Skolemization entry. -/
namespace Lemmatheca.Entry.Skolemization

open FirstOrder FirstOrder.Language

theorem five_variable_dependencies {M : Type*} (R : M → M → M → M → M → Prop) :
    (∃ a, ∀ x, ∃ b, ∀ z, ∃ c, R a x b z c) ↔
      ∃ (d : M) (f : M → M) (g : M → M → M), ∀ x z, R d x (f x) z (g x z) := by
  classical
  constructor
  · rintro ⟨d, hd⟩
    choose f hf using hd
    choose g hg using hf
    exact ⟨d, f, g, hg⟩
  · rintro ⟨d, f, g, h⟩
    exact ⟨d, fun x => ⟨f x, fun z => ⟨g x z, h x z⟩⟩⟩

/-- An unsuitable interpretation of a new function on a two-element domain. -/
def constantFalse : Bool → Bool := fun _ => false

theorem arbitrary_expansion_counterexample :
    (∀ x : Bool, ∃ y : Bool, x = y) ∧
      ¬ (∀ x : Bool, x = constantFalse x) ∧
      (∀ x : Bool, x = id x) := by
  refine ⟨fun x => ⟨x, rfl⟩, ?_, fun _ => rfl⟩
  intro h
  have hbad := h true
  cases hbad

theorem quantifier_order_counterexample :
    (∀ x : Bool, ∃ y : Bool, x = y) ∧
      ¬ (∃ y : Bool, ∀ x : Bool, x = y) := by
  refine ⟨fun x => ⟨x, rfl⟩, ?_⟩
  rintro ⟨y, hy⟩
  have hbad := (hy true).trans (hy false).symm
  cases hbad

theorem freshness_background_counterexample :
    (∃ x : Bool, x ≠ constantFalse x) ∧
      (∀ x : Bool, ∃ y : Bool, x = y) ∧
      ¬ ((∃ x : Bool, x ≠ constantFalse x) ∧
        ∀ x : Bool, x = constantFalse x) := by
  refine ⟨⟨true, by decide⟩, fun x => ⟨x, rfl⟩, ?_⟩
  rintro ⟨⟨x, hx⟩, h⟩
  exact hx (h x)

end Lemmatheca.Entry.Skolemization
