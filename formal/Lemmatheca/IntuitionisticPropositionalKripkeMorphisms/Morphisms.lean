import Lemmatheca.IntuitionisticKripkeSemantics.Constructions

/-! Bounded maps retain the actual specified function and the full future cone. -/
namespace Lemmatheca.ProofTheory.Intuitionistic.Kripke

open Lemmatheca.MathematicalLogic.Propositional
open PropFormula

universe u v w z
variable {α : Type u} {W : Type v} {X : Type w} {Y : Type z}
variable [Preorder W] [Preorder X] [Preorder Y]

/-- Forth and back are properties of this specified function. -/
structure IsBoundedFrameMap (f : W → X) : Prop where
  forth : Monotone f
  back : ∀ (a : W) (x : X), f a ≤ x → ∃ b : W, a ≤ b ∧ f b = x

/-- The very image function identifies the two complete upward cones. -/
theorem boundedFrameMap_iff_future_image (f : W → X) :
    IsBoundedFrameMap f ↔
      ∀ a : W, f '' {b : W | a ≤ b} = {x : X | f a ≤ x} := by
  constructor
  · intro hf a
    ext x
    constructor
    · rintro ⟨b, hab, rfl⟩
      exact hf.forth hab
    · intro hax
      obtain ⟨b, hab, hbx⟩ := hf.back a x hax
      exact ⟨b, hab, hbx⟩
  · intro h
    constructor
    · intro a b hab
      have hb : f b ∈ f '' {b : W | a ≤ b} := ⟨b, hab, rfl⟩
      rw [h a] at hb
      exact hb
    · intro a x hax
      have hx : x ∈ f '' {b : W | a ≤ b} := by
        rw [h a]
        exact hax
      exact hx

/-- Atom agreement and the frame conditions refer to one and the same function. -/
structure IsBoundedMorphism (M : Model α W) (N : Model α X) (f : W → X) : Prop
    extends IsBoundedFrameMap f where
  atoms : ∀ (a : W) (p : α), M.valuation a p ↔ N.valuation (f a) p

/-- The actual identity function is the morphism. -/
theorem boundedMorphism_identity (M : Model α W) : IsBoundedMorphism M M id := by
  refine { forth := fun _ _ h => h, back := ?_, atoms := ?_ }
  · intro a x hax
    exact ⟨x, hax, rfl⟩
  · intro a p
    rfl

/-- The actual composite, rather than an unspecified map with the same endpoints. -/
theorem boundedMorphism_composition (M : Model α W) (N : Model α X) (L : Model α Y)
    (f : W → X) (g : X → Y) (hf : IsBoundedMorphism M N f)
    (hg : IsBoundedMorphism N L g) : IsBoundedMorphism M L (g ∘ f) := by
  refine { forth := hg.forth.comp hf.forth, back := ?_, atoms := ?_ }
  · intro a y hay
    obtain ⟨x, hax, hxy⟩ := hg.back (f a) y hay
    obtain ⟨b, hab, hbx⟩ := hf.back a x hax
    exact ⟨b, hab, by simp only [Function.comp_apply, hbx, hxy]⟩
  · intro a p
    exact (hf.atoms a p).trans (hg.atoms (f a) p)

/-- The source valuation is literally the target valuation after this function. -/
def pullback [Nonempty W] (N : Model α X) (f : W → X) (hf : Monotone f) : Model α W where
  world_nonempty := inferInstance
  valuation a p := N.valuation (f a) p
  persistent h p hp := N.persistent (hf h) p hp

theorem pullback_boundedMorphism [Nonempty W] (N : Model α X) (f : W → X)
    (hf : IsBoundedFrameMap f) : IsBoundedMorphism (pullback N f hf.forth) N f := by
  exact { toIsBoundedFrameMap := hf, atoms := fun _ _ => Iff.rfl }

/-- The existing generated model and the literal subtype inclusion. -/
theorem generated_inclusion_boundedMorphism (M : Model α W) (r : W) :
    IsBoundedMorphism (generated M r) M
      (Subtype.val : {a : W // r ≤ a} → W) := by
  refine { forth := fun _ _ h => h, back := ?_, atoms := fun _ _ => Iff.rfl }
  intro a x hax
  exact ⟨⟨x, le_trans a.property hax⟩, hax, rfl⟩

theorem generated_inclusion_surjective_iff (r : W) :
    Function.Surjective (Subtype.val : {a : W // r ≤ a} → W) ↔
      ∀ a : W, r ≤ a := by
  constructor
  · intro h a
    obtain ⟨b, rfl⟩ := h a
    exact b.property
  · intro h a
    exact ⟨⟨a, h a⟩, rfl⟩

/-- Native negation and implication use the back condition, at the mapped world. -/
theorem boundedMorphism_forcing (M : Model α W) (N : Model α X) (f : W → X)
    (hf : IsBoundedMorphism M N f) (a : W) (A : PropFormula α) :
    Forces M a A ↔ Forces N (f a) A := by
  induction A generalizing a with
  | atom p => exact hf.atoms a p
  | falsum => rfl
  | neg A ih =>
      constructor
      · intro h x hax hx
        obtain ⟨b, hab, rfl⟩ := hf.back a x hax
        exact h b hab ((ih b).mpr hx)
      · intro h b hab hb
        exact h (f b) (hf.forth hab) ((ih b).mp hb)
  | conj A B ihA ihB => simp only [Forces, ihA, ihB]
  | disj A B ihA ihB => simp only [Forces, ihA, ihB]
  | impl A B ihA ihB =>
      constructor
      · intro h x hax hx
        obtain ⟨b, hab, rfl⟩ := hf.back a x hax
        exact (ihB b).mp (h b hab ((ihA b).mpr hx))
      · intro h b hab hb
        exact (ihB b).mpr (h (f b) (hf.forth hab) ((ihA b).mp hb))

theorem boundedMorphism_context (M : Model α W) (N : Model α X) (f : W → X)
    (hf : IsBoundedMorphism M N f) (a : W) (Γ : Set (PropFormula α)) :
    ForcesContext M a Γ ↔ ForcesContext N (f a) Γ := by
  constructor
  · intro h A hA
    exact (boundedMorphism_forcing M N f hf a A).mp (h A hA)
  · intro h A hA
    exact (boundedMorphism_forcing M N f hf a A).mpr (h A hA)

theorem boundedMorphism_countermodel (M : Model α W) (N : Model α X) (f : W → X)
    (hf : IsBoundedMorphism M N f) (a : W) (Γ : Set (PropFormula α)) (A : PropFormula α) :
    Countermodel M a Γ A ↔ Countermodel N (f a) Γ A := by
  exact and_congr (boundedMorphism_context M N f hf a Γ)
    (not_congr (boundedMorphism_forcing M N f hf a A))

theorem boundedMorphism_all_worlds_preimage (M : Model α W) (N : Model α X) (f : W → X)
    (hf : IsBoundedMorphism M N f) (A : PropFormula α) :
    (∀ x : X, Forces N x A) → ∀ a : W, Forces M a A := by
  intro h a
  exact (boundedMorphism_forcing M N f hf a A).mpr (h (f a))

theorem boundedMorphism_all_worlds_iff (M : Model α W) (N : Model α X) (f : W → X)
    (hf : IsBoundedMorphism M N f) (hsurj : Function.Surjective f) (A : PropFormula α) :
    (∀ a : W, Forces M a A) ↔ ∀ x : X, Forces N x A := by
  constructor
  · intro h x
    obtain ⟨a, rfl⟩ := hsurj x
    exact (boundedMorphism_forcing M N f hf a A).mp (h a)
  · exact boundedMorphism_all_worlds_preimage M N f hf A

/-- Every persistent valuation and every world on this nonempty preordered frame. -/
def FrameValid (W : Type v) [Preorder W] [Nonempty W] (A : PropFormula α) : Prop :=
  ∀ (M : Model α W) (a : W), Forces M a A

theorem boundedFrameMap_validity_image [Nonempty W] [Nonempty X]
    (f : W → X) (hf : IsBoundedFrameMap f) (hsurj : Function.Surjective f)
    (A : PropFormula α) : FrameValid W A → FrameValid X A := by
  intro h N
  exact (boundedMorphism_all_worlds_iff (pullback N f hf.forth) N f
    (pullback_boundedMorphism N f hf) hsurj A).mp (h (pullback N f hf.forth))

end Lemmatheca.ProofTheory.Intuitionistic.Kripke
