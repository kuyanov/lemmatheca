import Mathlib.Order.FixedPoints
import Mathlib.Tactic

/-! Reusable Relations definitions and results. -/

/-! Relation.Comp R S follows R first and then S. This is the
entry’s composition S ∘ R; reversing the written arguments silently would
reverse its meaning. -/
set_option autoImplicit false
universe u v
namespace Lemmatheca.SetTheory.Relations

/-- The nth power of a relation follows n edges, with power zero the diagonal. -/
def relationPower {α : Type u} (R : α → α → Prop) : ℕ → α → α → Prop
  | 0 => Eq
  | n + 1 => Relation.Comp (relationPower R n) R

/-- Finite positive paths describe the transitive closure, and arbitrary finite paths the reflexive transitive closure. -/
theorem paths_characterize_closures {α : Type u} (R : α → α → Prop) (a b : α) :
    (Relation.TransGen R a b ↔ ∃ n, 0 < n ∧ relationPower R n a b) ∧
    (Relation.ReflTransGen R a b ↔ ∃ n, relationPower R n a b) := by
  have hpath : ∀ n a b, relationPower R n a b → Relation.ReflTransGen R a b := by
    intro n
    induction n with
    | zero => intro a b hab; cases hab; exact .refl
    | succ n ih =>
      intro a b hab
      obtain ⟨c, hac, hcb⟩ := hab
      exact (ih a c hac).tail hcb
  have hpositive : ∀ n a b, relationPower R (n + 1) a b → Relation.TransGen R a b := by
    intro n
    induction n with
    | zero =>
      intro a b hab
      obtain ⟨c, hac, hcb⟩ := hab
      cases hac
      exact .single hcb
    | succ n ih =>
      intro a b hab
      obtain ⟨c, hac, hcb⟩ := hab
      exact (ih a c hac).tail hcb
  constructor
  · constructor
    · intro h
      induction h with
      | single hab => exact ⟨1, by omega, a, rfl, hab⟩
      | @tail b c h hbc ih =>
        obtain ⟨n, hn, hpath⟩ := ih
        exact ⟨n + 1, by omega, b, hpath, hbc⟩
    · rintro ⟨n, hn, hab⟩
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
      exact hpositive m a b hab
  · constructor
    · intro h
      induction h with
      | refl => exact ⟨0, rfl⟩
      | @tail b c h hbc ih =>
        obtain ⟨n, hn⟩ := ih
        exact ⟨n + 1, b, hn, hbc⟩
    · rintro ⟨n, hn⟩
      exact hpath n a b hn

/-- Reflexive and symmetric closures are the least relations with the required properties. -/
theorem elementary_closures_least {α : Type u} (R S : α → α → Prop) :
    (Std.Refl S → R ≤ S → Relation.ReflGen R ≤ S) ∧
    (Std.Symm S → R ≤ S → Relation.SymmGen R ≤ S) := by
  constructor
  · intro hS hRS a b hab
    cases hab with
    | refl => exact hS.refl a
    | single hab => exact hRS a b hab
  · intro hS hRS a b hab
    rcases hab with hab | hab
    · exact hRS a b hab
    · exact hS.symm b a (hRS b a hab)

/-- The double-complement operator used in the fixed-point proof of size comparison. -/
def comparisonOperator {α : Type u} {β : Type v} (f : α → β) (g : β → α)
    (X : Set α) : Set α := (g '' (f '' X)ᶜ)ᶜ

/-- The comparison operator is monotone. -/
theorem comparisonOperator_monotone {α : Type u} {β : Type v} (f : α → β) (g : β → α) :
    Monotone (comparisonOperator f g) := by
  intro X Y hXY
  exact Set.compl_subset_compl.mpr
    (Set.image_mono (Set.compl_subset_compl.mpr (Set.image_mono hXY)))

/-- Any fixed point of the comparison operator yields a bijection respecting both pieces. -/
theorem fixed_point_bijection {α : Type u} {β : Type v} (f : α ↪ β) (g : β ↪ α)
    (X : Set α) (hX : comparisonOperator f g X = X) :
    ∃ e : α ≃ β, (∀ a ∈ X, e a = f a) ∧ (∀ a ∉ X, g (e a) = a) ∧
      e '' X = f '' X ∧ e '' Xᶜ = (f '' X)ᶜ := by
  classical
  have houtside : ∀ a ∉ X, ∃ b ∉ f '' X, g b = a := by
    intro a ha
    have : a ∈ g '' (f '' X)ᶜ := by
      by_contra hn
      exact ha (hX ▸ hn)
    exact this
  let v : α → β := fun a => if ha : a ∈ X then f a else (houtside a ha).choose
  have inside : ∀ a ∈ X, v a = f a := by
    intro a ha
    simp [v, ha]
  have outside : ∀ a ∉ X, v a ∉ f '' X ∧ g (v a) = a := by
    intro a ha
    simpa only [v, dite_eq_right ha] using (houtside a ha).choose_spec
  have hinj : Function.Injective v := by
    intro a b hab
    by_cases ha : a ∈ X <;> by_cases hb : b ∈ X
    · apply f.injective
      simpa only [inside a ha, inside b hb] using hab
    · exact False.elim ((outside b hb).1 (hab ▸ ⟨a, ha, (inside a ha).symm⟩))
    · exact False.elim ((outside a ha).1 (hab.symm ▸ ⟨b, hb, (inside b hb).symm⟩))
    · have := congrArg g hab
      simpa only [(outside a ha).2, (outside b hb).2] using this
  have hsurj : Function.Surjective v := by
    intro b
    by_cases hb : b ∈ f '' X
    · obtain ⟨a, ha, rfl⟩ := hb
      exact ⟨a, inside a ha⟩
    · have ha : g b ∉ X := by
        intro ha
        have hn : g b ∉ g '' (f '' X)ᶜ := by
          change g b ∈ comparisonOperator f g X
          rw [hX]
          exact ha
        exact hn ⟨b, hb, rfl⟩
      exact ⟨g b, g.injective (outside (g b) ha).2⟩
  let e := Equiv.ofBijective v ⟨hinj, hsurj⟩
  refine ⟨e, inside, fun a ha => (outside a ha).2, ?_, ?_⟩
  · ext b
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a, ha, (inside a ha).symm⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a, ha, inside a ha⟩
  · ext b
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact (outside a ha).1
    · intro hb
      obtain ⟨a, rfl⟩ := hsurj b
      refine ⟨a, ?_, rfl⟩
      intro ha
      exact hb ⟨a, ha, (inside a ha).symm⟩

end Lemmatheca.SetTheory.Relations
