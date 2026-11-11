import Lemmatheca.PregeometryDimension.Localization

namespace Lemmatheca.ModelTheory.StronglyMinimalSets.Pregeometry
universe w
noncomputable section

def identityPregeometry (X : Type w) : Pregeometry X where
  cl S := S
  extensive := by intro S; exact Set.Subset.rfl
  monotone := by intro S R h; exact h
  idempotent := by intro S; rfl
  finite_character := by
    classical
    intro x S
    constructor
    · intro hx
      exact ⟨{x}, by simpa, by simp⟩
    · rintro ⟨F, hF, hx⟩
      exact hF hx
  exchange := by
    intro S a b hb
    have hba : b = a := hb.1.resolve_left hb.2
    subst b
    exact Or.inr rfl

theorem identity_independent {X : Type w} (S : Set X) :
    (identityPregeometry X).Independent S := by
  intro a ha hcl
  exact hcl.2 rfl

theorem identity_basis_iff {X : Type w} (B S : Set X) :
    (identityPregeometry X).IsBasis B S ↔ B = S := by
  constructor
  · intro hb
    exact hb.2.2
  · intro h
    subst B
    exact ⟨Set.Subset.rfl, identity_independent S, rfl⟩

theorem identity_dimension {X : Type w} (S : Set X) :
    (identityPregeometry X).dimension S = Cardinal.mk S := by
  exact (identityPregeometry X).dimension_eq_mk ((identity_basis_iff S S).mpr rfl)

theorem identity_independentOver_iff {X : Type w} (A I : Set X) :
    (identityPregeometry X).IndependentOver A I ↔ Disjoint I A := by
  change (∀ a ∈ I, a ∉ A ∪ (I \ {a})) ↔ Disjoint I A
  constructor
  · intro hi
    apply Set.disjoint_left.mpr
    intro a ha hA
    exact hi a ha (Or.inl hA)
  · intro hi a ha hcl
    rcases hcl with hA | hI
    · exact Set.disjoint_left.mp hi ha hA
    · exact hI.2 rfl

theorem identity_relative_basis_iff {X : Type w} (A B S : Set X) :
    (identityPregeometry X).IsRelativeBasis A B S ↔ B = S \ A := by
  constructor
  · rintro ⟨hBS, hi, hcl⟩
    change A ∪ B = A ∪ S at hcl
    have hd := (identity_independentOver_iff A B).mp hi
    apply Set.Subset.antisymm
    · intro x hx
      exact ⟨hBS hx, fun hxA => Set.disjoint_left.mp hd hx hxA⟩
    · intro x hx
      have hxU : x ∈ A ∪ B := by
        rw [hcl]
        exact Or.inr hx.1
      exact hxU.resolve_left hx.2
  · intro h
    subst B
    refine ⟨Set.sdiff_subset, (identity_independentOver_iff A _).mpr ?_, ?_⟩
    · exact Set.disjoint_left.mpr (fun x hx hxA => hx.2 hxA)
    · change A ∪ (S \ A) = A ∪ S
      ext x
      by_cases hx : x ∈ A <;> simp [hx]

theorem identity_relativeDimension {X : Type w} (A S : Set X) :
    (identityPregeometry X).relativeDimension A S = Cardinal.mk (S \ A : Set X) := by
  exact (identityPregeometry X).relativeDimension_eq_mk
    ((identity_relative_basis_iff A (S \ A) S).mpr rfl)

end
end Lemmatheca.ModelTheory.StronglyMinimalSets.Pregeometry
