import Lemmatheca.PregeometryDimension.Bases
import Lemmatheca.StronglyMinimalSets.Exchange

namespace Lemmatheca.ModelTheory.StronglyMinimalSets.Pregeometry
open FirstOrder FirstOrder.Language
open Lemmatheca.ModelTheory.Closures
universe u v w
noncomputable section
variable {X : Type w} (P : Pregeometry X)

def localization (A : Set X) : Pregeometry X where
  cl S := P.cl (A ∪ S)
  extensive := by
    intro S x hx
    exact P.extensive (A ∪ S) (Or.inr hx)
  monotone := by
    intro S R h
    exact P.monotone (Set.union_subset_union_right A h)
  idempotent := by
    intro S
    apply Set.Subset.antisymm
    · exact (P.monotone (Set.union_subset
        (Set.subset_union_left.trans (P.extensive (A ∪ S))) Set.Subset.rfl)).trans
        (P.idempotent (A ∪ S)).le
    · exact P.monotone (Set.union_subset_union_right A
        (Set.subset_union_right.trans (P.extensive (A ∪ S))))
  finite_character := by
    classical
    intro x S
    constructor
    · intro hx
      obtain ⟨F, hF, hxF⟩ := (P.finite_character x (A ∪ S)).mp hx
      refine ⟨F.filter (· ∈ S), ?_, ?_⟩
      · intro y hy
        exact (Finset.mem_filter.mp hy).2
      · apply P.monotone (B := A ∪ (↑(F.filter (· ∈ S)) : Set X)) ?_ hxF
        intro y hy
        rcases hF hy with hyA | hyS
        · exact Or.inl hyA
        · exact Or.inr (Finset.mem_filter.mpr ⟨hy, hyS⟩)
    · rintro ⟨F, hF, hxF⟩
      exact P.monotone (Set.union_subset_union_right A hF) hxF
  exchange := by
    intro S a b hb
    simpa only [Set.union_assoc] using
      P.exchange (A ∪ S) a b (by simpa only [Set.union_assoc] using hb)

def IndependentOver (A I : Set X) : Prop := (P.localization A).Independent I

def IsRelativeBasis (A B S : Set X) : Prop :=
  B ⊆ S ∧ P.IndependentOver A B ∧ P.cl (A ∪ B) = P.cl (A ∪ S)

def relativeDimension (A S : Set X) : Cardinal.{w} := (P.localization A).dimension S

theorem relative_basis_iff (A B S : Set X) :
    P.IsRelativeBasis A B S ↔ B ⊆ S ∧ (P.localization A).IsBasis B (P.cl (A ∪ S)) := by
  constructor
  · rintro ⟨hBS, hi, hcl⟩
    exact ⟨hBS, hBS.trans (Set.subset_union_right.trans (P.extensive _)), hi, hcl⟩
  · rintro ⟨hBS, _, hi, hcl⟩
    exact ⟨hBS, hi, hcl⟩

theorem exists_relative_basis_extension {A I S : Set X}
    (hi : P.IndependentOver A I) (his : I ⊆ S) :
    ∃ B : Set X, I ⊆ B ∧ P.IsRelativeBasis A B S := by
  obtain ⟨B, hIB, hBS, hiB, hcl⟩ := (P.localization A).exists_basis_extension hi his
  exact ⟨B, hIB, hBS, hiB, hcl⟩

theorem relative_basis_cardinal_eq {A B D S : Set X}
    (hB : P.IsRelativeBasis A B S) (hD : P.IsRelativeBasis A D S) :
    Cardinal.mk B = Cardinal.mk D := by
  exact (P.localization A).basis_cardinal_eq
    ((P.relative_basis_iff A B S).mp hB).2 ((P.relative_basis_iff A D S).mp hD).2

theorem relativeDimension_eq_mk {A B S : Set X} (hB : P.IsRelativeBasis A B S) :
    P.relativeDimension A S = Cardinal.mk B := by
  exact (P.localization A).dimension_eq_mk ((P.relative_basis_iff A B S).mp hB).2

theorem localization_closure_base (A : Set X) : P.localization (P.cl A) = P.localization A := by
  have hcl : (P.localization (P.cl A)).cl = (P.localization A).cl := by
    funext S
    change P.cl (P.cl A ∪ S) = P.cl (A ∪ S)
    apply Set.Subset.antisymm
    · rw [← P.idempotent (A ∪ S)]
      apply P.monotone
      exact Set.union_subset (P.monotone Set.subset_union_left)
        (Set.subset_union_right.trans (P.extensive _))
    · exact P.monotone (Set.union_subset_union_left S (P.extensive A))
  cases h₁ : P.localization (P.cl A) with
  | mk cl₁ _ _ _ _ _ =>
    cases h₂ : P.localization A with
    | mk cl₂ _ _ _ _ _ =>
      simp only [h₁, h₂] at hcl
      cases hcl
      rfl

theorem relativeDimension_eq_zero_iff (A S : Set X) :
    P.relativeDimension A S = 0 ↔ S ⊆ P.cl A := by
  constructor
  · intro hzero
    have hs := (P.localization A).chosenBasis_spec S
    have he : (P.localization A).chosenBasis S = ∅ := by
      apply Set.isEmpty_coe_sort.mp
      exact Cardinal.mk_eq_zero_iff.mp hzero
    have hspan : P.cl (A ∪ S) = P.cl A := by
      have hEq : P.cl (A ∪ (P.localization A).chosenBasis S) = P.cl (A ∪ S) := hs.2.2
      rw [he, Set.union_empty] at hEq
      exact hEq.symm
    exact Set.subset_union_right.trans ((P.extensive _).trans hspan.le)
  · intro hSA
    have hcl : P.cl (A ∪ (∅ : Set X)) = P.cl (A ∪ S) := by
      rw [Set.union_empty]
      apply Set.Subset.antisymm (P.monotone Set.subset_union_left)
      rw [← P.idempotent A]
      exact P.monotone (Set.union_subset (P.extensive A) hSA)
    have hb : P.IsRelativeBasis A ∅ S := ⟨Set.empty_subset _, (P.localization A).independent_empty, hcl⟩
    simpa using P.relativeDimension_eq_mk hb

theorem independentOver_disjoint_closure {A I : Set X} (hi : P.IndependentOver A I) :
    Disjoint I (P.cl A) := by
  apply Set.disjoint_left.mpr
  intro x hxI hxA
  exact hi x hxI (P.monotone Set.subset_union_left hxA)

variable {L : FirstOrder.Language.{u,v}} {M : Type w} [L.Structure M]

theorem algebraic_basis_extension (T : L.Theory) (hT : StronglyMinimalTheory T)
    [Nonempty M] [M ⊨ T] {I S : Set M}
    (hi : (aclPregeometry T hT).Independent I) (his : I ⊆ S) :
    ∃ B : Set M, I ⊆ B ∧ B ⊆ S ∧ (aclPregeometry T hT).Independent B ∧
      acl L B = acl L S := by
  exact (aclPregeometry T hT).exists_basis_extension hi his

theorem algebraic_relative_basis_extension (T : L.Theory) (hT : StronglyMinimalTheory T)
    [Nonempty M] [M ⊨ T] {A I S : Set M}
    (hi : (aclPregeometry T hT).IndependentOver A I) (his : I ⊆ S) :
    ∃ B : Set M, I ⊆ B ∧ B ⊆ S ∧ (aclPregeometry T hT).IndependentOver A B ∧
      acl L (A ∪ B) = acl L (A ∪ S) := by
  obtain ⟨B, hIB, hBS, hiB, hcl⟩ := (aclPregeometry T hT).exists_relative_basis_extension hi his
  exact ⟨B, hIB, hBS, hiB, hcl⟩

end
end Lemmatheca.ModelTheory.StronglyMinimalSets.Pregeometry
