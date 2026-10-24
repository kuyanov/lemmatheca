import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Finset.Card

namespace Lemmatheca.ModelTheory.StronglyMinimalSets
universe w
noncomputable section

structure Pregeometry (X : Type w) where
  cl : Set X → Set X
  extensive : ∀ A, A ⊆ cl A
  monotone : ∀ {A B}, A ⊆ B → cl A ⊆ cl B
  idempotent : ∀ A, cl (cl A) = cl A
  finite_character : ∀ (x : X) A, x ∈ cl A ↔
    ∃ S : Finset X, (S : Set X) ⊆ A ∧ x ∈ cl (S : Set X)
  exchange : ∀ A a b, b ∈ cl (A ∪ {a}) \ cl A → a ∈ cl (A ∪ {b})

namespace Pregeometry
variable {X : Type w} (P : Pregeometry X)

def Closed (C : Set X) : Prop := P.cl C = C

def Independent (I : Set X) : Prop := ∀ a ∈ I, a ∉ P.cl (I \ {a})

def IsBasis (B C : Set X) : Prop := B ⊆ C ∧ P.Independent B ∧ P.cl B = C

def FinitelyGenerated (C : Set X) : Prop := ∃ S : Finset X, P.cl (S : Set X) = C

theorem independent_empty : P.Independent ∅ := by
  intro a ha
  exact ha.elim

theorem independent_subset {I J : Set X} (hI : P.Independent I) (hJI : J ⊆ I) :
    P.Independent J := by
  intro a ha haCl
  exact hI a (hJI ha) (P.monotone (by intro x hx; exact ⟨hJI hx.1,hx.2⟩) haCl)

theorem independent_adjoin {I : Set X} (hI : P.Independent I) {a : X} (ha : a ∉ P.cl I) :
    P.Independent (I ∪ {a}) := by
  classical
  intro x hx hxcl
  by_cases hxa : x = a
  · subst x
    apply ha
    apply P.monotone (B := I) ?_ hxcl
    intro z hz
    rcases hz.1 with hzI | hza
    · exact hzI
    · exact (hz.2 hza).elim
  · have hxI : x ∈ I := hx.resolve_right (by simpa using hxa)
    have hxnot := hI x hxI
    have hsub : (I ∪ {a}) \ {x} ⊆ (I \ {x}) ∪ {a} := by
      intro z hz
      rcases hz.1 with hzI | hza
      · exact Or.inl ⟨hzI,hz.2⟩
      · exact Or.inr hza
    have hex := P.exchange (I \ {x}) a x ⟨P.monotone hsub hxcl,hxnot⟩
    apply ha
    apply P.monotone (B := I) ?_ hex
    intro z hz
    rcases hz with hz | hz
    · exact hz.1
    · have hzx : z = x := hz
      exact hzx.symm ▸ hxI

theorem closure_insert_of_mem {I : Set X} {a : X} (ha : a ∈ P.cl I) :
    P.cl (I ∪ {a}) = P.cl I := by
  apply Set.Subset.antisymm
  · rw [← P.idempotent I]
    apply P.monotone
    intro x hx
    rcases hx with hx | hx
    · exact P.extensive I hx
    · have hxa : x = a := hx
      exact hxa.symm ▸ ha
  · exact P.monotone Set.subset_union_left

end Pregeometry
end
end Lemmatheca.ModelTheory.StronglyMinimalSets
